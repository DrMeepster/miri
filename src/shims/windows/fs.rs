use std::fs::{remove_file, File, Metadata};
use std::io;

use rustc_middle::ty::TyCtxt;
use rustc_target::abi::Size;

use crate::helpers::split_u64;
use crate::shims::fs::{FileDescriptor, FileHandle};
use crate::shims::windows::error::EvalContextExt as _;
use crate::shims::windows::handle::{EvalContextExt as _, Handle};
use crate::*;

/// Special "file handle" for how std gets metadata
#[derive(Debug)]
struct MetadataHandle {
    data: Metadata,
}

impl FileDescriptor for MetadataHandle {
    fn name(&self) -> &'static str {
        "FILE METADATA"
    }

    fn read<'tcx>(
        &mut self,
        _communicate_allowed: bool,
        _bytes: &mut [u8],
        _tcx: TyCtxt<'tcx>,
    ) -> InterpResult<'tcx, io::Result<usize>> {
        Ok(Err(io::ErrorKind::PermissionDenied.into()))
    }

    fn write<'tcx>(
        &self,
        _communicate_allowed: bool,
        _bytes: &[u8],
        _tcx: TyCtxt<'tcx>,
    ) -> InterpResult<'tcx, io::Result<usize>> {
        Ok(Err(io::ErrorKind::PermissionDenied.into()))
    }

    fn seek<'tcx>(
        &mut self,
        _communicate_allowed: bool,
        _offset: io::SeekFrom,
    ) -> InterpResult<'tcx, io::Result<u64>> {
        Ok(Err(io::ErrorKind::PermissionDenied.into()))
    }

    fn close<'tcx>(
        self: Box<Self>,
        _communicate_allowed: bool,
    ) -> InterpResult<'tcx, io::Result<()>> {
        // nothing to close
        Ok(Ok(()))
    }

    fn metadata<'tcx>(
        &mut self,
        communicate_allowed: bool,
    ) -> InterpResult<'tcx, io::Result<std::fs::Metadata>> {
        assert!(communicate_allowed, "isolation should have prevented even opening a file");
        Ok(Ok(self.data.clone()))
    }

    fn dup(&mut self) -> io::Result<Box<dyn FileDescriptor>> {
        Ok(Box::new(MetadataHandle { data: self.data.clone() }))
    }

    // technically, this should fail
    fn is_tty(&self, _communicate_allowed: bool) -> bool {
        false
    }
}

impl<'mir, 'tcx> EvalContextExt<'mir, 'tcx> for MiriInterpCx<'mir, 'tcx> {}
#[allow(non_snake_case)]
pub trait EvalContextExt<'mir, 'tcx: 'mir>: MiriInterpCxExt<'mir, 'tcx> {
    // FIXME really unsure about the error messages here
    fn CreateFileW(
        &mut self,
        filename_op: &OpTy<'tcx, Provenance>, // LPCWSTR
        access_op: &OpTy<'tcx, Provenance>,   // DWORD
        share_op: &OpTy<'tcx, Provenance>,    // DWORD
        security_op: &OpTy<'tcx, Provenance>, // LPSECURITY_ATTRIBUTES
        create_op: &OpTy<'tcx, Provenance>,   // DWORD
        flags_op: &OpTy<'tcx, Provenance>,    // DWORD
        template_op: &OpTy<'tcx, Provenance>, // HANDLE
    ) -> InterpResult<'tcx, Scalar<Provenance>> /* HANDLE */ {
        let this = self.eval_context_mut();

        let path = this.read_path_from_wide_str(this.read_pointer(filename_op)?)?;
        let access = this.read_scalar(access_op)?.to_u32()?;
        let share = this.read_scalar(share_op)?.to_u32()?;

        if !this.ptr_is_null(this.read_pointer(security_op)?)? {
            throw_unsup_format!("non-null `lpSecurityAttributes` in `CreateFileW`")
        }

        let create = this.read_scalar(create_op)?.to_u32()?;
        let flags = this.read_scalar(flags_op)?.to_u32()?;

        if this.read_handle(template_op)? != Some(Handle::Null) {
            throw_unsup_format!("non-null `hTemplateFile` in `CreateFileW`")
        }

        // Reject if isolation is enabled.
        if let IsolatedOp::Reject(reject_with) = this.machine.isolated_op {
            this.reject_in_isolation("`CreateFileW`", reject_with)?;
            this.set_last_error_from_io_error(io::ErrorKind::PermissionDenied)?;
            return Ok(this.eval_windows("c", "INVALID_HANDLE_VALUE"));
        }

        let mut meta_only = true;
        let mut writable = false;
        let mut options = File::options();

        // access flags
        // see https://learn.microsoft.com/en-us/windows/win32/secauthz/generic-access-rights
        //     https://learn.microsoft.com/en-us/windows/win32/fileio/file-security-and-access-rights

        let generic_all = this.eval_windows_u32("c", "GENERIC_ALL");
        let generic_read = generic_all | this.eval_windows_u32("c", "GENERIC_READ");
        let generic_write = generic_all | this.eval_windows_u32("c", "GENERIC_WRITE");

        if access & (generic_read | this.eval_windows_u32("c", "FILE_READ_DATA")) != 0 {
            options.read(true);
            meta_only = false;
        }

        if access & (generic_write | this.eval_windows_u32("c", "FILE_APPEND_DATA")) != 0 {
            options.append(true);
            meta_only = false;
            writable = true;
        }

        if access & (generic_write | this.eval_windows_u32("c", "FILE_WRITE_DATA")) != 0 {
            // only append when there is FILE_APPEND_DATA without FILE_WRITE_DATA
            options.write(true).append(false);
            meta_only = false;
            writable = true;
        }

        // we don't need to forbid asking for permissions we don't support using

        let supported_file_share_mode = this.eval_windows_u32("c", "FILE_SHARE_READ")
            | this.eval_windows_u32("c", "FILE_SHARE_WRITE")
            | this.eval_windows_u32("c", "FILE_SHARE_DELETE");

        if share != supported_file_share_mode {
            throw_unsup_format!(
                "`dwShareMode` 0x{share:X} != 0x{supported_file_share_mode:X} in `CreateFileW`"
            )
        }

        let create_new = this.eval_windows_u32("c", "CREATE_NEW");
        let create_always = this.eval_windows_u32("c", "CREATE_ALWAYS");
        let open_existing = this.eval_windows_u32("c", "OPEN_EXISTING");
        let open_always = this.eval_windows_u32("c", "OPEN_ALWAYS");
        let truncate_existing = this.eval_windows_u32("c", "TRUNCATE_EXISTING");

        if meta_only {
            if create != open_existing {
                throw_unsup_format!(
                    "`dwCreationDisposition` is not `OPEN_EXISTING` for zero access file handle"
                )
            }

            let backup_semantics = this.eval_windows_u32("c", "FILE_FLAG_BACKUP_SEMANTICS");
            let open_reparse_point = this.eval_windows_u32("c", "FILE_FLAG_OPEN_REPARSE_POINT");

            let unsupported_flags = !(backup_semantics | open_reparse_point);

            if flags & backup_semantics == 0 {
                throw_unsup_format!(
                    "`dwFlagsAndAttributes` does not have `FILE_FLAG_BACKUP_SEMANTICS` for zero access file handle"
                )
            }

            let follow_symlinks = flags & open_reparse_point == 0;

            if flags & unsupported_flags != 0 {
                throw_unsup_format!(
                    "unsupported `dwFlagsAndAttributes` {:#x} for zero access file handle",
                    flags & unsupported_flags
                )
            }

            let result = if follow_symlinks { path.metadata() } else { path.symlink_metadata() };

            match this.try_unwrap_io_result(result)? {
                Some(data) => {
                    let id = this.machine.file_handler.insert_fd(Box::new(MetadataHandle { data }));

                    Ok(Handle::File(id).to_scalar(this))
                }
                None => Ok(Handle::Null.to_scalar(this)),
            }
        } else {
            // CREATE_ALWAYS and OPEN_ALWAYS set the last error when the file already exists
            let mut check_file_preexistance = false;

            if create == create_new {
                options.create_new(true);
            } else if create == create_always {
                options.truncate(true);
                check_file_preexistance = true;
            } else if create == open_existing {
                /* use default values */
            } else if create == open_always {
                check_file_preexistance = true;
            } else if create == truncate_existing {
                options.truncate(true);
            } else {
                this.set_last_error(this.eval_windows("c", "ERROR_INVALID_PARAMETER"))?;
                return Ok(this.eval_windows("c", "INVALID_HANDLE_VALUE"));
            }

            if create == create_new {
                let open_reparse_point = this.eval_windows_u32("c", "FILE_FLAG_OPEN_REPARSE_POINT");
                if flags != open_reparse_point {
                    throw_unsup_format!(
                        "`dwFlagsAndAttributes` is not `FILE_FLAG_OPEN_REPARSE_POINT` when `dwCreationDisposition` is `CREATE_NEW`"
                    )
                }
            } else {
                if flags != 0 {
                    throw_unsup_format!(
                        "`dwFlagsAndAttributes` is not 0 when `dwCreationDisposition` is not `CREATE_NEW`"
                    )
                }
            }

            let already_exists = if check_file_preexistance {
                let Some(already_exists) = this.try_unwrap_io_result(path.try_exists())? else {
                    return Ok(this.eval_windows("c", "INVALID_HANDLE_VALUE"));
                };

                // make sure it fails if the file is created/deleted before its opened
                options.create_new(!already_exists);

                if already_exists {
                    this.set_last_error(this.eval_windows("c", "ERROR_ALREADY_EXISTS"))?;
                }

                Some(already_exists)
            } else {
                None
            };

            match (options.open(path), already_exists) {
                (Ok(file), _) => {
                    let id = this
                        .machine
                        .file_handler
                        .insert_fd(Box::new(FileHandle { file, writable }));

                    Ok(Handle::File(id).to_scalar(this))
                }
                // abort if the file is created/deleted between the check and now
                // these errors are not expected by the caller
                (Err(err), Some(false)) if err.kind() == io::ErrorKind::AlreadyExists => {
                    throw_machine_stop!(TerminationInfo::Abort(
                        "file created while creating file in `CreateFileW`".to_string()
                    ))
                }
                (Err(err), Some(true)) if err.kind() == io::ErrorKind::NotFound => {
                    throw_machine_stop!(TerminationInfo::Abort(
                        "file deleted while opening file in `CreateFileW`".to_string()
                    ))
                }
                (Err(err), _) => {
                    this.set_last_error_from_io_error(err.kind())?;
                    Ok(Handle::Null.to_scalar(this))
                }
            }
        }
    }

    fn GetStdHandle(
        &mut self,
        which_op: &OpTy<'tcx, Provenance>,
    ) -> InterpResult<'tcx, Scalar<Provenance>> {
        let this = self.eval_context_mut();

        let which = this.read_scalar(which_op)?.to_u32()?;

        let handle = if which == this.eval_windows_u32("c", "STD_INPUT_HANDLE") {
            Handle::File(0).to_scalar(this)
        } else if which == this.eval_windows_u32("c", "STD_OUTPUT_HANDLE") {
            Handle::File(1).to_scalar(this)
        } else if which == this.eval_windows_u32("c", "STD_ERROR_HANDLE") {
            Handle::File(2).to_scalar(this)
        } else {
            this.set_last_error_from_io_error(io::ErrorKind::InvalidInput)?;
            this.eval_windows("c", "INVALID_HANDLE_VALUE")
        };

        Ok(handle)
    }

    fn GetFileInformationByHandle(
        &mut self,
        handle_op: &OpTy<'tcx, Provenance>, // HANDLE
        dest_op: &OpTy<'tcx, Provenance>,   // LPBY_HANDLE_FILE_INFORMATION
    ) -> InterpResult<'tcx, Scalar<Provenance>> /* BOOL */ {
        let this = self.eval_context_mut();

        let handle = this.read_handle(handle_op)?;
        let dest =
            this.deref_pointer_as(dest_op, this.windows_ty_layout("BY_HANDLE_FILE_INFORMATION"))?;

        // Isolation check is done via `FileDescriptor` trait.
        let communicate = this.machine.communicate();

        let Some(Handle::File(fd)) = handle else {
            return this.invalid_handle("FALSE");
        };

        let Some(file) = this.machine.file_handler.handles.get_mut(&fd) else {
            return this.invalid_handle("FALSE");
        };

        let result = file.metadata(communicate)?;

        let Some(meta) = this.try_unwrap_io_result(result)? else {
            return this.invalid_handle("FALSE");
        };

        let mut attributes = 0;

        if meta.is_dir() {
            attributes |= this.eval_windows_u32("c", "FILE_ATTRIBUTE_DIRECTORY");
        }

        if meta.is_symlink() {
            attributes |= this.eval_windows_u32("c", "FILE_ATTRIBUTE_REPARSE_POINT");
        }

        if meta.permissions().readonly() {
            attributes |= this.eval_windows_u32("c", "FILE_ATTRIBUTE_READONLY");
        }

        let created = match meta.created() {
            Ok(t) => this.system_time_to_windows_filetime(&t)?,
            Err(_) => 0,
        };

        let (created_low, created_high) = split_u64(created);

        let accessed = match meta.accessed() {
            Ok(t) => this.system_time_to_windows_filetime(&t)?,
            Err(_) => 0,
        };

        let (accessed_low, accessed_high) = split_u64(accessed);

        let (size_low, size_high) = split_u64(meta.len());

        // zeros are unavailable
        this.write_int_fields_named(
            &[
                ("dwFileAttributes", attributes.into()),
                ("dwVolumeSerialNumber", 0),
                ("nFileSizeHigh", size_high.into()),
                ("nFileSizeLow", size_low.into()),
                ("nNumberOfLinks", 0),
                ("nFileIndexHigh", 0),
                ("nFileIndexLow", 0),
            ],
            &dest,
        )?;
        this.write_int_fields(
            &[created_low.into(), created_high.into()],
            &this.project_field_named(&dest, "ftCreationTime")?,
        )?;
        this.write_int_fields(
            &[accessed_low.into(), accessed_high.into()],
            &this.project_field_named(&dest, "ftLastAccessTime")?,
        )?;
        this.write_int_fields(&[0, 0], &this.project_field_named(&dest, "ftLastWriteTime")?)?;

        Ok(this.eval_windows("c", "TRUE"))
    }

    fn DeleteFileW(
        &mut self,
        filename_op: &OpTy<'tcx, Provenance>, // LPCWSTR
    ) -> InterpResult<'tcx, Scalar<Provenance>> /* BOOL */ {
        let this = self.eval_context_mut();

        let path = this.read_path_from_wide_str(this.read_pointer(filename_op)?)?;

        // Reject if isolation is enabled.
        if let IsolatedOp::Reject(reject_with) = this.machine.isolated_op {
            this.reject_in_isolation("`DeleteFileW`", reject_with)?;
            this.set_last_error_from_io_error(io::ErrorKind::PermissionDenied)?;
            return Ok(this.eval_windows("c", "FALSE"));
        }

        match this.try_unwrap_io_result(remove_file(path))? {
            Some(()) => Ok(this.eval_windows("c", "TRUE")),
            None => Ok(this.eval_windows("c", "FALSE")),
        }
    }

    fn NtWriteFile(
        &mut self,
        handle_op: &OpTy<'tcx, Provenance>,          // HANDLE
        event_op: &OpTy<'tcx, Provenance>,           // HANDLE
        apc_routine_op: &OpTy<'tcx, Provenance>,     // PIO_APC_ROUTINE
        apc_context_op: &OpTy<'tcx, Provenance>,     // PVOID
        io_status_block_op: &OpTy<'tcx, Provenance>, // PIO_STATUS_BLOCK
        buf_op: &OpTy<'tcx, Provenance>,             // PVOID
        n_op: &OpTy<'tcx, Provenance>,               // ULONG
        byte_offset_op: &OpTy<'tcx, Provenance>,     // PLARGE_INTEGER
        key_op: &OpTy<'tcx, Provenance>,             // PULONG
    ) -> InterpResult<'tcx, Scalar<Provenance>> /* NTRESULT */ {
        let this = self.eval_context_mut();

        let handle = this.read_handle(handle_op)?;

        if !this.ptr_is_null(this.read_pointer(event_op)?)? {
            throw_unsup_format!("non-null `Event` in `NtWriteFile`")
        }

        if !this.ptr_is_null(this.read_pointer(apc_routine_op)?)? {
            throw_unsup_format!("non-null `ApcRoutine` in `NtWriteFile`")
        }

        if !this.ptr_is_null(this.read_pointer(apc_context_op)?)? {
            throw_unsup_format!("non-null `ApcContext` in `NtWriteFile`")
        }

        let io_status_block =
            this.deref_pointer_as(io_status_block_op, this.windows_ty_layout("IO_STATUS_BLOCK"))?;
        let buf = this.read_pointer(buf_op)?;
        let n = this.read_scalar(n_op)?.to_u32()?;

        if !this.ptr_is_null(this.read_pointer(byte_offset_op)?)? {
            throw_unsup_format!("non-null `ByteOffset` in `NtWriteFile`")
        }

        if !this.ptr_is_null(this.read_pointer(key_op)?)? {
            throw_unsup_format!("non-null `Key` in `NtWriteFile`")
        }

        // Isolation check is done via `FileDescriptor` trait.
        let communicate = this.machine.communicate();

        let io_status_status = this.project_field_named(
            &this.project_field_named(&io_status_block, "Anonymous")?,
            "Status",
        )?;

        let error_invalid_handle = this.eval_win32_error_as_ntstatus("ERROR_INVALID_HANDLE");

        let Some(Handle::File(fd)) = handle else {
            this.write_scalar(error_invalid_handle, &io_status_status)?;
            return Ok(error_invalid_handle);
        };

        let Some(file) = this.machine.file_handler.handles.get(&fd) else {
            this.write_scalar(error_invalid_handle, &io_status_status)?;
            return Ok(error_invalid_handle);
        };

        let bytes = this.read_bytes_ptr_strip_provenance(buf, Size::from_bytes(n))?;

        let (status, written) = match file.write(communicate, bytes, *this.tcx)? {
            Ok(written) =>
                (this.eval_windows("c", "STATUS_SUCCESS"), u64::try_from(written).unwrap()),
            Err(error) => (this.io_error_to_ntstatus(error.kind())?, 0),
        };

        let io_status_information = this.project_field_named(&io_status_block, "Information")?;
        this.write_scalar(Scalar::from_target_usize(written, this), &io_status_information)?;
        this.write_scalar(status, &io_status_status)?;

        Ok(status)
    }

    fn NtReadFile(
        &mut self,
        handle_op: &OpTy<'tcx, Provenance>,          // HANDLE
        event_op: &OpTy<'tcx, Provenance>,           // HANDLE
        apc_routine_op: &OpTy<'tcx, Provenance>,     // PIO_APC_ROUTINE
        apc_context_op: &OpTy<'tcx, Provenance>,     // PVOID
        io_status_block_op: &OpTy<'tcx, Provenance>, // PIO_STATUS_BLOCK
        buf_op: &OpTy<'tcx, Provenance>,             // PVOID
        n_op: &OpTy<'tcx, Provenance>,               // ULONG
        byte_offset_op: &OpTy<'tcx, Provenance>,     // PLARGE_INTEGER
        key_op: &OpTy<'tcx, Provenance>,             // PULONG
    ) -> InterpResult<'tcx, Scalar<Provenance>> /* NTRESULT */ {
        let this = self.eval_context_mut();

        let handle = this.read_handle(handle_op)?;

        if !this.ptr_is_null(this.read_pointer(event_op)?)? {
            throw_unsup_format!("non-null `Event` in `NtReadFile`")
        }

        if !this.ptr_is_null(this.read_pointer(apc_routine_op)?)? {
            throw_unsup_format!("non-null `ApcRoutine` in `NtReadFile`")
        }

        if !this.ptr_is_null(this.read_pointer(apc_context_op)?)? {
            throw_unsup_format!("non-null `ApcContext` in `NtReadFile`")
        }

        let io_status_block =
            this.deref_pointer_as(io_status_block_op, this.windows_ty_layout("IO_STATUS_BLOCK"))?;
        let buf = this.read_pointer(buf_op)?;
        let n = this.read_scalar(n_op)?.to_u32()?;

        if !this.ptr_is_null(this.read_pointer(byte_offset_op)?)? {
            throw_unsup_format!("non-null `ByteOffset` in `NtReadFile`")
        }

        if !this.ptr_is_null(this.read_pointer(key_op)?)? {
            throw_unsup_format!("non-null `Key` in `NtReadFile`")
        }

        // Isolation check is done via `FileDescriptor` trait.
        let communicate = this.machine.communicate();

        let io_status_status = this.project_field_named(
            &this.project_field_named(&io_status_block, "Anonymous")?,
            "Status",
        )?;

        // Check that the *entire* buffer is actually valid memory.
        this.check_ptr_access(buf, Size::from_bytes(n), CheckInAllocMsg::MemoryAccessTest)?;

        let error_invalid_handle = this.eval_win32_error_as_ntstatus("ERROR_INVALID_HANDLE");

        let Some(Handle::File(fd)) = handle else {
            this.write_scalar(error_invalid_handle, &io_status_status)?;
            return Ok(error_invalid_handle);
        };

        let Some(file) = this.machine.file_handler.handles.get_mut(&fd) else {
            this.write_scalar(error_invalid_handle, &io_status_status)?;
            return Ok(error_invalid_handle);
        };

        let mut bytes = vec![0; usize::try_from(n).unwrap()];

        let (status, read) = match file.read(communicate, &mut bytes, *this.tcx)? {
            Ok(0) if n > 0 => (this.eval_windows("c", "STATUS_END_OF_FILE"), 0),
            Ok(read) => (this.eval_windows("c", "STATUS_SUCCESS"), u64::try_from(read).unwrap()),
            Err(error) => (this.io_error_to_ntstatus(error.kind())?, 0),
        };

        let io_status_information = this.project_field_named(&io_status_block, "Information")?;
        this.write_scalar(Scalar::from_target_usize(read, this), &io_status_information)?;
        this.write_scalar(status, &io_status_status)?;

        Ok(status)
    }
}
