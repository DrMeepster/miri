//! (limited) support for Windows errors
//!
//! We need to produce 3 kinds of errors:
//! * [Win32 error codes][MS-ERRREF 2.2] are 16 bit values usually returned from `GetLastError`.
//! Zero is a success and any other value is an error. Most windows functions we implement use these.
//!
//! * [`HRESULT`][MS-ERRREF 2.1]s are 32 bit packed structures usually returned by a function directly.
//! Zero (and any other value with the highest bit unset) is a success. Only a few of the functions we implement use these.
//! Because of this, we only ever make them by encoding Win32 errors into this format with [`win32_error_to_hresult`].
//!
//! * [`NTRESULT`][MS-ERRREF 2.3]s are 32 bit packed structures similar to `HRESULT`s but for NT functions.
//! We encode Win32 errors as these with [`win32_error_to_ntstatus`] and also decode them with [`ntstatus_to_win32_error`].
//!
//! [MS-ERRREF 2.1]: https://learn.microsoft.com/en-us/openspecs/windows_protocols/ms-erref/0642cb2f-2075-4469-918c-4441e69c548a
//! [MS-ERRREF 2.2]: https://learn.microsoft.com/en-us/openspecs/windows_protocols/ms-erref/18d8fbe8-a967-4f1c-ae50-99ca8e491d2d
//! [MS-ERRREF 2.3]: https://learn.microsoft.com/en-us/openspecs/windows_protocols/ms-erref/87fba13e-bf06-450e-83b1-9241dc81e781

use std::io;

use crate::*;

// This mapping should match the first part of `decode_error_kind` in
// <https://github.com/rust-lang/rust/blob/master/library/std/src/sys/windows/mod.rs>.
pub const IO_ERROR_TABLE: &[(&str, std::io::ErrorKind)] = {
    use std::io::ErrorKind::*;
    // many of these errors map to the same errorkind
    // both will be used in the forwards mapping
    // only the first will be used in the backwards mapping
    &[
        ("ERROR_ACCESS_DENIED", PermissionDenied),
        ("ERROR_FILE_EXISTS", AlreadyExists),
        ("ERROR_ALREADY_EXISTS", AlreadyExists),
        ("ERROR_BROKEN_PIPE", BrokenPipe),
        ("ERROR_NO_DATA", BrokenPipe),
        ("ERROR_FILE_NOT_FOUND", NotFound),
        ("ERROR_PATH_NOT_FOUND", NotFound),
        ("ERROR_INVALID_DRIVE", NotFound),
        ("ERROR_BAD_NETPATH", NotFound),
        ("ERROR_BAD_NET_NAME", NotFound),
        ("ERROR_INVALID_NAME", InvalidFilename),
        ("ERROR_BAD_PATHNAME", InvalidFilename),
        ("ERROR_INVALID_PARAMETER", InvalidInput),
        ("ERROR_NOT_ENOUGH_MEMORY", OutOfMemory),
        ("ERROR_OUTOFMEMORY", OutOfMemory),
        ("ERROR_TIMEOUT", TimedOut),
        ("ERROR_SEM_TIMEOUT", TimedOut),
        ("WAIT_TIMEOUT", TimedOut),
        ("ERROR_DRIVER_CANCEL_TIMEOUT", TimedOut),
        ("ERROR_OPERATION_ABORTED", TimedOut),
        ("ERROR_SERVICE_REQUEST_TIMEOUT", TimedOut),
        ("ERROR_COUNTER_TIMEOUT", TimedOut),
        ("ERROR_RESOURCE_CALL_TIMED_OUT", TimedOut),
        ("ERROR_CTX_MODEM_RESPONSE_TIMEOUT", TimedOut),
        ("ERROR_CTX_CLIENT_QUERY_TIMEOUT", TimedOut),
        ("FRS_ERR_SYSVOL_POPULATE_TIMEOUT", TimedOut),
        ("ERROR_DS_TIMELIMIT_EXCEEDED", TimedOut),
        ("DNS_ERROR_RECORD_TIMED_OUT", TimedOut),
        ("ERROR_IPSEC_IKE_TIMED_OUT", TimedOut),
        ("ERROR_RUNLEVEL_SWITCH_TIMEOUT", TimedOut),
        ("ERROR_RUNLEVEL_SWITCH_AGENT_TIMEOUT", TimedOut),
        ("ERROR_CALL_NOT_IMPLEMENTED", Unsupported),
        ("ERROR_HOST_UNREACHABLE", HostUnreachable),
        ("ERROR_NETWORK_UNREACHABLE", NetworkUnreachable),
        ("ERROR_DIRECTORY", NotADirectory),
        ("ERROR_DIRECTORY_NOT_SUPPORTED", IsADirectory),
        ("ERROR_DIR_NOT_EMPTY", DirectoryNotEmpty),
        ("ERROR_WRITE_PROTECT", ReadOnlyFilesystem),
        ("ERROR_DISK_FULL", StorageFull),
        ("ERROR_HANDLE_DISK_FULL", StorageFull),
        ("ERROR_SEEK_ON_DEVICE", NotSeekable),
        ("ERROR_DISK_QUOTA_EXCEEDED", FilesystemQuotaExceeded),
        ("ERROR_FILE_TOO_LARGE", FileTooLarge),
        ("ERROR_BUSY", ResourceBusy),
        ("ERROR_POSSIBLE_DEADLOCK", Deadlock),
        ("ERROR_NOT_SAME_DEVICE", CrossesDevices),
        ("ERROR_TOO_MANY_LINKS", TooManyLinks),
        ("ERROR_FILENAME_EXCED_RANGE", InvalidFilename),
    ]
};

const CODE_MASK: u32 = 0xFFFF;

const NTSTATUS_FACILITY_MASK: u32 = 0x3FFF_0000;
const STATUS_SEVERITY_ERROR: u32 = 0b11;
const FACILITY_NTWIN32: u32 = 0x007;

/// An NTSTATUS with severity of STATUS_SEVERITY_ERROR and facility of FACILITY_NTWIN32
///
/// See https://learn.microsoft.com/en-us/openspecs/windows_protocols/ms-erref/87fba13e-bf06-450e-83b1-9241dc81e781
const NTSTATUS_WIN32: u32 = STATUS_SEVERITY_ERROR << 30 | FACILITY_NTWIN32 << 16;

pub fn win32_error_to_ntstatus(error: u32) -> u32 {
    // win32 error codes are always less than 0xFFFF
    assert!(error <= CODE_MASK);

    error | NTSTATUS_WIN32
}

pub fn ntstatus_to_win32_error(ntstatus: u32) -> Option<u32> {
    if (ntstatus & NTSTATUS_FACILITY_MASK) >> 16 == FACILITY_NTWIN32 {
        Some(ntstatus & CODE_MASK)
    } else {
        None
    }
}

const FACILITY_WIN32: u32 = 0x007;

/// An HRESULT with the severity bit set and facility of FACILITY_WIN32
///
/// See https://learn.microsoft.com/en-us/openspecs/windows_protocols/ms-erref/0642cb2f-2075-4469-918c-4441e69c548a
const HRESULT_WIN32: u32 = 1 << 31 | FACILITY_WIN32 << 16;

pub fn win32_error_to_hresult(error: u32) -> u32 {
    // win32 error codes are always less than 0xFF
    assert!(error <= CODE_MASK);

    error | HRESULT_WIN32
}

impl<'mir, 'tcx: 'mir> EvalContextExt<'mir, 'tcx> for crate::MiriInterpCx<'mir, 'tcx> {}
#[allow(non_snake_case)]
pub trait EvalContextExt<'mir, 'tcx: 'mir>: crate::MiriInterpCxExt<'mir, 'tcx> {
    fn RtlNtStatusToDosError(
        &mut self,
        status_op: &OpTy<'tcx, Provenance>,
    ) -> InterpResult<'tcx, Scalar<Provenance>> {
        let this = self.eval_context_mut();

        let status = this.read_scalar(status_op)?.to_u32()?;

        if let Some(error) = ntstatus_to_win32_error(status) {
            Ok(Scalar::from_u32(error))
        } else {
            throw_unsup_format!("Unsupported NTSTATUS {status:#x}")
        }
    }

    fn eval_win32_error_as_ntstatus(&mut self, error_name: &str) -> Scalar<Provenance> {
        let this = self.eval_context_mut();

        let error = this.eval_windows_u32("c", error_name);
        let ntstatus = win32_error_to_ntstatus(error);
        Scalar::from_u32(ntstatus)
    }

    fn io_error_to_ntstatus(
        &mut self,
        err_kind: io::ErrorKind,
    ) -> InterpResult<'tcx, Scalar<Provenance>> {
        let this = self.eval_context_mut();

        let error = this.io_error_to_errnum(err_kind)?.to_u32()?;
        let ntstatus = win32_error_to_ntstatus(error);
        Ok(Scalar::from_u32(ntstatus))
    }
}
