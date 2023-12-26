use rustc_target::abi::HasDataLayout;
use std::mem::variant_count;

use crate::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PseudoHandle {
    CurrentThread,
    CurrentProcess,
}

/// Miri representation of a Windows `HANDLE`
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Handle {
    Null,
    Pseudo(PseudoHandle),
    Thread(ThreadId),
    File(i32),
}

impl PseudoHandle {
    fn value(self) -> u32 {
        self as u32
    }

    fn from_value(value: u32) -> Option<Self> {
        const CURRENT_THREAD_VALUE: u32 = PseudoHandle::CurrentThread as u32;
        const CURRENT_PROCESS_VALUE: u32 = PseudoHandle::CurrentProcess as u32;

        match value {
            CURRENT_THREAD_VALUE => Some(Self::CurrentThread),
            CURRENT_PROCESS_VALUE => Some(Self::CurrentProcess),
            _ => None,
        }
    }
}

impl Handle {
    const NULL_DISCRIMINANT: u32 = 0;
    const PSEUDO_DISCRIMINANT: u32 = 1;
    const THREAD_DISCRIMINANT: u32 = 2;
    const FILE_DISCRIMINANT: u32 = 3;

    fn discriminant(self) -> u32 {
        match self {
            Self::Null => Self::NULL_DISCRIMINANT,
            Self::Pseudo(_) => Self::PSEUDO_DISCRIMINANT,
            Self::Thread(_) => Self::THREAD_DISCRIMINANT,
            Self::File(_) => Self::FILE_DISCRIMINANT,
        }
    }

    fn data(self) -> u32 {
        match self {
            Self::Null => 0,
            Self::Pseudo(pseudo_handle) => pseudo_handle.value(),
            Self::Thread(thread) => thread.to_u32(),
            #[allow(clippy::cast_sign_loss)] // we want to lose the sign
            Self::File(file) => file as u32,
        }
    }

    fn packed_disc_size() -> u32 {
        // we add one to the variant count to ensure the all ones discriminant is never valid
        // ensuring that INVALID_HANDLE_VALUE (0xFFFFFFFF) is never a valid handle
        // see https://devblogs.microsoft.com/oldnewthing/20230914-00/?p=108766
        #[allow(clippy::arithmetic_side_effects)] // cannot overflow
        let variant_count = variant_count::<Self>() + 1;

        // ceil(log2(x)) is how many bits it takes to store x numbers
        // however, std's ilog2 is floor(log2(x))
        let floor_log2 = variant_count.ilog2();

        // we need to add one for non powers of two to compensate for the difference
        #[allow(clippy::arithmetic_side_effects)] // cannot overflow
        if variant_count.is_power_of_two() { floor_log2 } else { floor_log2 + 1 }
    }

    /// Converts a handle into its machine representation.
    ///
    /// The upper [`Self::packed_disc_size()`] bits are used to store a discriminant corresponding to the handle variant.
    /// The remaining bits are used for the variant's field.
    ///
    /// None of this layout is guaranteed to applications by Windows or Miri.
    fn to_packed(self) -> u32 {
        let disc_size = Self::packed_disc_size();
        let data_size = u32::BITS.checked_sub(disc_size).unwrap();

        let discriminant = self.discriminant();
        let data = self.data();

        // make sure the discriminant fits into `disc_size` bits
        assert!(discriminant < 2u32.pow(disc_size));

        // make sure the data fits into `data_size` bits
        assert!(data < 2u32.pow(data_size));

        // packs the data into the lower `data_size` bits
        // and packs the discriminant right above the data
        #[allow(clippy::arithmetic_side_effects)] // cannot overflow
        return discriminant << data_size | data;
    }

    fn new(discriminant: u32, data: u32) -> Option<Self> {
        match discriminant {
            Self::NULL_DISCRIMINANT if data == 0 => Some(Self::Null),
            Self::PSEUDO_DISCRIMINANT => Some(Self::Pseudo(PseudoHandle::from_value(data)?)),
            Self::THREAD_DISCRIMINANT => Some(Self::Thread(data.into())),
            #[allow(clippy::cast_possible_wrap)]
            Self::FILE_DISCRIMINANT => Some(Self::File(data as i32)),
            _ => None,
        }
    }

    /// see docs for `to_packed`
    fn from_packed(handle: u32) -> Option<Self> {
        let disc_size = Self::packed_disc_size();
        let data_size = u32::BITS.checked_sub(disc_size).unwrap();

        // the lower `data_size` bits of this mask are 1
        #[allow(clippy::arithmetic_side_effects)] // cannot overflow
        let data_mask = 2u32.pow(data_size) - 1;

        // the discriminant is stored right above the lower `data_size` bits
        #[allow(clippy::arithmetic_side_effects)] // cannot overflow
        let discriminant = handle >> data_size;

        // the data is stored in the lower `data_size` bits
        let data = handle & data_mask;

        Self::new(discriminant, data)
    }

    pub fn to_scalar(self, cx: &impl HasDataLayout) -> Scalar<Provenance> {
        // 64-bit handles are sign extended 32-bit handles
        // see https://docs.microsoft.com/en-us/windows/win32/winprog64/interprocess-communication
        #[allow(clippy::cast_possible_wrap)] // we want it to wrap
        let signed_handle = self.to_packed() as i32;
        Scalar::from_target_isize(signed_handle.into(), cx)
    }

    pub fn from_scalar<'tcx>(
        handle: Scalar<Provenance>,
        cx: &impl HasDataLayout,
    ) -> InterpResult<'tcx, Option<Self>> {
        let sign_extended_handle = handle.to_target_isize(cx)?;

        #[allow(clippy::cast_sign_loss)] // we want to lose the sign
        let handle = if let Ok(signed_handle) = i32::try_from(sign_extended_handle) {
            signed_handle as u32
        } else {
            // if a handle doesn't fit in an i32, it isn't valid.
            return Ok(None);
        };

        Ok(Self::from_packed(handle))
    }

    // FIXME should this be the display trait?
    fn describe_kind(&self) -> &'static str {
        match self {
            Self::Null => "null handle",
            Self::Pseudo(PseudoHandle::CurrentThread) => "current thread pseudohandle",
            Self::Pseudo(PseudoHandle::CurrentProcess) => "current process pseudohandle",
            Self::Thread(_) => "thread handle",
            Self::File(_) => "file handle",
        }
    }
}

impl<'mir, 'tcx> EvalContextExt<'mir, 'tcx> for crate::MiriInterpCx<'mir, 'tcx> {}

#[allow(non_snake_case)]
pub trait EvalContextExt<'mir, 'tcx: 'mir>: crate::MiriInterpCxExt<'mir, 'tcx> {
    fn read_handle(
        &mut self,
        handle_op: &OpTy<'tcx, Provenance>,
    ) -> InterpResult<'tcx, Option<Handle>> {
        let this = self.eval_context_mut();

        let scalar = this.read_scalar(handle_op)?;

        Handle::from_scalar(scalar, this)
    }

    /// Helper function to set the last error to `ERROR_INVALID_HANDLE` and return the named `windows` constant
    fn invalid_handle(
        &mut self,
        return_value_name: &str,
    ) -> InterpResult<'tcx, Scalar<Provenance>> {
        let this = self.eval_context_mut();

        let ERROR_INVALID_HANDLE = this.eval_windows("c", "ERROR_INVALID_HANDLE");
        this.set_last_error(ERROR_INVALID_HANDLE)?;

        Ok(this.eval_windows("c", return_value_name))
    }

    fn DuplicateHandle(
        &mut self,
        src_process_op: &OpTy<'tcx, Provenance>, // HANDLE
        src_handle_op: &OpTy<'tcx, Provenance>,  // HANDLE
        dst_process_op: &OpTy<'tcx, Provenance>, // HANDLE
        dst_handle_op: &OpTy<'tcx, Provenance>,  // LPHANDLE
        access_op: &OpTy<'tcx, Provenance>,      // DWORD
        inherit_op: &OpTy<'tcx, Provenance>,     // BOOL
        options_op: &OpTy<'tcx, Provenance>,     // DWORD
    ) -> InterpResult<'tcx, Scalar<Provenance>> /* BOOL */ {
        let this = self.eval_context_mut();

        let src_process = this.read_handle(src_process_op)?;
        let src_handle = this.read_handle(src_handle_op)?;
        let dst_process = this.read_handle(dst_process_op)?;
        let dst_handle = this.read_pointer(dst_handle_op)?;
        this.read_scalar(access_op)?.to_u32()?; // ignored: we require DUPLICATE_SAME_ACCESS
        this.read_scalar(inherit_op)?.to_u32()?; // ignored: inheriting handles is not possible
        let options = this.read_scalar(options_op)?.to_u32()?;

        if [src_process, dst_process] != [Some(Handle::Pseudo(PseudoHandle::CurrentProcess)); 2] {
            return this.invalid_handle("FALSE");
        }

        if options != this.eval_windows_u32("c", "DUPLICATE_SAME_ACCESS") {
            throw_unsup_format!("unsupported `dwOptions` {options:#x} in `DuplicateHandle`");
        }

        let new_handle = match src_handle {
            Some(Handle::Pseudo(PseudoHandle::CurrentThread)) =>
                Handle::Thread(this.get_active_thread()),
            Some(Handle::File(fd)) => {
                let Some(file) = this.machine.file_handler.handles.get_mut(&fd) else {
                    return this.invalid_handle("FALSE");
                };

                let result = file.dup();

                match this.try_unwrap_io_result(result)? {
                    Some(dupped_file) => {
                        let fd = this.machine.file_handler.insert_fd(dupped_file);
                        Handle::File(fd)
                    }
                    None => return this.invalid_handle("FALSE"),
                }
            }
            Some(Handle::Null) | None => return this.invalid_handle("FALSE"),
            Some(handle) => throw_unsup_format!("cannot duplicate {}", handle.describe_kind()),
        };

        if !this.ptr_is_null(dst_handle)? {
            let place = this.deref_pointer_as(dst_handle_op, this.windows_ty_layout("HANDLE"))?;
            this.write_scalar(new_handle.to_scalar(this), &place)?;
        }

        Ok(this.eval_windows("c", "TRUE"))
    }

    fn CloseHandle(
        &mut self,
        handle_op: &OpTy<'tcx, Provenance>, // HANDLE
    ) -> InterpResult<'tcx, Scalar<Provenance>> /* BOOL */ {
        let this = self.eval_context_mut();

        match this.read_handle(handle_op)? {
            Some(Handle::Thread(thread)) => {
                this.detach_thread(thread, /*allow_terminated_joined*/ true)?;
                Ok(this.eval_windows("c", "TRUE"))
            }
            _ => this.invalid_handle("FALSE"),
        }
    }
}
