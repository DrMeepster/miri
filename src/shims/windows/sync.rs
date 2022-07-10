use crate::thread::Time;
use crate::*;
use rustc_middle::ty::layout::TyAndLayout;
use std::time::{Duration, Instant};

// Private extension trait for local helper methods
impl<'mir, 'tcx: 'mir> EvalContextExtPriv<'mir, 'tcx> for crate::MiriEvalContext<'mir, 'tcx> {}

trait EvalContextExtPriv<'mir, 'tcx: 'mir>: crate::MiriEvalContextExt<'mir, 'tcx> {
    fn get_or_create_id(
        &mut self,
        next_id: Scalar<Tag>,
        value_place: &MPlaceTy<'tcx, Tag>,
    ) -> InterpResult<'tcx, Option<u32>> {
        let this = self.eval_context_mut();

        let (old, success) = this
            .atomic_compare_exchange_scalar(
                value_place,
                &ImmTy::from_uint(0u32, this.machine.layouts.u32),
                next_id.into(),
                AtomicRwOrd::Relaxed,
                AtomicReadOrd::Relaxed,
                false,
            )?
            .to_scalar_pair()
            .expect("compare_exchange returns a scalar pair");

        Ok(if success.to_bool().expect("compare_exchange's second return value is a bool") {
            // Caller of the closure needs to allocate next_id
            None
        } else {
            Some(old.to_u32().expect("layout is u32"))
        })
    }

    // Locks are pointer-sized pieces of data, initialized to 0.
    // We use the first 4 bytes to store the RwLockId.
    fn srwlock_get_or_create_id(
        &mut self,
        lock_op: &OpTy<'tcx, Tag>,
    ) -> InterpResult<'tcx, RwLockId> {
        let this = self.eval_context_mut();
        let value_place = this.deref_operand_and_offset(lock_op, 0, this.machine.layouts.u32)?;

        this.rwlock_get_or_create(|ecx, next_id| {
            Ok(ecx.get_or_create_id(next_id.to_u32_scalar(), &value_place)?.map(RwLockId::from_u32))
        })
    }

    // see above: condvars are implemented identically to locks
    fn condvar_get_or_create_id(
        &mut self,
        condvar_op: &OpTy<'tcx, Tag>,
    ) -> InterpResult<'tcx, CondvarId> {
        let this = self.eval_context_mut();
        let value_place = this.deref_operand_and_offset(condvar_op, 0, this.machine.layouts.u32)?;

        this.condvar_get_or_create(|ecx, next_id| {
            Ok(ecx
                .get_or_create_id(next_id.to_u32_scalar(), &value_place)?
                .map(CondvarId::from_u32))
        })
    }

    /// Try to reacquire the lock associated with the condition variable after we
    /// were signaled.
    fn reacquire_cond_lock(
        &mut self,
        thread: ThreadId,
        lock: RwLockId,
        shared: bool,
    ) -> InterpResult<'tcx> {
        let this = self.eval_context_mut();
        this.unblock_thread(thread);

        if shared {
            if this.rwlock_is_locked(lock) {
                this.rwlock_enqueue_and_block_reader(lock, thread);
            } else {
                this.rwlock_reader_lock(lock, thread);
            }
        } else {
            if this.rwlock_is_write_locked(lock) {
                this.rwlock_enqueue_and_block_writer(lock, thread);
            } else {
                this.rwlock_writer_lock(lock, thread);
            }
        }

        Ok(())
    }

    fn wait_on_address_layout(&mut self, size: u64) -> Option<TyAndLayout<'tcx>> {
        let this = self.eval_context_mut();

        match size {
            1 => Some(this.machine.layouts.u8),
            2 => Some(this.machine.layouts.u16),
            4 => Some(this.machine.layouts.u32),
            8 => Some(this.machine.layouts.u64),
            _ => None,
        }
    }

    fn read_futex_val(
        &mut self,
        ptr_op: &OpTy<'tcx, Tag>,
        layout: TyAndLayout<'tcx>,
    ) -> InterpResult<'tcx, u64> {
        let this = self.eval_context_mut();

        this.check_ptr_access_align(
            this.read_pointer(ptr_op)?,
            layout.size,
            layout.align.abi,
            CheckInAllocMsg::MemoryAccessTest,
        )?;

        let val = this
            .read_scalar_at_offset_atomic(ptr_op, 0, layout, AtomicReadOrd::Relaxed)?
            .check_init()?
            .to_uint(layout.size)?
            .try_into()
            .expect("layout should be only u8, u16, u32 or u64 from wait_on_address_layout");

        Ok(val)
    }
}

impl<'mir, 'tcx> EvalContextExt<'mir, 'tcx> for crate::MiriEvalContext<'mir, 'tcx> {}

#[allow(non_snake_case)]
pub trait EvalContextExt<'mir, 'tcx: 'mir>: crate::MiriEvalContextExt<'mir, 'tcx> {
    fn AcquireSRWLockExclusive(&mut self, lock_op: &OpTy<'tcx, Tag>) -> InterpResult<'tcx> {
        let this = self.eval_context_mut();
        let id = this.srwlock_get_or_create_id(lock_op)?;
        let active_thread = this.get_active_thread();

        if this.rwlock_is_locked(id) {
            // Note: this will deadlock if the lock is already locked by this
            // thread in any way.
            //
            // FIXME: Detect and report the deadlock proactively. (We currently
            // report the deadlock only when no thread can continue execution,
            // but we could detect that this lock is already locked and report
            // an error.)
            this.rwlock_enqueue_and_block_writer(id, active_thread);
        } else {
            this.rwlock_writer_lock(id, active_thread);
        }

        Ok(())
    }

    fn TryAcquireSRWLockExclusive(&mut self, lock_op: &OpTy<'tcx, Tag>) -> InterpResult<'tcx, u8> {
        let this = self.eval_context_mut();
        let id = this.srwlock_get_or_create_id(lock_op)?;
        let active_thread = this.get_active_thread();

        if this.rwlock_is_locked(id) {
            // Lock is already held.
            Ok(0)
        } else {
            this.rwlock_writer_lock(id, active_thread);
            Ok(1)
        }
    }

    fn ReleaseSRWLockExclusive(&mut self, lock_op: &OpTy<'tcx, Tag>) -> InterpResult<'tcx> {
        let this = self.eval_context_mut();
        let id = this.srwlock_get_or_create_id(lock_op)?;
        let active_thread = this.get_active_thread();

        if !this.rwlock_writer_unlock(id, active_thread) {
            // The docs do not say anything about this case, but it seems better to not allow it.
            throw_ub_format!(
                "calling ReleaseSRWLockExclusive on an SRWLock that is not exclusively locked by the current thread"
            );
        }

        Ok(())
    }

    fn AcquireSRWLockShared(&mut self, lock_op: &OpTy<'tcx, Tag>) -> InterpResult<'tcx> {
        let this = self.eval_context_mut();
        let id = this.srwlock_get_or_create_id(lock_op)?;
        let active_thread = this.get_active_thread();

        if this.rwlock_is_write_locked(id) {
            this.rwlock_enqueue_and_block_reader(id, active_thread);
        } else {
            this.rwlock_reader_lock(id, active_thread);
        }

        Ok(())
    }

    fn TryAcquireSRWLockShared(&mut self, lock_op: &OpTy<'tcx, Tag>) -> InterpResult<'tcx, u8> {
        let this = self.eval_context_mut();
        let id = this.srwlock_get_or_create_id(lock_op)?;
        let active_thread = this.get_active_thread();

        if this.rwlock_is_write_locked(id) {
            Ok(0)
        } else {
            this.rwlock_reader_lock(id, active_thread);
            Ok(1)
        }
    }

    fn ReleaseSRWLockShared(&mut self, lock_op: &OpTy<'tcx, Tag>) -> InterpResult<'tcx> {
        let this = self.eval_context_mut();
        let id = this.srwlock_get_or_create_id(lock_op)?;
        let active_thread = this.get_active_thread();

        if !this.rwlock_reader_unlock(id, active_thread) {
            // The docs do not say anything about this case, but it seems better to not allow it.
            throw_ub_format!(
                "calling ReleaseSRWLockShared on an SRWLock that is not locked by the current thread"
            );
        }

        Ok(())
    }

    fn SleepConditionVariableSRW(
        &mut self,
        condvar_op: &OpTy<'tcx, Tag>,
        lock_op: &OpTy<'tcx, Tag>,
        timeout_op: &OpTy<'tcx, Tag>,
        flags_op: &OpTy<'tcx, Tag>,
        dest: &PlaceTy<'tcx, Tag>,
    ) -> InterpResult<'tcx> {
        let this = self.eval_context_mut();
        let condvar_id = this.condvar_get_or_create_id(condvar_op)?;
        let lock_id = this.srwlock_get_or_create_id(lock_op)?;

        let timeout_ms = this.read_scalar(timeout_op)?.to_u32()?;

        let timeout_time = if timeout_ms == this.eval_windows("c", "INFINITE")?.to_u32()? {
            None
        } else {
            this.check_no_isolation("`SleepConditionVariableSRW` with non-infinite timeout")?;

            let duration = Duration::from_millis(timeout_ms as u64);

            Some(Time::Monotonic(Instant::now().checked_add(duration).unwrap()))
        };

        let flags = this.read_scalar(flags_op)?.to_u32()?;

        let shared_mode = 0x1; // CONDITION_VARIABLE_LOCKMODE_SHARED is not in std

        let shared = flags == shared_mode;

        let active_thread = this.get_active_thread();

        let was_locked = if shared {
            this.rwlock_reader_unlock(lock_id, active_thread)
        } else {
            this.rwlock_writer_unlock(lock_id, active_thread)
        };

        if !was_locked {
            throw_ub_format!(
                "calling SleepConditionVariableSRW with an SRWLock that is not locked by the current thread"
            );
        }

        this.block_thread(active_thread);

        this.condvar_wait(condvar_id, active_thread, lock_id.to_u32(), shared);

        if let Some(timeout) = timeout_time {
            let dest = *dest;

            this.register_timeout_callback(
                active_thread,
                timeout,
                Box::new(move |this| {
                    this.reacquire_cond_lock(active_thread, lock_id, shared)?;

                    this.condvar_remove_waiter(condvar_id, active_thread);

                    let error_timeout = this.eval_windows("c", "ERROR_TIMEOUT")?;
                    this.set_last_error(error_timeout)?;
                    this.write_scalar(Scalar::from_i32(0), &dest)?;
                    Ok(())
                }),
            );
        }

        this.write_scalar(Scalar::from_i32(1), dest)?;

        Ok(())
    }

    fn WakeConditionVariable(&mut self, condvar_op: &OpTy<'tcx, Tag>) -> InterpResult<'tcx> {
        let this = self.eval_context_mut();
        let condvar_id = this.condvar_get_or_create_id(condvar_op)?;

        if let Some((thread, lock, shared)) = this.condvar_signal(condvar_id) {
            this.reacquire_cond_lock(thread, RwLockId::from_u32(lock), shared)?;
            this.unregister_timeout_callback_if_exists(thread);
        }

        Ok(())
    }

    fn WakeAllConditionVariable(&mut self, condvar_op: &OpTy<'tcx, Tag>) -> InterpResult<'tcx> {
        let this = self.eval_context_mut();
        let condvar_id = this.condvar_get_or_create_id(condvar_op)?;

        while let Some((thread, lock, shared)) = this.condvar_signal(condvar_id) {
            this.reacquire_cond_lock(thread, RwLockId::from_u32(lock), shared)?;
            this.unregister_timeout_callback_if_exists(thread);
        }

        Ok(())
    }

    fn WaitOnAddress(
        &mut self,
        ptr_op: &OpTy<'tcx, Tag>,
        compare_op: &OpTy<'tcx, Tag>,
        size_op: &OpTy<'tcx, Tag>,
        timeout_op: &OpTy<'tcx, Tag>,
        dest: &PlaceTy<'tcx, Tag>,
    ) -> InterpResult<'tcx> {
        let this = self.eval_context_mut();

        let thread = this.get_active_thread();

        let ptr = this.read_pointer(ptr_op)?;

        let addr = ptr.addr().bytes();

        let compare = this.deref_operand(compare_op)?;
        let size = this.read_scalar(size_op)?.to_machine_usize(this)?;

        let timeout_ms = this.read_scalar(timeout_op)?.to_u32()?;

        let timeout_time = if timeout_ms == this.eval_windows("c", "INFINITE")?.to_u32()? {
            None
        } else {
            this.check_no_isolation("`WaitOnAddress` with non-infinite timeout")?;

            let duration = Duration::from_millis(timeout_ms as u64);

            Some(Time::Monotonic(Instant::now().checked_add(duration).unwrap()))
        };

        let Some(layout) = this.wait_on_address_layout(size) else {
            let invalid_param = this.eval_windows("c", "ERROR_INVALID_PARAMETER")?;
            this.set_last_error(invalid_param)?;
            this.write_scalar(Scalar::from_i32(0), dest)?;
            return Ok(())
        };

        let futex_val = this.read_futex_val(ptr_op, layout)?;

        let undesired = this
            .read_scalar(&compare.into())?
            .check_init()?
            .to_uint(layout.size)?
            .try_into()
            .expect("layout should be only u8, u16, u32 or u64 from wait_on_address_layout");

        if futex_val == undesired {
            this.block_thread(thread);
            this.futex_wait(addr, thread, u32::MAX, Some((undesired, size)));

            if let Some(timeout_time) = timeout_time {
                let dest = *dest;

                this.register_timeout_callback(
                    thread,
                    timeout_time,
                    Box::new(move |this| {
                        this.unblock_thread(thread);
                        this.futex_remove_waiter(addr, thread);
                        let error_timeout = this.eval_windows("c", "ERROR_TIMEOUT")?;
                        this.set_last_error(error_timeout)?;
                        this.write_scalar(Scalar::from_i32(0), &dest)?;
                        Ok(())
                    }),
                )
            }
        }

        this.write_scalar(Scalar::from_i32(1), dest)?;

        Ok(())
    }

    fn WakeByAddressSingle(&mut self, ptr_op: &OpTy<'tcx, Tag>) -> InterpResult<'tcx> {
        let this = self.eval_context_mut();

        let ptr = this.read_pointer(ptr_op)?;

        if let Some(waiter) = this.futex_wake(ptr.addr().bytes(), u32::MAX) {
            let (undesired, size) =
                waiter.undesired.expect("undesired value should always exist on windows");

            let layout = this
                .wait_on_address_layout(size)
                .expect("should have been checked in WaitOnAddress");

            let futex_val = this.read_futex_val(ptr_op, layout)?;

            if futex_val != undesired {
                this.unblock_thread(waiter.thread);
                this.unregister_timeout_callback_if_exists(waiter.thread);
            }
        }

        Ok(())
    }
}
