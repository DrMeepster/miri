//@only-target-windows: Uses win32 api functions
// We are making scheduler assumptions here.
//@compile-flags: -Zmiri-preemption-rate=0

// On windows, joining main is not UB, but it will block a thread forever.

use std::thread;

extern "system" {
    fn GetCurrentProcess() -> isize;
    fn GetCurrentThread() -> isize;
    fn DuplicateHandle(
        src_proc: isize,
        src_handle: isize,
        dst_proc: isize,
        dst_handle: *mut isize,
        access: u32,
        inherit: u32,
        options: u32,
    ) -> u32;
    fn WaitForSingleObject(handle: isize, timeout: u32) -> u32;
}

const DUPLICATE_SAME_ACCESS: u32 = 2;
const INFINITE: u32 = u32::MAX;

fn main() {
    let mut main_thread = 0;

    unsafe {
        assert_eq!(
            DuplicateHandle(
                GetCurrentProcess(),
                GetCurrentThread(),
                GetCurrentProcess(),
                &mut main_thread,
                0,
                0,
                DUPLICATE_SAME_ACCESS
            ),
            1
        );
    }

    thread::spawn(move || {
        unsafe {
            assert_eq!(WaitForSingleObject(main_thread, INFINITE), 0); //~ ERROR: deadlock: the evaluated program deadlocked
        }
    })
    .join()
    .unwrap();
}
