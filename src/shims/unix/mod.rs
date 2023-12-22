pub mod foreign_items;

mod fs;
mod mem;
mod sync;
mod thread;

mod freebsd;
mod linux;
mod macos;

// Make up some constants.
const UID: u32 = 1000;
