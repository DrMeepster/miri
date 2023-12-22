use std::any::Any;
use std::collections::BTreeMap;
use std::fs::{File, ReadDir};
use std::io::{self, IsTerminal, Read, Seek, SeekFrom, Write};

use rustc_data_structures::fx::FxHashMap;
use rustc_middle::ty::TyCtxt;

use crate::*;

#[derive(Debug)]
pub struct FileHandle {
    pub file: File,
    pub writable: bool,
}

pub trait FileDescriptor: std::fmt::Debug + Any {
    fn name(&self) -> &'static str;

    fn read<'tcx>(
        &mut self,
        _communicate_allowed: bool,
        _bytes: &mut [u8],
        _tcx: TyCtxt<'tcx>,
    ) -> InterpResult<'tcx, io::Result<usize>> {
        throw_unsup_format!("cannot read from {}", self.name());
    }

    fn write<'tcx>(
        &self,
        _communicate_allowed: bool,
        _bytes: &[u8],
        _tcx: TyCtxt<'tcx>,
    ) -> InterpResult<'tcx, io::Result<usize>> {
        throw_unsup_format!("cannot write to {}", self.name());
    }

    fn seek<'tcx>(
        &mut self,
        _communicate_allowed: bool,
        _offset: SeekFrom,
    ) -> InterpResult<'tcx, io::Result<u64>> {
        throw_unsup_format!("cannot seek on {}", self.name());
    }

    fn close<'tcx>(
        self: Box<Self>,
        _communicate_allowed: bool,
    ) -> InterpResult<'tcx, io::Result<()>> {
        throw_unsup_format!("cannot close {}", self.name());
    }

    fn metadata<'tcx>(
        &mut self,
        _communicate_allowed: bool,
    ) -> InterpResult<'tcx, io::Result<std::fs::Metadata>> {
        throw_unsup_format!("cannot obtain metadata of {}", self.name());
    }

    fn dup(&mut self) -> io::Result<Box<dyn FileDescriptor>>;

    fn is_tty(&self, _communicate_allowed: bool) -> bool {
        false
    }
}

impl dyn FileDescriptor {
    #[inline(always)]
    pub fn downcast_ref<T: Any>(&self) -> Option<&T> {
        (self as &dyn Any).downcast_ref()
    }

    #[inline(always)]
    pub fn downcast_mut<T: Any>(&mut self) -> Option<&mut T> {
        (self as &mut dyn Any).downcast_mut()
    }
}

impl FileDescriptor for FileHandle {
    fn name(&self) -> &'static str {
        "FILE"
    }

    fn read<'tcx>(
        &mut self,
        communicate_allowed: bool,
        bytes: &mut [u8],
        _tcx: TyCtxt<'tcx>,
    ) -> InterpResult<'tcx, io::Result<usize>> {
        assert!(communicate_allowed, "isolation should have prevented even opening a file");
        Ok(self.file.read(bytes))
    }

    fn write<'tcx>(
        &self,
        communicate_allowed: bool,
        bytes: &[u8],
        _tcx: TyCtxt<'tcx>,
    ) -> InterpResult<'tcx, io::Result<usize>> {
        assert!(communicate_allowed, "isolation should have prevented even opening a file");
        Ok((&mut &self.file).write(bytes))
    }

    fn seek<'tcx>(
        &mut self,
        communicate_allowed: bool,
        offset: SeekFrom,
    ) -> InterpResult<'tcx, io::Result<u64>> {
        assert!(communicate_allowed, "isolation should have prevented even opening a file");
        Ok(self.file.seek(offset))
    }

    fn close<'tcx>(
        self: Box<Self>,
        communicate_allowed: bool,
    ) -> InterpResult<'tcx, io::Result<()>> {
        assert!(communicate_allowed, "isolation should have prevented even opening a file");
        // We sync the file if it was opened in a mode different than read-only.
        if self.writable {
            // `File::sync_all` does the checks that are done when closing a file. We do this to
            // to handle possible errors correctly.
            let result = self.file.sync_all();
            // Now we actually close the file.
            drop(self);
            // And return the result.
            Ok(result)
        } else {
            // We drop the file, this closes it but ignores any errors
            // produced when closing it. This is done because
            // `File::sync_all` cannot be done over files like
            // `/dev/urandom` which are read-only. Check
            // https://github.com/rust-lang/miri/issues/999#issuecomment-568920439
            // for a deeper discussion.
            drop(self);
            Ok(Ok(()))
        }
    }

    fn metadata<'tcx>(
        &mut self,
        communicate_allowed: bool,
    ) -> InterpResult<'tcx, io::Result<std::fs::Metadata>> {
        assert!(communicate_allowed, "isolation should have prevented even opening a file");
        Ok(self.file.metadata())
    }

    fn dup(&mut self) -> io::Result<Box<dyn FileDescriptor>> {
        let duplicated = self.file.try_clone()?;
        Ok(Box::new(FileHandle { file: duplicated, writable: self.writable }))
    }

    fn is_tty(&self, communicate_allowed: bool) -> bool {
        communicate_allowed && self.file.is_terminal()
    }
}

impl FileDescriptor for io::Stdin {
    fn name(&self) -> &'static str {
        "stdin"
    }

    fn read<'tcx>(
        &mut self,
        communicate_allowed: bool,
        bytes: &mut [u8],
        _tcx: TyCtxt<'tcx>,
    ) -> InterpResult<'tcx, io::Result<usize>> {
        if !communicate_allowed {
            // We want isolation mode to be deterministic, so we have to disallow all reads, even stdin.
            helpers::isolation_abort_error("`read` from stdin")?;
        }
        Ok(Read::read(self, bytes))
    }

    fn dup(&mut self) -> io::Result<Box<dyn FileDescriptor>> {
        Ok(Box::new(io::stdin()))
    }

    fn is_tty(&self, communicate_allowed: bool) -> bool {
        communicate_allowed && self.is_terminal()
    }
}

impl FileDescriptor for io::Stdout {
    fn name(&self) -> &'static str {
        "stdout"
    }

    fn write<'tcx>(
        &self,
        _communicate_allowed: bool,
        bytes: &[u8],
        _tcx: TyCtxt<'tcx>,
    ) -> InterpResult<'tcx, io::Result<usize>> {
        // We allow writing to stderr even with isolation enabled.
        let result = Write::write(&mut { self }, bytes);
        // Stdout is buffered, flush to make sure it appears on the
        // screen.  This is the write() syscall of the interpreted
        // program, we want it to correspond to a write() syscall on
        // the host -- there is no good in adding extra buffering
        // here.
        io::stdout().flush().unwrap();

        Ok(result)
    }

    fn dup(&mut self) -> io::Result<Box<dyn FileDescriptor>> {
        Ok(Box::new(io::stdout()))
    }

    fn is_tty(&self, communicate_allowed: bool) -> bool {
        communicate_allowed && self.is_terminal()
    }
}

impl FileDescriptor for io::Stderr {
    fn name(&self) -> &'static str {
        "stderr"
    }

    fn write<'tcx>(
        &self,
        _communicate_allowed: bool,
        bytes: &[u8],
        _tcx: TyCtxt<'tcx>,
    ) -> InterpResult<'tcx, io::Result<usize>> {
        // We allow writing to stderr even with isolation enabled.
        // No need to flush, stderr is not buffered.
        Ok(Write::write(&mut { self }, bytes))
    }

    fn dup(&mut self) -> io::Result<Box<dyn FileDescriptor>> {
        Ok(Box::new(io::stderr()))
    }

    fn is_tty(&self, communicate_allowed: bool) -> bool {
        communicate_allowed && self.is_terminal()
    }
}

#[derive(Debug)]
struct NullOutput;

impl FileDescriptor for NullOutput {
    fn name(&self) -> &'static str {
        "stderr and stdout"
    }

    fn write<'tcx>(
        &self,
        _communicate_allowed: bool,
        bytes: &[u8],
        _tcx: TyCtxt<'tcx>,
    ) -> InterpResult<'tcx, io::Result<usize>> {
        // We just don't write anything, but report to the user that we did.
        Ok(Ok(bytes.len()))
    }

    fn dup(&mut self) -> io::Result<Box<dyn FileDescriptor>> {
        Ok(Box::new(NullOutput))
    }
}

#[derive(Debug)]
pub struct FileHandler {
    pub handles: BTreeMap<i32, Box<dyn FileDescriptor>>,
}

impl VisitProvenance for FileHandler {
    fn visit_provenance(&self, _visit: &mut VisitWith<'_>) {
        // All our FileDescriptor do not have any tags.
    }
}

impl FileHandler {
    pub(crate) fn new(mute_stdout_stderr: bool) -> FileHandler {
        let mut handles: BTreeMap<_, Box<dyn FileDescriptor>> = BTreeMap::new();
        handles.insert(0i32, Box::new(io::stdin()));
        if mute_stdout_stderr {
            handles.insert(1i32, Box::new(NullOutput));
            handles.insert(2i32, Box::new(NullOutput));
        } else {
            handles.insert(1i32, Box::new(io::stdout()));
            handles.insert(2i32, Box::new(io::stderr()));
        }
        FileHandler { handles }
    }

    pub fn insert_fd(&mut self, file_handle: Box<dyn FileDescriptor>) -> i32 {
        self.insert_fd_with_min_fd(file_handle, 0)
    }

    pub fn insert_fd_with_min_fd(
        &mut self,
        file_handle: Box<dyn FileDescriptor>,
        min_fd: i32,
    ) -> i32 {
        // Find the lowest unused FD, starting from min_fd. If the first such unused FD is in
        // between used FDs, the find_map combinator will return it. If the first such unused FD
        // is after all other used FDs, the find_map combinator will return None, and we will use
        // the FD following the greatest FD thus far.
        let candidate_new_fd =
            self.handles.range(min_fd..).zip(min_fd..).find_map(|((fd, _fh), counter)| {
                if *fd != counter {
                    // There was a gap in the fds stored, return the first unused one
                    // (note that this relies on BTreeMap iterating in key order)
                    Some(counter)
                } else {
                    // This fd is used, keep going
                    None
                }
            });
        let new_fd = candidate_new_fd.unwrap_or_else(|| {
            // find_map ran out of BTreeMap entries before finding a free fd, use one plus the
            // maximum fd in the map
            self.handles
                .last_key_value()
                .map(|(fd, _)| fd.checked_add(1).unwrap())
                .unwrap_or(min_fd)
        });

        self.handles.try_insert(new_fd, file_handle).unwrap();
        new_fd
    }
}

/// An open directory, tracked by DirHandler.
#[derive(Debug)]
pub struct OpenDir {
    /// The directory reader on the host.
    pub read_dir: ReadDir,
    /// The most recent entry returned by readdir()
    pub entry: Pointer<Option<Provenance>>,
}

impl OpenDir {
    fn new(read_dir: ReadDir) -> Self {
        // We rely on `free` being a NOP on null pointers.
        Self { read_dir, entry: Pointer::null() }
    }
}

#[derive(Debug)]
pub struct DirHandler {
    /// Directory iterators used to emulate libc "directory streams", as used in opendir, readdir,
    /// and closedir.
    ///
    /// When opendir is called, a directory iterator is created on the host for the target
    /// directory, and an entry is stored in this hash map, indexed by an ID which represents
    /// the directory stream. When readdir is called, the directory stream ID is used to look up
    /// the corresponding ReadDir iterator from this map, and information from the next
    /// directory entry is returned. When closedir is called, the ReadDir iterator is removed from
    /// the map.
    pub streams: FxHashMap<u64, OpenDir>,
    /// ID number to be used by the next call to opendir
    next_id: u64,
}

impl DirHandler {
    #[allow(clippy::arithmetic_side_effects)]
    pub fn insert_new(&mut self, read_dir: ReadDir) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        self.streams.try_insert(id, OpenDir::new(read_dir)).unwrap();
        id
    }
}

impl Default for DirHandler {
    fn default() -> DirHandler {
        DirHandler {
            streams: FxHashMap::default(),
            // Skip 0 as an ID, because it looks like a null pointer to libc
            next_id: 1,
        }
    }
}

impl VisitProvenance for DirHandler {
    fn visit_provenance(&self, visit: &mut VisitWith<'_>) {
        let DirHandler { streams, next_id: _ } = self;

        for dir in streams.values() {
            dir.entry.visit_provenance(visit);
        }
    }
}
