//! `RegionMapping` — the mmap primitive under Marrow's compacted regions
//! (bead fln-wgp, plan §6.4): private copy-on-write file mappings, the
//! at-base fast path, sealing, and page facts.
//!
//! Soundness invariant (the covenant argument for the safe slice views):
//! a `RegionMapping` privately maps a REGULAR file that the region store
//! treats as an immutable artifact (olean/CAS discipline — the same posture
//! the Reference's own loader takes). `MAP_PRIVATE` isolates the mapping
//! from later file writes on every page this process has touched; a store
//! that truncates a mapped artifact can raise `SIGBUS` — a fault, diagnosed
//! by the fault drills, never silent corruption. The mapping owns its range
//! exclusively: slices borrow it under ordinary borrow rules, and `seal`
//! refuses to run while a mutable borrow could exist (it takes `&mut self`).
//!
//! Page facts (`page_size`) come from `/proc/self/auxv` (`AT_PAGESZ`) — safe
//! file parsing, no libc.

use crate::sys;
use std::fs::File;
use std::os::fd::AsRawFd;
use std::path::Path;

/// Typed mapping failure (FL-INV-07: never a panic, never a partial map).
#[derive(Debug)]
pub enum MapError {
    /// Opening or inspecting the backing file failed.
    Io(std::io::Error),
    /// Zero-length files have no region payload to map.
    Empty,
    /// A syscall failed with the given errno.
    Sys { call: &'static str, errno: i32 },
    /// A mutable view or reseal was requested after `seal`.
    Sealed,
    /// The requested fixed base was not page-aligned.
    MisalignedBase { addr: usize },
}

impl std::fmt::Display for MapError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(e) => write!(f, "region file: {e}"),
            Self::Empty => write!(f, "region file is empty"),
            Self::Sys { call, errno } => write!(f, "{call} failed with errno {errno}"),
            Self::Sealed => write!(f, "mapping is sealed read-only"),
            Self::MisalignedBase { addr } => {
                write!(f, "fixed base {addr:#x} is not page-aligned")
            }
        }
    }
}

impl std::error::Error for MapError {}

/// The system page size, from `/proc/self/auxv` (`AT_PAGESZ` = 6). Falls
/// back to 4096 if the auxv is unreadable (the smallest page size on the
/// certified matrix — a conservative rounding unit for mprotect/munmap).
pub fn page_size() -> usize {
    static PAGE: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *PAGE.get_or_init(|| {
        const AT_PAGESZ: u64 = 6;
        if let Ok(auxv) = std::fs::read("/proc/self/auxv") {
            for pair in auxv.as_chunks::<16>().0 {
                let key = u64::from_le_bytes(pair[0..8].try_into().expect("chunk"));
                let val = u64::from_le_bytes(pair[8..16].try_into().expect("chunk"));
                if key == AT_PAGESZ && val.is_power_of_two() {
                    return usize::try_from(val).expect("page size");
                }
            }
        }
        4096
    })
}

fn round_up_pages(len: usize) -> usize {
    let page = page_size();
    len.div_ceil(page) * page
}

/// A private copy-on-write mapping of a region file. See the module
/// invariant for the safety story behind the slice views.
pub struct RegionMapping {
    addr: usize,
    len: usize,
    sealed: bool,
}

impl RegionMapping {
    /// Map `path` privately (read-write, copy-on-write) at a kernel-chosen
    /// address. Unmodified pages share the page cache with every other
    /// consumer of the file — the PG-4/PG-6 sharing mechanism.
    pub fn map_file_private(path: &Path) -> Result<RegionMapping, MapError> {
        Self::map_common(path, None)
    }

    /// Try to map `path` privately AT `base` (`MAP_FIXED_NOREPLACE`) — the
    /// Reference's zero-relocation fast path. `Ok(None)` when the range is
    /// already occupied; the caller falls back to [`map_file_private`] plus
    /// a relocation walk (the relocate-or-copy law).
    pub fn try_map_file_private_at(
        path: &Path,
        base: usize,
    ) -> Result<Option<RegionMapping>, MapError> {
        if !base.is_multiple_of(page_size()) {
            return Err(MapError::MisalignedBase { addr: base });
        }
        match Self::map_common(path, Some(base)) {
            Ok(mapping) => Ok(Some(mapping)),
            Err(MapError::Sys { errno, .. }) if errno == sys::EEXIST => Ok(None),
            Err(e) => Err(e),
        }
    }

    // UNSAFE-LEDGER: FLN-UL-0058
    #[allow(unsafe_code)]
    fn map_common(path: &Path, fixed: Option<usize>) -> Result<RegionMapping, MapError> {
        let file = File::open(path).map_err(MapError::Io)?;
        let meta = file.metadata().map_err(MapError::Io)?;
        if !meta.is_file() {
            return Err(MapError::Io(std::io::Error::other(
                "region source is not a regular file",
            )));
        }
        let len = usize::try_from(meta.len()).map_err(|_| MapError::Empty)?;
        if len == 0 {
            return Err(MapError::Empty);
        }
        let (addr_hint, flags) = match fixed {
            Some(base) => (base, sys::MAP_PRIVATE | sys::MAP_FIXED_NOREPLACE),
            None => (0, sys::MAP_PRIVATE),
        };
        // SAFETY: len > 0; fixed bases are page-aligned (checked by the
        // caller); the fd is open and readable for the duration of the call
        // (the mapping survives the fd per POSIX). The returned range is
        // owned by the new RegionMapping and released in Drop.
        let addr = unsafe {
            sys::sys_mmap(
                addr_hint,
                len,
                sys::PROT_READ | sys::PROT_WRITE,
                flags,
                file.as_raw_fd(),
            )
        }
        .map_err(|errno| MapError::Sys {
            call: "mmap",
            errno,
        })?;
        Ok(RegionMapping {
            addr,
            len,
            sealed: false,
        })
    }

    /// The mapping's live address (the relocation target base).
    pub fn addr(&self) -> usize {
        self.addr
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn is_sealed(&self) -> bool {
        self.sealed
    }

    /// Borrow the mapped bytes.
    // UNSAFE-LEDGER: FLN-UL-0059
    #[allow(unsafe_code)]
    pub fn as_slice(&self) -> &[u8] {
        // SAFETY: the mapping is live for `len` bytes, exclusively owned by
        // `self`, and aliasing follows ordinary borrow rules (module
        // invariant covers the immutable-artifact posture).
        unsafe { std::slice::from_raw_parts(self.addr as *const u8, self.len) }
    }

    /// Borrow the mapped bytes mutably (copy-on-write pages). Refused after
    /// [`seal`](Self::seal) — writes would fault.
    // UNSAFE-LEDGER: FLN-UL-0060
    #[allow(unsafe_code)]
    pub fn as_mut_slice(&mut self) -> Result<&mut [u8], MapError> {
        if self.sealed {
            return Err(MapError::Sealed);
        }
        // SAFETY: as as_slice, with exclusivity guaranteed by `&mut self`.
        Ok(unsafe { std::slice::from_raw_parts_mut(self.addr as *mut u8, self.len) })
    }

    /// Seal the mapping read-only (`mprotect(PROT_READ)`) — region hygiene:
    /// after relocation the region is immutable, and hardened builds trap
    /// any write. Idempotent-refusing: sealing twice is the typed `Sealed`
    /// error so state machines stay explicit.
    // UNSAFE-LEDGER: FLN-UL-0061
    #[allow(unsafe_code)]
    pub fn seal(&mut self) -> Result<(), MapError> {
        if self.sealed {
            return Err(MapError::Sealed);
        }
        // SAFETY: the range is an owned mapping; `&mut self` proves no live
        // borrow exists while protections narrow.
        unsafe { sys::sys_mprotect(self.addr, round_up_pages(self.len), sys::PROT_READ) }.map_err(
            |errno| MapError::Sys {
                call: "mprotect",
                errno,
            },
        )?;
        self.sealed = true;
        Ok(())
    }
}

// UNSAFE-LEDGER: FLN-UL-0062
#[allow(unsafe_code)]
impl Drop for RegionMapping {
    fn drop(&mut self) {
        // SAFETY: the range is owned and no borrow can outlive Drop; munmap
        // failure here is unreachable for a well-formed mapping and is
        // deliberately ignored (nothing sound can be done in Drop).
        let _ = unsafe { sys::sys_munmap(self.addr, round_up_pages(self.len)) };
    }
}
