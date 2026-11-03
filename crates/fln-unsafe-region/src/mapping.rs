//! `RegionMapping` — the file-mapping primitive under Marrow's compacted regions
//! (bead fln-wgp, plan §6.4): private copy-on-write file mappings, the
//! at-base fast path, sealing, and page facts.
//!
//! Soundness invariant (the covenant argument for the safe slice views):
//! a `RegionMapping` privately maps a REGULAR file that the region store
//! treats as an immutable artifact (olean/CAS discipline — the same posture
//! the Reference's own loader takes). Linux `MAP_PRIVATE` and Windows
//! `FILE_MAP_COPY` keep writes private to this view. The store must not mutate
//! or truncate a live artifact: such interference can produce an operating
//! system paging fault. The mapping owns its range
//! exclusively: slices borrow it under ordinary borrow rules, and `seal`
//! refuses to run while a mutable borrow could exist (it takes `&mut self`).
//!
//! Page facts (`page_size`) come from `/proc/self/auxv` (`AT_PAGESZ`) on Linux
//! and `GetSystemInfo` on Windows. No libc or additional crate is required.

#[cfg(target_os = "linux")]
use crate::sys;
#[cfg(target_os = "windows")]
use crate::windows;
use std::fs::File;
#[cfg(target_os = "linux")]
use std::os::fd::AsRawFd;
use std::path::Path;

/// Typed mapping failure (FL-INV-07: never a panic, never a partial map).
#[derive(Debug)]
pub enum MapError {
    /// Opening or inspecting the backing file failed.
    Io(std::io::Error),
    /// Zero-length files have no region payload to map.
    Empty,
    /// A native mapping operation failed with its operating-system error code.
    Sys { call: &'static str, errno: i32 },
    /// A mutable view or reseal was requested after `seal`.
    Sealed,
    /// The fixed base did not meet the operating system's mapping alignment.
    MisalignedBase { addr: usize },
}

impl std::fmt::Display for MapError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(e) => write!(f, "region file: {e}"),
            Self::Empty => write!(f, "region file is empty"),
            Self::Sys { call, errno } => write!(f, "{call} failed with OS error {errno}"),
            Self::Sealed => write!(f, "mapping is sealed read-only"),
            Self::MisalignedBase { addr } => {
                write!(f, "fixed base {addr:#x} is not mapping-aligned")
            }
        }
    }
}

impl std::error::Error for MapError {}

/// The operating system's page size. Linux reads `/proc/self/auxv`
/// (`AT_PAGESZ` = 6), falling back to 4096 if auxv is unreadable; Windows
/// queries `GetSystemInfo`. Windows fixed mappings additionally require its
/// allocation granularity, which can be larger than this protection unit.
pub fn page_size() -> usize {
    #[cfg(target_os = "windows")]
    {
        windows::page_geometry().0
    }
    #[cfg(target_os = "linux")]
    {
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
}

#[cfg(target_os = "linux")]
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

    /// Try to map `path` privately AT `base` without replacing any existing
    /// allocation — the Reference's zero-relocation fast path. `Ok(None)`
    /// means the address is unavailable (including the null address, which
    /// cannot back a Rust slice). The caller can use [`Self::map_file_private`]
    /// plus a relocation walk. Windows requires allocation-granularity
    /// alignment; Linux requires page alignment.
    pub fn try_map_file_private_at(
        path: &Path,
        base: usize,
    ) -> Result<Option<RegionMapping>, MapError> {
        #[cfg(target_os = "linux")]
        let alignment = page_size();
        #[cfg(target_os = "windows")]
        let alignment = windows::page_geometry().1;
        if !base.is_multiple_of(alignment) {
            return Err(MapError::MisalignedBase { addr: base });
        }
        if base == 0 {
            return Ok(None);
        }
        match Self::map_common(path, Some(base)) {
            // Older Linux kernels may ignore MAP_FIXED_NOREPLACE. Never
            // publish an at-base success for a mapping at another address;
            // dropping this owned view also releases the unexpected range.
            Ok(mapping) if mapping.addr() != base => Ok(None),
            Ok(mapping) => Ok(Some(mapping)),
            #[cfg(target_os = "linux")]
            Err(MapError::Sys { errno, .. }) if errno == sys::EEXIST => Ok(None),
            #[cfg(target_os = "windows")]
            Err(MapError::Sys {
                call: "MapViewOfFileEx",
                errno,
            }) if errno == windows::ERROR_INVALID_ADDRESS => Ok(None),
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
        // Both slice constructors require a range no larger than isize::MAX.
        // Reject oversized artifacts before requesting any native mapping.
        let len = usize::try_from(meta.len())
            .ok()
            .filter(|len| *len <= isize::MAX as usize)
            .ok_or_else(|| {
                MapError::Io(std::io::Error::new(
                    std::io::ErrorKind::InvalidData,
                    "region file exceeds the maximum slice length",
                ))
            })?;
        if len == 0 {
            return Err(MapError::Empty);
        }
        #[cfg(target_os = "linux")]
        let (addr_hint, flags) = match fixed {
            Some(base) => (base, sys::MAP_PRIVATE | sys::MAP_FIXED_NOREPLACE),
            None => (0, sys::MAP_PRIVATE),
        };
        #[cfg(target_os = "linux")]
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
        #[cfg(target_os = "windows")]
        // SAFETY: the readable regular file stays alive through the call;
        // len is nonzero and slice-bounded; fixed bases are nonnull and
        // allocation-aligned. The returned view belongs to this mapping.
        let addr = unsafe { windows::map_private(&file, len, fixed) }?;
        let mapping = RegionMapping {
            addr,
            len,
            sealed: false,
        };
        if addr == 0 || addr.checked_add(len).is_none() {
            return Err(MapError::Io(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "native mapping cannot be represented by a Rust slice",
            )));
        }
        Ok(mapping)
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

    /// Seal the mapping read-only in the operating system — region hygiene:
    /// after relocation the region is immutable, and hardened builds trap
    /// any write. Idempotent-refusing: sealing twice is the typed `Sealed`
    /// error so state machines stay explicit.
    // UNSAFE-LEDGER: FLN-UL-0061
    #[allow(unsafe_code)]
    pub fn seal(&mut self) -> Result<(), MapError> {
        if self.sealed {
            return Err(MapError::Sealed);
        }
        #[cfg(target_os = "linux")]
        // SAFETY: the range is an owned mapping; `&mut self` proves no live
        // borrow exists while protections narrow.
        unsafe { sys::sys_mprotect(self.addr, round_up_pages(self.len), sys::PROT_READ) }.map_err(
            |errno| MapError::Sys {
                call: "mprotect",
                errno,
            },
        )?;
        #[cfg(target_os = "windows")]
        // SAFETY: the entire range belongs to this view, and `&mut self`
        // excludes live borrows while Windows narrows its page protection.
        unsafe { windows::protect_readonly(self.addr, self.len) }?;
        self.sealed = true;
        Ok(())
    }
}

// UNSAFE-LEDGER: FLN-UL-0062
#[allow(unsafe_code)]
impl Drop for RegionMapping {
    fn drop(&mut self) {
        #[cfg(target_os = "linux")]
        // SAFETY: the range is owned and no borrow can outlive Drop; munmap
        // failure here is unreachable for a well-formed mapping and is
        // deliberately ignored (nothing sound can be done in Drop).
        let _ = unsafe { sys::sys_munmap(self.addr, round_up_pages(self.len)) };
        #[cfg(target_os = "windows")]
        // SAFETY: addr is the original base of this uniquely owned native
        // file view, and all borrowed slices ended before Drop.
        let _ = unsafe { windows::unmap(self.addr) };
    }
}
