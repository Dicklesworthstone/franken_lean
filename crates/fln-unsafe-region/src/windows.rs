//! Native Windows file views for compacted regions (plan §6.4).
//!
//! `PAGE_WRITECOPY` plus `FILE_MAP_COPY` preserves private relocation writes.
//! `MapViewOfFileEx` never replaces an occupied range; `VirtualProtect`
//! enforces sealing. Only the safe `mapping::RegionMapping` surface escapes
//! this crate. ABI declarations follow the Windows SDK's memoryapi.h and
//! sysinfoapi.h contracts, without an additional dependency.
//!
//! https://learn.microsoft.com/windows/win32/api/memoryapi/nf-memoryapi-mapviewoffileex
//! https://learn.microsoft.com/windows/win32/api/sysinfoapi/ns-sysinfoapi-system_info

use crate::mapping::MapError;
use std::ffi::c_void;
use std::fs::File;
use std::os::windows::io::{AsRawHandle, FromRawHandle, OwnedHandle};
use std::ptr;

pub(crate) const ERROR_INVALID_ADDRESS: i32 = 487;
pub(crate) const PAGE_READONLY: u32 = 0x02;
pub(crate) const PAGE_WRITECOPY: u32 = 0x08;
const FILE_MAP_COPY: u32 = 0x01;

// The first SDK field is a union of a DWORD and two WORDs. Its four-byte
// storage suffices here because this backend reads only page geometry.
#[repr(C)]
struct SystemInfo {
    _architecture: u32,
    page_size: u32,
    _minimum_address: *mut c_void,
    _maximum_address: *mut c_void,
    _active_processor_mask: usize,
    _processor_count: u32,
    _processor_type: u32,
    allocation_granularity: u32,
    _processor_level: u16,
    _processor_revision: u16,
}

#[cfg(test)]
#[repr(C)]
struct MemoryBasicInformation {
    _base: *mut c_void,
    _allocation_base: *mut c_void,
    _allocation_protection: u32,
    _partition: u16,
    _region_size: usize,
    _state: u32,
    protection: u32,
    _kind: u32,
}

// UNSAFE-LEDGER: FLN-UL-0664
#[allow(unsafe_code)]
#[link(name = "kernel32")]
unsafe extern "system" {
    #[link_name = "GetSystemInfo"]
    fn get_system_info(info: *mut SystemInfo);
    #[link_name = "CreateFileMappingW"]
    fn create_file_mapping(
        file: *mut c_void,
        attributes: *const c_void,
        protection: u32,
        size_high: u32,
        size_low: u32,
        name: *const u16,
    ) -> *mut c_void;
    #[link_name = "MapViewOfFileEx"]
    fn map_view(
        mapping: *mut c_void,
        access: u32,
        offset_high: u32,
        offset_low: u32,
        len: usize,
        base: *mut c_void,
    ) -> *mut c_void;
    #[link_name = "VirtualProtect"]
    fn virtual_protect(addr: *mut c_void, len: usize, new: u32, old: *mut u32) -> i32;
    #[link_name = "UnmapViewOfFile"]
    fn unmap_view(addr: *const c_void) -> i32;
    #[link_name = "GetLastError"]
    safe fn last_error_code() -> u32;
    #[cfg(test)]
    #[link_name = "VirtualQuery"]
    fn virtual_query(addr: *const c_void, info: *mut MemoryBasicInformation, len: usize) -> usize;
}

fn last_error(call: &'static str) -> MapError {
    MapError::Sys {
        call,
        errno: last_error_code() as i32,
    }
}

/// Page protection size and fixed-view allocation granularity are distinct
/// Windows facts. `GetSystemInfo` always fills the supplied native structure.
// UNSAFE-LEDGER: FLN-UL-0665
#[allow(unsafe_code)]
pub(crate) fn page_geometry() -> (usize, usize) {
    static GEOMETRY: std::sync::OnceLock<(usize, usize)> = std::sync::OnceLock::new();
    *GEOMETRY.get_or_init(|| {
        let mut info = SystemInfo {
            _architecture: 0,
            page_size: 0,
            _minimum_address: ptr::null_mut(),
            _maximum_address: ptr::null_mut(),
            _active_processor_mask: 0,
            _processor_count: 0,
            _processor_type: 0,
            allocation_granularity: 0,
            _processor_level: 0,
            _processor_revision: 0,
        };
        // SAFETY: info is an initialized, correctly aligned SYSTEM_INFO
        // representation with the SDK field widths and order. The API writes
        // the complete value and retains no pointer to it.
        unsafe { get_system_info(&mut info) };
        (
            info.page_size as usize,
            info.allocation_granularity as usize,
        )
    })
}

/// Map exactly `len` bytes of a readable regular file privately.
///
/// # Safety
/// `len` is nonzero, slice-bounded and within the immutable artifact. A fixed
/// base, when present, is nonnull and allocation-aligned. The returned native
/// view is owned by the caller and must be released with `unmap`.
// UNSAFE-LEDGER: FLN-UL-0666
#[allow(unsafe_code)]
pub(crate) unsafe fn map_private(
    file: &File,
    len: usize,
    fixed: Option<usize>,
) -> Result<usize, MapError> {
    // SAFETY: file is an open readable handle for the whole call; the extent
    // is already checked against its metadata. No name or security pointer
    // is supplied, so this creates a fresh, non-inheritable mapping object.
    let raw = unsafe {
        create_file_mapping(
            file.as_raw_handle(),
            ptr::null(),
            PAGE_WRITECOPY,
            ((len as u64) >> 32) as u32,
            len as u32,
            ptr::null(),
        )
    };
    if raw.is_null() {
        return Err(last_error("CreateFileMappingW"));
    }
    // SAFETY: a nonnull CreateFileMappingW result is a fresh owned HANDLE,
    // never INVALID_HANDLE_VALUE. OwnedHandle closes it on every return
    // path; a successfully mapped view retains its own native reference.
    let mapping = unsafe { OwnedHandle::from_raw_handle(raw) };
    // SAFETY: the mapping handle is live, offset zero is aligned, len fits
    // its declared extent, and fixed obeys the native alignment contract.
    // FILE_MAP_COPY creates writable private pages without modifying file
    // data. MapViewOfFileEx refuses occupied ranges instead of replacing them.
    let view = unsafe {
        map_view(
            mapping.as_raw_handle(),
            FILE_MAP_COPY,
            0,
            0,
            len,
            fixed.unwrap_or(0) as *mut c_void,
        )
    };
    if view.is_null() {
        // Capture the error before OwnedHandle's destructor calls Windows.
        return Err(last_error("MapViewOfFileEx"));
    }
    Ok(view as usize)
}

/// Narrow a complete live view to read-only pages.
///
/// # Safety
/// The caller exclusively owns this nonempty view and has no live borrowed
/// slices while its protections change. Windows rounds to containing pages.
// UNSAFE-LEDGER: FLN-UL-0667
#[allow(unsafe_code)]
pub(crate) unsafe fn protect_readonly(addr: usize, len: usize) -> Result<(), MapError> {
    let mut previous = 0;
    // SAFETY: the range lies wholly in one owned mapped view; previous is a
    // live DWORD output, and PAGE_READONLY narrows its original CoW access.
    if unsafe { virtual_protect(addr as *mut c_void, len, PAGE_READONLY, &mut previous) } == 0 {
        return Err(last_error("VirtualProtect"));
    }
    Ok(())
}

/// Release a native file view, including its final partial page.
///
/// # Safety
/// `addr` is the original base returned by MapViewOfFileEx; the caller owns
/// that complete view and all slices borrowed from it have ended.
// UNSAFE-LEDGER: FLN-UL-0668
#[allow(unsafe_code)]
pub(crate) unsafe fn unmap(addr: usize) -> Result<(), MapError> {
    // SAFETY: the unique original view base identifies the complete mapping.
    if unsafe { unmap_view(addr as *const c_void) } == 0 {
        return Err(last_error("UnmapViewOfFile"));
    }
    Ok(())
}

/// Query the real page permissions for the sealing regression, rather than
/// trusting the Rust `sealed` bit to describe the operating system state.
// UNSAFE-LEDGER: FLN-UL-0669
#[allow(unsafe_code)]
#[cfg(test)]
pub(crate) fn page_protection(addr: usize) -> Result<u32, MapError> {
    let mut info = MemoryBasicInformation {
        _base: ptr::null_mut(),
        _allocation_base: ptr::null_mut(),
        _allocation_protection: 0,
        _partition: 0,
        _region_size: 0,
        _state: 0,
        protection: 0,
        _kind: 0,
    };
    // SAFETY: VirtualQuery only inspects the supplied address; info is a
    // correctly sized and aligned native output buffer retained for the call.
    let written = unsafe {
        virtual_query(
            addr as *const c_void,
            &mut info,
            std::mem::size_of::<MemoryBasicInformation>(),
        )
    };
    if written == 0 {
        return Err(last_error("VirtualQuery"));
    }
    if written != std::mem::size_of::<MemoryBasicInformation>() {
        return Err(MapError::Io(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            "VirtualQuery returned an incomplete memory information record",
        )));
    }
    Ok(info.protection)
}
