//! Raw Linux memory-mapping syscalls (bead fln-wgp, plan §6.4).
//!
//! The closed universe (D1) has no libc: these are direct `syscall`/`svc`
//! invocations via inline asm, per certified architecture, with the syscall
//! numbers and flag values taken from the kernel's stable userspace ABI
//! (x86_64 and AArch64 use the asm-generic mmap flag values; the syscall
//! numbers differ per table below). Everything here is `pub(crate)`: the
//! reviewed surface is `mapping::RegionMapping`.
//!
//! Error law: the kernel returns `-errno` in `(-4096, 0)`; wrappers surface
//! it as `Err(errno)` — a typed value, never a panic (FL-INV-07 posture).

#![cfg(target_os = "linux")]

// Userspace ABI constants (asm-generic, shared by x86_64 and aarch64).
pub(crate) const PROT_READ: usize = 0x1;
pub(crate) const PROT_WRITE: usize = 0x2;
pub(crate) const MAP_PRIVATE: usize = 0x02;
pub(crate) const MAP_FIXED_NOREPLACE: usize = 0x10_0000;
/// `EEXIST` — `MAP_FIXED_NOREPLACE` found the range occupied.
pub(crate) const EEXIST: i32 = 17;

#[cfg(target_arch = "x86_64")]
mod nr {
    pub(crate) const MMAP: usize = 9;
    pub(crate) const MPROTECT: usize = 10;
    pub(crate) const MUNMAP: usize = 11;
}

#[cfg(target_arch = "aarch64")]
mod nr {
    pub(crate) const MMAP: usize = 222;
    pub(crate) const MPROTECT: usize = 226;
    pub(crate) const MUNMAP: usize = 215;
}

/// One six-argument Linux syscall (x86_64).
///
/// # Safety
/// The syscall number and arguments must form a well-defined kernel request;
/// callers are the three typed wrappers below, each with its own contract.
// UNSAFE-LEDGER: FLN-UL-0053
#[allow(unsafe_code)]
#[cfg(target_arch = "x86_64")]
unsafe fn syscall6(
    nr: usize,
    a0: usize,
    a1: usize,
    a2: usize,
    a3: usize,
    a4: usize,
    a5: usize,
) -> isize {
    let ret: isize;
    // SAFETY: the x86_64 Linux syscall convention — number in rax, args in
    // rdi/rsi/rdx/r10/r8/r9, kernel clobbers rcx/r11, result in rax.
    unsafe {
        core::arch::asm!(
            "syscall",
            inlateout("rax") nr as isize => ret,
            in("rdi") a0,
            in("rsi") a1,
            in("rdx") a2,
            in("r10") a3,
            in("r8") a4,
            in("r9") a5,
            lateout("rcx") _,
            lateout("r11") _,
            options(nostack),
        );
    }
    ret
}

/// One six-argument Linux syscall (AArch64).
///
/// # Safety
/// As the x86_64 variant.
// UNSAFE-LEDGER: FLN-UL-0054
#[allow(unsafe_code)]
#[cfg(target_arch = "aarch64")]
unsafe fn syscall6(
    nr: usize,
    a0: usize,
    a1: usize,
    a2: usize,
    a3: usize,
    a4: usize,
    a5: usize,
) -> isize {
    let ret: isize;
    // SAFETY: the AArch64 Linux syscall convention — number in x8, args in
    // x0..x5, result in x0.
    unsafe {
        core::arch::asm!(
            "svc 0",
            inlateout("x0") a0 as isize => ret,
            in("x1") a1,
            in("x2") a2,
            in("x3") a3,
            in("x4") a4,
            in("x5") a5,
            in("x8") nr,
            options(nostack),
        );
    }
    ret
}

fn decode(ret: isize) -> Result<usize, i32> {
    if (-4095..0).contains(&ret) {
        Err(-(ret as i32))
    } else {
        Ok(ret as usize)
    }
}

/// `mmap(addr, len, prot, flags, fd, 0)`.
///
/// # Safety
/// `len > 0`; when `MAP_FIXED_NOREPLACE` is set, `addr` must be page-aligned;
/// `fd` must be a readable open descriptor for file-backed maps. The returned
/// range is owned by the caller and must be released with [`sys_munmap`].
// UNSAFE-LEDGER: FLN-UL-0055
#[allow(unsafe_code)]
pub(crate) unsafe fn sys_mmap(
    addr: usize,
    len: usize,
    prot: usize,
    flags: usize,
    fd: i32,
) -> Result<usize, i32> {
    // SAFETY: forwards a well-formed mmap request per this function's
    // contract; the kernel validates the rest and reports -errno.
    decode(unsafe { syscall6(nr::MMAP, addr, len, prot, flags, fd as usize, 0) })
}

/// `mprotect(addr, len, prot)`.
///
/// # Safety
/// `[addr, addr+len)` must lie within a mapping owned by the caller;
/// narrowing protections on live borrows is the caller's soundness burden.
// UNSAFE-LEDGER: FLN-UL-0056
#[allow(unsafe_code)]
pub(crate) unsafe fn sys_mprotect(addr: usize, len: usize, prot: usize) -> Result<(), i32> {
    // SAFETY: as sys_mmap.
    decode(unsafe { syscall6(nr::MPROTECT, addr, len, prot, 0, 0, 0) }).map(|_| ())
}

/// `munmap(addr, len)`.
///
/// # Safety
/// `[addr, addr+len)` must be an owned mapping with no live borrows.
// UNSAFE-LEDGER: FLN-UL-0057
#[allow(unsafe_code)]
pub(crate) unsafe fn sys_munmap(addr: usize, len: usize) -> Result<(), i32> {
    // SAFETY: as sys_mmap.
    decode(unsafe { syscall6(nr::MUNMAP, addr, len, 0, 0, 0, 0) }).map(|_| ())
}
