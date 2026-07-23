//! **fln-unsafe-region** — Marrow's region boundary crate — mmap and arena primitives beyond what asupersync region heaps provide: compacted-region mappings, sealing, page facts (plan §6.4, D3).
//!
//! D3 boundary crate: `unsafe` is permitted here ONLY at narrowly scoped
//! `#[allow(unsafe_code)]` sites, each carrying a `// UNSAFE-LEDGER: FLN-UL-NNNN`
//! marker and a matching row in `ci/UNSAFE_LEDGER.txt`. Every public item
//! carries a reviewed `ci/BOUNDARY_API.txt` row (the no-admission export
//! covenant, FLN-STRUCT-022/025). This crate must never depend on
//! `fln-kernel` or `fln-checker` (D3 law a).
//!
//! Bead fln-wgp (slice 1): [`mapping::RegionMapping`] — private copy-on-write
//! file mappings via raw Linux syscalls (the closed universe has no libc;
//! inline asm per certified architecture), the `MAP_FIXED_NOREPLACE` at-base
//! fast path, read-only sealing, and auxv-derived page facts. The safe
//! relocation engine that drives these mappings lives in `fln-rt::region`.

#![deny(unsafe_code)]

// The mapping primitive is Linux-syscall based; the certified platform matrix
// is 64-bit little-endian, and slice 1 is Linux-only (macOS/Windows join with
// their own ledgered primitives when the platform matrix expands).
#[cfg(not(all(
    target_os = "linux",
    target_pointer_width = "64",
    target_endian = "little",
    any(target_arch = "x86_64", target_arch = "aarch64")
)))]
compile_error!(
    "fln-unsafe-region slice 1 requires 64-bit little-endian Linux on \
     x86_64/aarch64; other platforms need their own ledgered mapping primitives"
);

pub mod mapping;
mod sys;

#[cfg(test)]
mod tests;
