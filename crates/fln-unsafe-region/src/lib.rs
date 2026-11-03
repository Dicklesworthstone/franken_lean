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
//! file mappings via raw Linux syscalls or native Windows file views. Both
//! backends preserve the non-replacing at-base fast path and kernel-enforced
//! read-only sealing. Page facts come from the operating system. The safe
//! relocation engine that drives these mappings lives in `fln-rt::region`.

#![deny(unsafe_code)]
// D3's SAFETY-note half, enforced here because this crate's library is clean
// (FLN-STRUCT-040). Scope note: a crate-root lint does not reach `examples/`, and
// examples/region_trap_probe.rs still has one undocumented block, tracked on bead
// franken_lean-d3-safety-note-unenforced-cdbg.
#![deny(clippy::undocumented_unsafe_blocks)]

// Region images use the certified 64-bit little-endian object layout. Linux
// and Windows have separate ledgered mapping primitives; other operating
// systems need an implementation with the same CoW and sealing guarantees.
#[cfg(not(all(
    any(target_os = "linux", target_os = "windows"),
    target_pointer_width = "64",
    target_endian = "little",
    any(target_arch = "x86_64", target_arch = "aarch64")
)))]
compile_error!(
    "fln-unsafe-region requires 64-bit little-endian Linux or Windows on \
     x86_64/aarch64; other platforms need their own ledgered mapping primitives"
);

pub mod mapping;
#[cfg(target_os = "linux")]
mod sys;
#[cfg(target_os = "windows")]
mod windows;

#[cfg(test)]
mod tests;
