//! **fln-unsafe-abi** — Marrow's boundary crate — object layout, tagged-pointer arithmetic, compacted-region relocation, `dlopen` of Reference-ABI plugins, and the exported `lean_*` symbol surface (plan §6, D3).
//!
//! D3 boundary crate: `unsafe` is permitted here ONLY at narrowly scoped
//! `#[allow(unsafe_code)]` sites, each carrying a `// UNSAFE-LEDGER: FLN-UL-NNNN`
//! marker and a matching row in `ci/UNSAFE_LEDGER.txt` (path, invariant, evidence,
//! safe fallback, no-claim boundary). CI rejects unledgered sites. This crate
//! must never depend on `fln-kernel` or `fln-checker` (D3 law a).
//!
//! Bead fln-lld (slice 1) implements the CompatHeap core: the `lean_object`
//! object model with layouts generated from the pinned contract
//! ([`contract`]), membrane-only allocation with the pin's `LEAN_MIMALLOC`
//! observables ([`membrane`]), per-category constructors/accessors
//! ([`object`]), tri-state reference counting with iterative teardown
//! ([`rc`]), tagged-pointer scalars ([`tagged`]), debug ownership shadows
//! ([`shadow`]), and the safe RAII prototype of the eventual fln-rt surface
//! ([`handle`]). Slice 2 opens the reviewed Rust surface: [`handle`] (the
//! safe RAII `Obj` API), [`rc`] (the `Header` view), and [`shadow`] (the
//! ownership-shadow controls) are public, with every exported item carrying
//! a reviewed row in `ci/BOUNDARY_API.txt` — the type-aware half of the D3
//! no-admission export covenant, enforced both directions plus post-expansion
//! by `tools/structure-guard` (FLN-STRUCT-022/025). The raw membrane
//! (`membrane`/`object`/`tagged`/`contract`) stays crate-internal. Bead
//! franken_lean-83r (slice 1) opens the exported `lean_*` C symbol surface
//! ([`export`]): census-signatured `#[unsafe(export_name)]` wrappers over
//! the membrane/object/rc twins, per-symbol status rows in
//! `ci/ABI_EXPORT_STATUS.txt` (§6.5 taxonomy, no unclassified symbol,
//! guard-enforced both directions), and the size-prefixed small heap that
//! serves the pin's sizeless `mi_free` shape. The remaining doors (`dlopen`,
//! outbound linking artifacts) stay with beads franken_lean-sno / fln-kok.
//!
//! Slice-1 typed restrictions (tracked, never silent):
//! * the task plane is LIVE as of fln-3gv slice 3: `task_manager.rs` ports
//!   the pin's manager (workers, promises, sync-inline execution) and the
//!   slice-2 state family carries both arms — manager-served, and the pin's
//!   own managerless envelope with typed refusals where the pin has UB.
//!   Still excluded: the `io.cpp` wrapper family (as_task/map_task/
//!   bind_task/wait/wait_any/cancel/check_canceled) and `wait_any_core` —
//!   fln-3gv next slice;
//! * forcing thunks / applying closures / external `m_foreach` traversal —
//!   bead franken_lean-7xe (Golem apply machinery);
//! * compacted-region loading — bead fln-wgp; the size-classed allocator
//!   backend, deterministic thread-matrix, and soak evidence — fln-8w8 (its
//!   calibrated small-allocation heartbeat hook is installed);
//! * mpz arithmetic — the fln-bignum shim (Crucible workstream).

#![deny(unsafe_code)]
// D3's SAFETY-note half, now enforced here as it already was in the other two boundary
// crates (bead franken_lean-d3-safety-note-unenforced-cdbg). The 28 sites this crate
// carried are written; the waiver that stood here is discharged rather than moved.
//
// There is no declared allowance and that is the point. The sibling bead
// franken_lean-d3-safety-note-clippy-diff-lane-5dkw showed a per-site allowance cannot
// shrink — `#[expect(clippy::undocumented_unsafe_blocks)]` is not reported as unfulfilled
// for clippy's own lints in this toolchain, so a note written without removing its
// attribute would rot silently. At zero sites that question does not arise: the count can
// only go up, and going up is what this denies.
#![deny(clippy::undocumented_unsafe_blocks)]

// The layout mirrors are exact only under the certified target shape: 64-bit,
// little-endian (C bitfield unit `m_cs_sz:16|m_other:8|m_tag:8` byte-splits
// low-to-high; pointers are 8 bytes; `size_t` is `usize` is 8 bytes).
#[cfg(not(all(target_pointer_width = "64", target_endian = "little")))]
compile_error!(
    "fln-unsafe-abi requires a 64-bit little-endian target; the CompatHeap \
     layout mirrors are byte-exact only on the certified platform matrix"
);

mod contract;
#[cfg(all(test, target_os = "linux"))]
mod door;
mod export;
pub mod handle;
mod layout;
mod membrane;
mod object;
pub mod rc;
pub mod shadow;
mod tagged;
mod task_manager;

/// Read this runtime thread's allocation-linked heartbeat counter.
///
/// This is the counter surfaced by `IO.getNumHeartbeats`, not the separate
/// native `check_system` poll counter in the pinned C++ runtime.
pub fn allocation_heartbeats() -> u64 {
    membrane::get_num_heartbeats()
}

/// Replace this runtime thread's allocation-linked heartbeat counter.
///
/// Small Marrow allocations and explicit ABI heartbeat bumps subsequently
/// advance the installed value with wrapping `u64` arithmetic.
pub fn set_allocation_heartbeats(count: u64) {
    membrane::set_heartbeats(count);
}

#[cfg(test)]
mod tests;
