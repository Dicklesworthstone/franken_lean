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
//! (`membrane`/`object`/`tagged`/`contract`) stays crate-internal; the
//! exported `lean_*` C symbol surface is a later slice (per-symbol census
//! join, beads franken_lean-sno / franken_lean-83r).
//!
//! Slice-1 typed restrictions (tracked, never silent):
//! * scheduled tasks/promises (`m_imp != NULL`) — bead fln-3gv (effects on
//!   asupersync);
//! * forcing thunks / applying closures / external `m_foreach` traversal —
//!   bead franken_lean-7xe (Golem apply machinery);
//! * compacted-region loading — bead fln-wgp; the owned allocator — fln-8w8;
//!   mpz arithmetic — the fln-bignum shim (Crucible workstream).

#![deny(unsafe_code)]

// The layout mirrors are exact only under the certified target shape: 64-bit,
// little-endian (C bitfield unit `m_cs_sz:16|m_other:8|m_tag:8` byte-splits
// low-to-high; pointers are 8 bytes; `size_t` is `usize` is 8 bytes).
#[cfg(not(all(target_pointer_width = "64", target_endian = "little")))]
compile_error!(
    "fln-unsafe-abi requires a 64-bit little-endian target; the CompatHeap \
     layout mirrors are byte-exact only on the certified platform matrix"
);

mod contract;
pub mod handle;
mod layout;
mod membrane;
mod object;
pub mod rc;
pub mod shadow;
mod tagged;

#[cfg(test)]
mod tests;
