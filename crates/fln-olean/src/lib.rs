//! **fln-olean** — Grimoire's module codec (plan §7.2–7.4). Today this crate reads
//! `.olean`, writes fresh basic `ModuleData` images, and reads/writes the pinned compact
//! `.ilean` projection.
//!
//! **Not a stub.** [`region`] is a working by-value reader for real `.olean` files
//! produced by the pinned Reference — fixed header, compacted-region object graph,
//! budgeted iterative traversal — and [`decl`] decodes `ModuleData` constants on top
//! of it. [`write`] constructs fresh expression regions and complete basic module roots
//! under explicit object/byte budgets, preserving expression allocation sharing through
//! the shared runtime compactor. [`ilean`] is a budgeted, typed codec whose emitter recreates
//! the pinned Reference's compact field ordering and omission rules. The crate map and
//! layering are governed by `WORKSPACE_GRAPH.txt` (bead fln-8mj).
//!
//! **Not implemented, and therefore not claimed above:** fresh serialization of
//! environment-extension payloads, coordinated `.olean`/`.server`/`.private`/`.ir`
//! publication, byte-identical emission against Reference-built fresh modules, collection
//! of fresh `.ilean` data from elaboration, and olean-next. Those remain the crate's charter
//! under §7.2–7.4 and one of the product's six drop-in surfaces, owned by bead
//! `franken_lean-0nz`; their absence still blocks FL-INV-04 write fidelity and the
//! mixed-producer codec rig (`franken_lean-iwu`).
//!
//! Every byte this crate reads is UNTRUSTED. The reader interprets stored pointers
//! as `base_addr`-relative offsets and bounds- and alignment-checks every
//! dereference, so it needs no `unsafe`; malformed input must yield a typed
//! [`region::RegionError`], never a panic, never an abort, and never a
//! silently-partial success. Any length read out of the file is attacker-controlled
//! and must be proven to fit before anything is sized from it.

#![forbid(unsafe_code)]

pub mod decl;
pub mod format;
pub mod ilean;
pub mod rebuild;
pub mod region;
pub mod write;
