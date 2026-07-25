//! **fln-olean** — Grimoire's module codec — byte-compatible `.olean` read and write, `.ilean`, and the olean-next frontier format (plan §7.2–7.4).
//!
//! **Not a stub.** [`region`] is a working by-value reader for real `.olean` files
//! produced by the pinned Reference — fixed header, compacted-region object graph,
//! budgeted iterative traversal — and [`decl`] decodes `ModuleData` constants on top
//! of it. Writing, `.ilean`, and olean-next arrive with their workstream beads; the
//! crate map and layering are governed by `WORKSPACE_GRAPH.txt` (bead fln-8mj).
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
pub mod region;
