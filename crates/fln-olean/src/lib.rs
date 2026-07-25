//! **fln-olean** — Grimoire's module codec (plan §7.2–7.4). **Today this crate reads
//! `.olean`; it does not write it.**
//!
//! **Not a stub.** [`region`] is a working by-value reader for real `.olean` files
//! produced by the pinned Reference — fixed header, compacted-region object graph,
//! budgeted iterative traversal — and [`decl`] decodes `ModuleData` constants on top
//! of it. The crate map and layering are governed by `WORKSPACE_GRAPH.txt` (bead fln-8mj).
//!
//! **Not implemented, and therefore not claimed above:** byte-compatible `.olean` *write*,
//! `.ilean`, and olean-next. There is no encoder in this crate and no `Expr` writer anywhere
//! in the workspace. Those remain the crate's charter under §7.2–7.4 and one of the product's
//! six drop-in surfaces, but **no bead owns the writer yet** — the missing-capability record,
//! including what its absence blocks (FL-INV-04 codec fidelity, the mixed-producer codec rig,
//! `franken_lean-iwu`), is on bead `franken_lean-oh1j`. This header previously asserted read
//! *and* write on line 1 while deferring writing on line 6, which is the overclaim shape the
//! header is now explicit to avoid (bead `fln-olean-doc-self-contradiction-myri`).
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
