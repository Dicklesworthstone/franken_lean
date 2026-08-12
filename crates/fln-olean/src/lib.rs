//! **fln-olean** — Grimoire's module codec (plan §7.2–7.4). Today this crate reads
//! `.olean`, writes fresh basic `ModuleData` images, reads/writes the pinned compact
//! `.ilean` projection, and transactionally publishes complete cross-file generations.
//!
//! **Not a stub.** [`region`] is a working by-value reader for real `.olean` files
//! produced by the pinned Reference — fixed header, compacted-region object graph,
//! budgeted iterative traversal — and [`decl`] decodes `ModuleData` constants on top
//! of it. [`write`] constructs fresh expression regions and complete basic module roots
//! under explicit object/byte budgets, preserving expression allocation sharing through
//! the shared runtime compactor. [`ilean`] is a budgeted, typed codec whose emitter recreates
//! the pinned Reference's compact field ordering and omission rules. [`artifact`] stages,
//! verifies, binds, and atomically activates immutable multi-file generations behind one
//! content root. The crate map and layering are governed by `WORKSPACE_GRAPH.txt` (bead
//! fln-8mj).
//!
//! **Not implemented, and therefore not claimed above:** closure-bearing v3 regions and their
//! native-library relocation tables, environment-extension payloads, byte-identical emission
//! against Reference-built fresh modules, collection of fresh `.ilean` data from elaboration,
//! and olean-next. Publication is atomic only for consumers resolving the generation through
//! [`artifact::ArtifactStore`];
//! independently opening conventional flat sibling paths is not a multi-file transaction.
//! The remaining gaps stay owned by bead `franken_lean-0nz` and still block full FL-INV-04
//! write fidelity.
//!
//! Every byte this crate reads is UNTRUSTED. The reader interprets stored pointers
//! as `base_addr`-relative offsets and bounds- and alignment-checks every
//! dereference, so it needs no `unsafe`; malformed input must yield a typed
//! [`region::RegionError`], never a panic, never an abort, and never a
//! silently-partial success. Any length read out of the file is attacker-controlled
//! and must be proven to fit before anything is sized from it.

#![forbid(unsafe_code)]

pub mod artifact;
pub mod decl;
pub mod format;
pub mod ilean;
pub mod rebuild;
pub mod region;
pub mod write;
