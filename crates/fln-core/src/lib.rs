//! **fln-core** — names, levels, expressions, literals, options, and source positions —
//! the term-plane vocabulary shared by every FrankenLean subsystem (plan §21, §1.1).
//!
//! Everything here is **API surface, not internals**: user metaprograms pattern-match
//! on the constructor inventory and read the cached observables (hashes, loose-bvar
//! ranges, has-fvar/has-mvar flags), so each module reproduces the pinned Reference's
//! semantics bit-for-bit, with a source anchor on every rule. Where upstream would
//! `lean_internal_panic` on a packing overflow, this crate returns a typed error
//! instead — malformed input must never panic (plan D8 taxonomy, FL-INV-07 posture).
//!
//! The layout (bead franken_lean-p8a):
//! * [`lean_hash`] — the observable hash primitives (`mixHash`, `String.hash`);
//!   content addressing is fln-hash's charter, not this;
//! * [`name`] — hierarchical names, `Name.hash`, and both comparison orders;
//! * [`level`] — universe levels, the packed data word, and full normalization
//!   (including the `imax u 0 = 0` collapse Prop impredicativity depends on);
//! * [`expr`] — the kernel expression inventory with per-constructor cached data;
//! * [`options`] — `KVMap`/`DataValue` and the canonical resource limits;
//! * [`pos`] — byte positions and the `FileMap` line/column model;
//! * [`ids`] — the distinct semantic-kind newtypes of §8.2b.

#![forbid(unsafe_code)]

pub mod expr;
pub mod ids;
pub mod lean_hash;
pub mod level;
pub mod name;
pub mod options;
pub mod pos;
