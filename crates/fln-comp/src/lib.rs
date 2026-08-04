//! **fln-comp** — Golem's compiler — elaborated terms → FIR (LCNF-class IR
//! with borrow inference and constructor reuse) → FLBC bytecode (plan §11.1).
//!
//! The G0-3 prototype includes a bounded stack-safe ingress from an already
//! elaborated closed core expression ([`ingress`]), a target-neutral FIR
//! schema, validator, canonical printer, and mandatory lowering ([`fir`]), plus
//! FLBC's versioned schema, canonical artifact codec, and independent validator
//! ([`flbc`]). A bounded ownership checkpoint inserts eager last-use drops and
//! turns last-use copies into ownership moves for straight-line and CFG SSA
//! functions, including backedges. Straight-line register reuse is partitioned
//! into per-definition value epochs, so overwritten values receive their own
//! exact final read, move, or drop. Non-overlapping CFG register reuse uses
//! path-specific retirement before each replacement, permits distinct
//! branch-local values to converge in the same register, and reaches a
//! deterministic ownership fixed point across backedges. A separate checker
//! reconstructs those epochs or its own CFG backward-demand fixed point and
//! exact ownership joins. Programs that already contain Move or Drop remain
//! byte-identical only after a separate linear/CFG state walk proves every
//! consume, overwrite, join, backedge and terminal balanced and binds the
//! existing instruction counts. Intrinsic, direct-call, closure-capture,
//! dynamic-application, and internal Task/Thunk boundaries bind explicit
//! argument ownership; generated intrinsic and callable results carry their
//! independently checked result classes. It prices the ABI-valued
//! compiler-to-VM path without claiming Lean text parsing, elaboration/type
//! checking, external ABI invocation or export, Borrowed or Unique callable
//! results, LLVM C API execution, explicit FIR phi ownership, unsupported
//! read/write-overlap rewriting, exceptional CFG ownership, alias-sensitive
//! heap uniqueness, constructor reuse, or the complete production W5 pipeline.
//! The crate map and layering are governed by `WORKSPACE_GRAPH.txt` (bead
//! fln-8mj).

#![forbid(unsafe_code)]

pub mod fir;
pub mod flbc;
pub mod ingress;
