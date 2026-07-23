//! **fln-env** — Grimoire's environment (plan §7.1; bead fln-amv): the Reference's
//! name→constant map and contract-registered extensions over persistent structures,
//! so a snapshot is an O(1) clone and mutation after a fork is invisible to the
//! fork — the primitive under Athanor's speculative parallelism (§10.6), Lantern's
//! per-request views (§14.3), and Envoy's search trees (§16.3).
//!
//! Layout:
//! * [`pmap`] — the persistent HAMT (structural sharing, deterministic iteration);
//! * [`constants`] — the eight-kind `ConstantInfo` model, field-anchored to the pin;
//! * [`extensions`] — the extension registry: merge/checkpoint semantics declared by
//!   contract; opaque payloads preserved losslessly, flagged, and conservatively
//!   blocking (never guessed safe);
//! * [`modules`] — lossless direct-import records and the immutable, resource-bounded
//!   module DAG; effective closure and contribution provenance build on this substrate;
//! * [`provenance`] — the separately rooted canonical module/declaration/extension
//!   contribution identity used by invalidation and future Ledger receipts;
//! * [`environment`] — the environment itself, with the logical root (declarations +
//!   extension deltas + options, nothing else) and the separate operational-metadata
//!   root of §7.1.
//!
//! Olean decoding and import-graph replay against real mathlib artifacts arrive with
//! the codec beads (G0-1/W2); this crate owns the in-memory semantics they target.

#![forbid(unsafe_code)]

pub mod constants;
pub mod effective_imports;
pub mod environment;
pub mod extensions;
pub mod modules;
pub mod pmap;
pub mod provenance;
