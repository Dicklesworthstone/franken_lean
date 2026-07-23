//! **fln-conformance** — the Tribunal (plan §18; bead fln-euo bootstrap): the Parity
//! Ledger, the comparison-class normalizers, the oracle-precedence ladder, and the
//! `ORACLE_FALLBACK` poison machinery. Differential rigs consume these; the Reference
//! runs *inside the harness* as the standing differential oracle, forever (D8
//! capacity 1) — never as a component.
//!
//! Bootstrap layout:
//! * [`ledger`] — the row-per-symbol Parity Ledger schema (§18.1): parse, validate,
//!   aggregate; headline percentages are never accepted as evidence (D6);
//! * [`normalize`] — comparison classes as versioned normalizer code: a normalizer
//!   may strip only declared-nonsemantic fields and can never discard an error body
//!   to pass;
//! * [`precedence`] — the oracle-precedence ladder as data; `Unclassified` blocks a
//!   claim, never rounds up;
//! * [`poison`] (feature `oracle-fallback-dev`, compiled out of releases) — the
//!   `ORACLE_FALLBACK` tag that poisons every product of the development-only
//!   lockstep harness: cache-inadmissible, gate-inert (§18.10).
//!
//! The epoch laboratory lives under `tribunal/epochs/<tag>/` (immutable once
//! published; regenerate-and-diff via `scripts/tribunal/gen_epoch_manifest.sh`), and
//! the Reference-vs-Reference smoke differential is `scripts/tribunal/ref_vs_ref.sh`.

#![forbid(unsafe_code)]

pub mod ledger;
pub mod normalize;
pub mod ownership;
#[cfg(feature = "oracle-fallback-dev")]
pub mod poison;
pub mod precedence;
