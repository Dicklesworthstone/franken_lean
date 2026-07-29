//! **fln-conformance** — the Tribunal (plan §18; bead fln-euo bootstrap): the Parity
//! Ledger, the comparison-class normalizers, the oracle-precedence ladder, and the
//! `ORACLE_FALLBACK` poison machinery. Differential rigs consume these; the Reference
//! runs *inside the harness* as the standing differential oracle, forever (D8
//! capacity 1) — never as a component.
//!
//! Bootstrap layout:
//! * [`ledger`] — the row-per-symbol Parity Ledger schema (§18.1): parse, validate,
//!   aggregate; headline percentages are never accepted as evidence (D6);
//! * [`corpus`] — the corpus's durable-format descriptors as a projection of
//!   `fln_hash::canon::SCHEMA_REGISTRY` (bead franken_lean-dgxa, Appendix B): one
//!   specification feeds both the codecs and the corpus, joined in both directions,
//!   and a coverage claim carries the exercise that demonstrates it;
//! * [`witness`] — the claim matrix and its documentation gate (bead
//!   franken_lean-claim-matrix-doc-ci-mhew, Bet B8): every governed claim is a row carrying
//!   its D7 type, its B8 evidence state, and the evidence itself, checked in both directions
//!   so repaired wording cannot regress and a standing overclaim cannot be quietly fixed
//!   without the matrix noticing;
//! * [`naming`] — the suite-wide subsystem-name registry (`ci/SUBSYSTEM_REGISTRY.txt`)
//!   and the current-vocabulary scanner (bead fln-7gr6): reserved codenames cannot
//!   silently re-enter governed prose, contracts, schemas, or mutable bead fields;
//! * [`pin`] — locating the pinned Reference from `SUITE.lock`, once: a rig that
//!   hard-codes a toolchain path can consult a Reference this epoch is not defined
//!   against, and the run looks exactly as green;
//! * [`normalize`] — comparison classes as versioned normalizer code: a normalizer
//!   may strip only declared-nonsemantic fields and can never discard an error body
//!   to pass;
//! * [`precedence`] — the oracle-precedence ladder as data; `Unclassified` blocks a
//!   claim, never rounds up;
//! * [`tree_identity`] — refusing a test binary compiled for a different checkout than
//!   the one running it (bead `fln-cross-tree-baked-root-k60n`): the target directory is
//!   shared across worktrees, so a rig can resolve, measure and report a whole verdict
//!   about a repository that is not the one under test;
//! * [`poison`] (feature `oracle-fallback-dev`, compiled out of releases) — the
//!   `ORACLE_FALLBACK` tag that poisons every product of the development-only
//!   lockstep harness: cache-inadmissible, gate-inert (§18.10).
//!
//! The epoch laboratory lives under `tribunal/epochs/<tag>/` (immutable once
//! published; regenerate-and-diff via `scripts/tribunal/gen_epoch_manifest.sh`), and
//! the Reference-vs-Reference smoke differential is `scripts/tribunal/ref_vs_ref.sh`.

#![forbid(unsafe_code)]

pub mod corpus;
pub mod execution;
pub mod ledger;
pub mod naming;
pub mod normalize;
pub mod ownership;
pub mod pin;
#[cfg(feature = "oracle-fallback-dev")]
pub mod poison;
pub mod precedence;
pub mod trace_replay;
pub mod tree_identity;
pub mod witness;
