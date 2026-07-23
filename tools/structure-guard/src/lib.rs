//! **structure-guard** — the workspace structural CI gate (bead fln-8mj).
//!
//! Compares the actual cargo workspace against the reviewed acknowledgment files
//! `ci/WORKSPACE_GRAPH.txt` and `ci/UNSAFE_LEDGER.txt` and enforces, statically:
//!
//! * the **snapshot law** — every crate and every inter-crate dependency edge must be
//!   explicitly acknowledged in the reviewed graph file, both directions;
//! * the **strictly-downward layering** of plan §5/§21 (`rank(from) > rank(to)`);
//! * the **D3 structural laws** — declared transitive prohibitions (no `fln-unsafe-*`
//!   path into `fln-kernel`/`fln-checker`; kernel/checker engine independence);
//! * the **trust-base covenants** — exhaustive direct-dependency allowlists for
//!   `fln-kernel`/`fln-checker` and the ≤ 12 KLOC kernel line-count covenant;
//! * the **unsafe posture** — `#![forbid(unsafe_code)]` at every ordinary crate root,
//!   `#![deny(unsafe_code)]` at boundary-crate roots, and a ledger row for every
//!   `#[allow(unsafe_code)]` site (stale rows fail too);
//! * the **closed dependency universe** (D1) — external dependencies only from the
//!   FrankenSuite allowlist, only by `path`.
//!
//! The guard is deliberately `std`-only (D1 applies to the apparatus too) and parses a
//! constrained, uniform Cargo.toml style; a manifest it cannot parse is a finding, not
//! a guess. Exit codes: 0 clean, 1 findings, 2 setup/parse failure at the root.

#![forbid(unsafe_code)]

pub mod boundary_api;
pub mod checks;
pub mod graph;
pub mod ledger;
pub mod lockfile;
pub mod manifest;
pub mod report;

/// Workspace-relative path of the reviewed graph acknowledgment file.
pub const GRAPH_FILE: &str = "ci/WORKSPACE_GRAPH.txt";
/// Workspace-relative path of the unsafe-boundary ledger.
pub const LEDGER_FILE: &str = "ci/UNSAFE_LEDGER.txt";
/// Workspace-relative path of the reviewed boundary-crate public-API allowlist.
pub const BOUNDARY_API_FILE: &str = "ci/BOUNDARY_API.txt";
/// Workspace-relative path of the governed dependency-closure allowlist (D1).
pub const ALLOWLIST_FILE: &str = "ci/CLOSURE_ALLOWLIST.txt";
/// Workspace-relative path of the one-ceremony pin file.
pub const SUITE_LOCK_FILE: &str = "SUITE.lock";
/// Workspace-relative path of the cargo lockfile the closure audit walks.
pub const LOCK_FILE: &str = "Cargo.lock";
/// Workspace-relative path of the toolchain pin that must agree with SUITE.lock.
pub const TOOLCHAIN_FILE: &str = "rust-toolchain.toml";
/// NDJSON schema identifier for robot output.
pub const NDJSON_SCHEMA: &str = "structure-guard/2";
