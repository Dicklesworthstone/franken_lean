//! Call-site checkout identity for test binaries (bead `fln-cross-tree-baked-root-k60n`).
//!
//! `CARGO_TARGET_DIR` is shared machine-wide. The compile-time manifest-dir
//! `env!` form is a constant, so a test binary answers for the tree that **built** it.
//! These macros expand `env!` at the call site and compare that bake path with the
//! invoking tree cargo puts in the process environment.
//!
//! # Why this lives in fln-core (the same Option B as [`crate::scratch`])
//!
//! The check only protects crates that can *name* it. `fln-conformance` is rank 22,
//! so a dev-dependency from a product crate is an upward edge. `fln-core` is rank 0:
//! every producer crate already sits above it, so hosting the macros here adds
//! **zero dependency edges**. The cost is test-support code in a product crate —
//! the same judgement `scratch` already made and disclosed.
//!
//! The census that *counts* coverage stays in `fln-conformance`. This module is
//! only the check.

use std::path::{Path, PathBuf};

/// The environment variable cargo sets, at compile time for `env!` and again in the
/// environment of the process it launches.
pub const MANIFEST_DIR_VAR: &str = "CARGO_MANIFEST_DIR";

/// Why a run cannot be trusted to describe the tree it was launched from.
///
/// Both variants are refusals. There is deliberately no "probably fine" outcome.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CrossTreeFault {
    /// The binary was compiled for a different checkout than the one running it.
    Mismatch {
        /// The manifest dir baked in at compile time — the tree that built the binary.
        compiled_in: String,
        /// The manifest dir cargo set at run time — the tree that launched it.
        invoked_from: String,
    },
    /// `CARGO_MANIFEST_DIR` was absent from the environment.
    InvokingTreeUnknown {
        /// The manifest dir baked in at compile time.
        compiled_in: String,
    },
}

impl CrossTreeFault {
    /// The operator-facing refusal. Names **both** paths and the real cause.
    pub fn message(&self) -> String {
        match self {
            Self::Mismatch {
                compiled_in,
                invoked_from,
            } => format!(
                "this test binary was COMPILED FOR A DIFFERENT CHECKOUT than the one \
                 running it, so every path it resolves — and every verdict it reports — \
                 describes the other tree.\n  \
                 compiled in:  {compiled_in}\n  \
                 invoked from: {invoked_from}\n\
                 CARGO_TARGET_DIR is shared across checkouts on this machine, and cargo \
                 reuses a test binary built from an identical-bytes copy of the same \
                 package without rebuilding it. Nothing about the reused artifact is \
                 wrong; it is simply about a different repository. Re-run with a target \
                 directory of your own, e.g. \
                 CARGO_TARGET_DIR=/data/tmp/cargo-target-$USER, or run from the checkout \
                 named on the first line. Bead fln-cross-tree-baked-root-k60n."
            ),
            Self::InvokingTreeUnknown { compiled_in } => format!(
                "{MANIFEST_DIR_VAR} is absent from this process's environment, so the \
                 checkout that launched this binary is unknown and it cannot be shown to \
                 match the one it was compiled for ({compiled_in}). Cargo always sets \
                 this variable for the binaries it runs, so this binary was launched \
                 some other way. Run it through cargo. Refusing rather than guessing: a \
                 check that cannot decide must not report a pass. Bead \
                 fln-cross-tree-baked-root-k60n."
            ),
        }
    }
}

/// Compare a call site's baked manifest dir against the invoking one.
pub fn cross_tree_fault(compiled_in: &str, invoked_from: Option<&str>) -> Option<CrossTreeFault> {
    let Some(invoked_from) = invoked_from else {
        return Some(CrossTreeFault::InvokingTreeUnknown {
            compiled_in: compiled_in.to_string(),
        });
    };
    if same_path(compiled_in, invoked_from) {
        return None;
    }
    Some(CrossTreeFault::Mismatch {
        compiled_in: compiled_in.to_string(),
        invoked_from: invoked_from.to_string(),
    })
}

fn same_path(left: &str, right: &str) -> bool {
    if left == right {
        return true;
    }
    match (
        Path::new(left).canonicalize(),
        Path::new(right).canonicalize(),
    ) {
        (Ok(left), Ok(right)) => left == right,
        _ => false,
    }
}

/// The calling crate's own directory, refusing a cross-tree artifact first.
pub fn manifest_dir_of(compiled_in: &str) -> PathBuf {
    let invoked_from = std::env::var(MANIFEST_DIR_VAR).ok();
    if let Some(fault) = cross_tree_fault(compiled_in, invoked_from.as_deref()) {
        panic!("{}", fault.message());
    }
    PathBuf::from(compiled_in)
}

/// The workspace root for a call site, refusing a cross-tree artifact first.
pub fn workspace_root_of(compiled_in: &str) -> PathBuf {
    manifest_dir_of(compiled_in)
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .expect("workspace root is two levels above the crate manifest")
}

/// The workspace root of the tree this run was launched from, or a refusal.
///
/// Expands `env!` at the call site so the check describes the *calling* target.
#[macro_export]
macro_rules! checked_workspace_root {
    () => {
        $crate::tree_identity::workspace_root_of(env!("CARGO_MANIFEST_DIR"))
    };
}

/// The calling crate's own directory in the tree this run was launched from, or a
/// refusal.
#[macro_export]
macro_rules! checked_manifest_dir {
    () => {
        $crate::tree_identity::manifest_dir_of(env!("CARGO_MANIFEST_DIR"))
    };
}
