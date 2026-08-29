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

    /// One-line machine record of why the run cannot answer for this checkout.
    ///
    /// User-facing CLIs print this and exit 2: a missing or mismatched invoking
    /// tree is FL-INV-07 inconclusive, not an invariant panic. Tests still panic
    /// through [`manifest_dir_of`].
    pub fn robot_reason(&self) -> String {
        match self {
            Self::Mismatch {
                compiled_in,
                invoked_from,
            } => format!("reason=cross_tree compiled_in={compiled_in} invoked_from={invoked_from}"),
            Self::InvokingTreeUnknown { compiled_in } => {
                format!("reason=invoking_tree_unknown compiled_in={compiled_in}")
            }
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

/// The calling crate's own directory, or a typed refusal.
///
/// Prefer this from a user-facing binary: a missing `CARGO_MANIFEST_DIR` or a
/// cross-tree bake is inconclusive, not an invariant panic (FL-INV-07).
pub fn try_manifest_dir_of(compiled_in: &str) -> Result<PathBuf, CrossTreeFault> {
    let invoked_from = std::env::var(MANIFEST_DIR_VAR).ok();
    if let Some(fault) = cross_tree_fault(compiled_in, invoked_from.as_deref()) {
        return Err(fault);
    }
    Ok(PathBuf::from(compiled_in))
}

/// The calling crate's own directory, refusing a cross-tree artifact first.
///
/// Panics on a fault. That is the right posture for a test: the binary must not
/// answer for another checkout. User-facing CLIs must use [`try_manifest_dir_of`]
/// (or [`checked_manifest_dir!`] with the `try` arm) and exit typed.
pub fn manifest_dir_of(compiled_in: &str) -> PathBuf {
    match try_manifest_dir_of(compiled_in) {
        Ok(path) => path,
        Err(fault) => panic!("{}", fault.message()),
    }
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
///
/// The `try` arm expands the same `env!` as the panicking arm, so a CLI can take
/// a [`Result`] without growing the k60n raw-site residue. The panicking arm is
/// `$crate::checked_manifest_dir!(try)` plus a panic, not a second `env!`.
#[macro_export]
macro_rules! checked_manifest_dir {
    (try) => {
        $crate::tree_identity::try_manifest_dir_of(env!("CARGO_MANIFEST_DIR"))
    };
    () => {
        match $crate::checked_manifest_dir!(try) {
            Ok(path) => path,
            Err(fault) => panic!("{}", fault.message()),
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn try_manifest_dir_returns_the_invoking_crate_directory() {
        let invoked = std::env::var(MANIFEST_DIR_VAR).expect("cargo sets this for tests");
        assert_eq!(
            try_manifest_dir_of(&invoked).expect("the invoking tree matches itself"),
            PathBuf::from(&invoked)
        );
        let via_try =
            crate::checked_manifest_dir!(try).expect("the try arm is the same check under cargo");
        assert_eq!(via_try, crate::checked_manifest_dir!());
        assert!(via_try.join("Cargo.toml").is_file());
    }

    #[test]
    fn try_manifest_dir_refuses_a_foreign_bake() {
        let fault = try_manifest_dir_of("/data/tmp/wt-foreign/crates/fln-core")
            .expect_err("a foreign bake tree is a fault");
        match &fault {
            CrossTreeFault::Mismatch { compiled_in, .. } => {
                assert_eq!(compiled_in, "/data/tmp/wt-foreign/crates/fln-core");
            }
            other => panic!("expected mismatch, got {other:?}"),
        }
        assert!(fault.robot_reason().starts_with("reason=cross_tree "));
    }

    #[test]
    fn robot_reason_names_an_unknown_invoking_tree() {
        let fault = CrossTreeFault::InvokingTreeUnknown {
            compiled_in: "/compiled".to_string(),
        };
        assert_eq!(
            fault.robot_reason(),
            "reason=invoking_tree_unknown compiled_in=/compiled"
        );
    }
}
