//! Locating the pinned Reference, once, from the lock that pins it.
//!
//! Every rig that consults the oracle needs the same two facts: which tag `SUITE.lock`
//! pins, and where that toolchain lives. Before this module each rig answered them
//! separately — `kernel_replay.rs` hard-codes the elan path, `leanchecker_witness.sh`
//! builds its own, and a third spelling would have shipped with the next rig.
//!
//! That duplication is not merely untidy. A hard-coded path can probe a toolchain the lock
//! does not pin, and the run would look **exactly** as green: the oracle answers, the
//! comparison passes, and the answer is about a different Reference than the one this epoch
//! is defined against. Resolving the tag from `SUITE.lock` — the single pin ceremony
//! (D15) — makes that state unrepresentable rather than unlikely.
//!
//! Absence is never a pass. Callers get [`None`] and are expected to emit a typed skip
//! saying what was *not* established, in the FL-INV-07 spirit: an oracle that could not be
//! consulted has produced no evidence, and a rig that quietly proceeds without one has
//! substituted its own reading for the oracle's answer (bead
//! `fln-parity-ledger-l2-pinned-source-qydn`).

use std::path::{Path, PathBuf};

/// The workspace root, two levels above this crate's manifest.
pub fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .expect("workspace root is two levels above the crate manifest")
}

/// The Reference tag `SUITE.lock` pins, e.g. `v4.32.0`.
pub fn pinned_tag() -> Option<String> {
    let lock = std::fs::read_to_string(workspace_root().join("SUITE.lock")).ok()?;
    tag_from_lock(&lock)
}

/// The commit `SUITE.lock` pins for the Reference.
pub fn pinned_commit() -> Option<String> {
    let lock = std::fs::read_to_string(workspace_root().join("SUITE.lock")).ok()?;
    field_from_lock(&lock, "commit=")
}

/// Split out so the parse is testable without a filesystem, and so a lock that stops
/// naming a reference row fails loudly here rather than silently returning a default.
fn tag_from_lock(lock: &str) -> Option<String> {
    field_from_lock(lock, "tag=")
}

fn field_from_lock(lock: &str, prefix: &str) -> Option<String> {
    lock.lines()
        .find(|line| line.starts_with("reference leanprover/lean4 "))?
        .split_whitespace()
        .find_map(|field| field.strip_prefix(prefix).map(str::to_string))
}

/// The pinned `lean` binary. `FLN_REFERENCE_BIN` overrides for hosts that install the
/// toolchain elsewhere; otherwise the elan layout for the tag the lock pins.
pub fn pinned_lean() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("FLN_REFERENCE_BIN") {
        let p = PathBuf::from(path);
        return p.is_file().then_some(p);
    }
    let home = std::env::var("HOME").ok()?;
    let tag = pinned_tag()?;
    let p = PathBuf::from(home)
        .join(".elan/toolchains")
        .join(format!("leanprover--lean4---{tag}"))
        .join("bin/lean");
    p.is_file().then_some(p)
}

/// A typed skip line naming what was NOT established, for rigs whose oracle is absent.
pub fn skip_notice(rig: &str) -> String {
    format!(
        "SKIP {rig}: the pinned Reference toolchain ({}) was not found. Install it with \
         `elan toolchain install leanprover/lean4:{}` or set FLN_REFERENCE_BIN. This is a \
         typed skip: NOTHING this rig checks has been established by this run.",
        pinned_tag().unwrap_or_else(|| "<unreadable SUITE.lock>".into()),
        pinned_tag().unwrap_or_else(|| "<tag>".into()),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_tag_comes_from_the_reference_row_and_nowhere_else() {
        let lock = "\
# comment\n\
rust-commit deadbeef\n\
suite frankensqlite commit=abc path=/dp/frankensqlite\n\
reference leanprover/lean4 tag=v4.32.0 commit=8c9756b tree=ba16913\n\
corpus leanprover-community/mathlib4 tag=nightly commit=999\n";
        assert_eq!(tag_from_lock(lock).as_deref(), Some("v4.32.0"));
        assert_eq!(field_from_lock(lock, "commit=").as_deref(), Some("8c9756b"));
    }

    /// A lock with no reference row yields None rather than a default: a rig that
    /// defaulted would probe whatever happened to be installed.
    #[test]
    fn a_lock_without_a_reference_row_names_no_tag() {
        assert_eq!(tag_from_lock("rust-commit deadbeef\n"), None);
        // The corpus row must not be mistaken for the reference row.
        assert_eq!(
            tag_from_lock("corpus leanprover-community/mathlib4 tag=nightly commit=1\n"),
            None
        );
    }

    #[test]
    fn the_real_lock_pins_a_reference_tag_and_commit() {
        assert!(pinned_tag().is_some_and(|tag| tag.starts_with('v')));
        assert!(pinned_commit().is_some_and(|commit| commit.len() >= 7));
    }
}
