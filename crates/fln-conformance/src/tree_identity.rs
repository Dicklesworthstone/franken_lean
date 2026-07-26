//! Refusing a test binary that was compiled for one checkout and is being run from
//! another (bead `fln-cross-tree-baked-root-k60n`).
//!
//! `CARGO_TARGET_DIR` is set machine-wide here and shared by the main tree and every
//! linked worktree. `env!` of [`MANIFEST_DIR_VAR`] is a **compile-time** constant, so a
//! test binary carries the path of whichever tree last compiled it — and cargo treats
//! that artifact as *fresh* when the same package is built from a different tree with
//! identical bytes, rebuilding nothing and saying nothing. Every rig that resolves the
//! repository from its own manifest dir therefore measures the **bake** tree while its
//! reader is standing in the **invoking** one.
//!
//! Measured at `5c5ada4b`: the single compiled `real_workspace` test binary carried
//! `/data/tmp/wt-cc_2/tools/structure-guard`, so `cargo test -p structure-guard --test
//! real_workspace` run from the main tree reported a verdict about another pane's
//! worktree — `INCONCLUSIVE` there, `PASS` here, at the same instant. Today that
//! direction is a loud false red. Swap which tree is dirty and the identical mechanism
//! yields a **false green**: a suite reporting *structurally clean* about a repository
//! that is not the one under test.
//!
//! This is [`AGENTS.md`](../../../AGENTS.md) item 7's join shape turned on the harness
//! itself — a claim and the checkout that produced it, with nothing naming the join. It
//! was already found once and written down as prose inside a bead about something else
//! (`fln-census-empty-referent-no-mock-krb0`, "cheap mitigation, offered not imposed"),
//! and then re-derived from scratch hours later by a reader who could not have known.
//! That is why it is code here and not a paragraph.
//!
//! **The discriminator is exact and does not depend on the working directory.** Cargo
//! also sets `CARGO_MANIFEST_DIR` in the *environment of the test process*, where it
//! names the **invoking** package. So:
//!
//! | reading [`MANIFEST_DIR_VAR`] | names |
//! |---|---|
//! | with `env!`, at compile time | the tree that **built** the binary |
//! | with [`std::env::var`], at run time | the tree that **launched** it |
//!
//! They disagree exactly when a stale cross-tree artifact is being reused.
//! [`std::env::current_dir`] tracks the invoking tree too and was measured to work, but
//! any test that changes directory defeats it, so the environment pair is the better
//! signal.
//!
//! **The check must expand at the call site.** A plain function captures its *own*
//! crate's manifest dir, which answers for the library rather than for the test target
//! that called it — and the two are separately cached, so they can come from different
//! trees. Measured: a `macro_rules!` body expands `env!` in the *calling* crate; a plain
//! function does not. Hence [`checked_workspace_root!`] is a macro and
//! [`workspace_root_of`] takes the call site's manifest dir as an argument.
//!
//! **What this does not earn.** Detection is not prevention: the clean fix is a per-tree
//! target directory, and the sharing is a deliberate machine-level disk cap (see the
//! comment in `.cargo/config.toml`), not this repository's to change. And a refusal only
//! protects the crates that *call* it — the census in [`crate::tree_identity`]'s guard
//! reports how much of the workspace that is, derived rather than asserted, because a
//! mechanism whose coverage is claimed instead of measured is the defect this bead is
//! an instance of.

use std::path::{Path, PathBuf};

/// The environment variable cargo sets, at compile time for `env!` and again in the
/// environment of the process it launches.
pub const MANIFEST_DIR_VAR: &str = "CARGO_MANIFEST_DIR";

/// Why a run cannot be trusted to describe the tree it was launched from.
///
/// Both variants are refusals. There is deliberately no "probably fine" outcome: a check
/// that cannot decide must not report a pass (FL-INV-07, and the pre-commit guard's rule
/// that nothing exits 0 on an unanswered question).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CrossTreeFault {
    /// The binary was compiled for a different checkout than the one running it.
    Mismatch {
        /// The manifest dir baked in at compile time — the tree that built the binary.
        compiled_in: String,
        /// The manifest dir cargo set at run time — the tree that launched it.
        invoked_from: String,
    },
    /// `CARGO_MANIFEST_DIR` was absent from the environment, so the invoking tree is
    /// unknown. Cargo always sets it; its absence means the binary was launched some
    /// other way, and the question this module exists to answer cannot be answered.
    InvokingTreeUnknown {
        /// The manifest dir baked in at compile time.
        compiled_in: String,
    },
}

impl CrossTreeFault {
    /// The operator-facing refusal.
    ///
    /// It names **both** paths and the real cause. The sibling finding
    /// `franken_lean-worktree-gitdir-refusal-hugg` is the standing argument for spending
    /// words here: that failure blamed `ubs`, the census and `vendor/` in three different
    /// lanes while the true line appeared once, and a message naming neither candidate
    /// lets every reader supply whichever cause they arrived with. The observed instance
    /// of *this* fault reports a symlink defect on a path that is a regular file in the
    /// tree the reader is standing in, which is exactly as misleading.
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

/// Compare a call site's baked manifest dir against the invoking one, without touching
/// the environment.
///
/// Split out so the decision is testable at every input, including the two that cannot
/// be produced on demand from inside a passing test run.
///
/// Paths are compared canonically where both sides resolve, and literally otherwise — a
/// bake tree that has since been deleted does not canonicalize, and must still refuse
/// rather than be excused.
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

/// Equality up to symlink resolution, falling back to a literal comparison when a side
/// does not resolve. Never reports equal on an unresolvable pair that differs literally.
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
///
/// `compiled_in` must be the **caller's** own `env!` of [`MANIFEST_DIR_VAR`]; use
/// [`checked_manifest_dir!`] rather than passing it by hand, so the value cannot drift
/// from the crate it is meant to describe.
///
/// Panics on refusal. That is the loud direction, and the right one: the alternative is a
/// verdict about a repository nobody asked about.
pub fn manifest_dir_of(compiled_in: &str) -> PathBuf {
    let invoked_from = std::env::var(MANIFEST_DIR_VAR).ok();
    if let Some(fault) = cross_tree_fault(compiled_in, invoked_from.as_deref()) {
        panic!("{}", fault.message());
    }
    PathBuf::from(compiled_in)
}

/// The workspace root for a call site, refusing a cross-tree artifact first.
///
/// Crate-relative rigs want [`manifest_dir_of`] instead; both refuse identically, because
/// a receipt read out of `crates/<crate>/evidence/` in the wrong checkout is exactly as
/// wrong as a governed document read out of the wrong root.
pub fn workspace_root_of(compiled_in: &str) -> PathBuf {
    manifest_dir_of(compiled_in)
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .expect("workspace root is two levels above the crate manifest")
}

/// The workspace root of the tree this run was launched from, or a refusal.
///
/// Expands `env!` at the call site so the check describes the *calling* target, which is
/// the whole point — see the module docs. Use this anywhere a rig would otherwise walk
/// up two levels from its own compile-time manifest dir.
#[macro_export]
macro_rules! checked_workspace_root {
    () => {
        $crate::tree_identity::workspace_root_of(env!("CARGO_MANIFEST_DIR"))
    };
}

/// The calling crate's own directory in the tree this run was launched from, or a
/// refusal. The crate-relative sibling of [`checked_workspace_root!`]; see its docs for
/// why this expands at the call site.
#[macro_export]
macro_rules! checked_manifest_dir {
    () => {
        $crate::tree_identity::manifest_dir_of(env!("CARGO_MANIFEST_DIR"))
    };
}

/// How much of the workspace resolves its paths through the tree check, and how much
/// still does not — measured, never asserted.
///
/// A mechanism whose coverage is *claimed* is the defect this module is an instance of,
/// so the claim is bound to a count that is re-derived on every run (the technique
/// `fln-bench-apparatus-empty-referent-bkw6` arrived at: when prose and reality can
/// drift, bind the prose to the cardinality of what it asserts).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RootResolutionCensus {
    /// Source files examined. A scan that reads almost nothing is a broken scan, not a
    /// clean tree, so callers assert a floor on this.
    pub files: usize,
    /// Occurrences of the compile-time form, which resolves against the **bake** tree.
    /// Never zero while this module exists: the two macro definitions below are
    /// themselves occurrences, and are deliberately not exempted — a guard that excuses
    /// its own file cannot see a regression added to it.
    pub raw_sites: usize,
    /// Invocations of [`checked_workspace_root!`] / [`checked_manifest_dir!`].
    pub checked_sites: usize,
    /// The files carrying `raw_sites`, so a new one is named rather than merely counted.
    pub raw_files: std::collections::BTreeSet<String>,
}

/// Census a set of `(path, contents)` pairs.
///
/// Pure, so every interesting input — including a tree with no sites at all, which must
/// read as a broken scan rather than a clean one — is reachable from a test without
/// staging a repository.
///
/// The needles are assembled at compile time from fragments so that **this file's own
/// source does not contain them**. That is not self-exemption: the macro definitions
/// below still count, and a raw site added to this module would still be found. It only
/// keeps the scanner's own needle literals out of the population it measures.
pub fn census<'a>(files: impl IntoIterator<Item = (&'a str, &'a str)>) -> RootResolutionCensus {
    const RAW: &str = concat!("env!(\"CARGO_", "MANIFEST_DIR\")");
    const CHECKED_ROOT: &str = concat!("checked_workspace_", "root!(");
    const CHECKED_DIR: &str = concat!("checked_manifest_", "dir!(");

    let mut census = RootResolutionCensus::default();
    for (path, contents) in files {
        census.files += 1;
        let raw = contents.matches(RAW).count();
        if raw > 0 {
            census.raw_sites += raw;
            census.raw_files.insert(path.to_string());
        }
        census.checked_sites +=
            contents.matches(CHECKED_ROOT).count() + contents.matches(CHECKED_DIR).count();
    }
    census
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identical_dirs_are_not_a_fault() {
        assert_eq!(
            cross_tree_fault("/a/b/crates/x", Some("/a/b/crates/x")),
            None
        );
    }

    #[test]
    fn a_foreign_bake_tree_is_refused_and_the_message_names_both() {
        let fault = cross_tree_fault(
            "/data/tmp/wt-cc_2/tools/g",
            Some("/data/projects/fl/tools/g"),
        )
        .expect("differing checkouts are a fault");
        assert_eq!(
            fault,
            CrossTreeFault::Mismatch {
                compiled_in: "/data/tmp/wt-cc_2/tools/g".to_string(),
                invoked_from: "/data/projects/fl/tools/g".to_string(),
            }
        );
        let message = fault.message();
        // Naming both is the whole repair: the observed instance of this fault reported
        // a true statement about the other tree, which read as a false statement about
        // this one. A message carrying one path would be just as misdirecting.
        assert!(message.contains("/data/tmp/wt-cc_2/tools/g"), "{message}");
        assert!(message.contains("/data/projects/fl/tools/g"), "{message}");
        assert!(
            message.contains("COMPILED FOR A DIFFERENT CHECKOUT"),
            "{message}"
        );
        assert!(
            message.contains("fln-cross-tree-baked-root-k60n"),
            "{message}"
        );
    }

    #[test]
    fn an_absent_invoking_tree_refuses_rather_than_assuming_it_matches() {
        let fault =
            cross_tree_fault("/a/b/crates/x", None).expect("an unknown invoker is a refusal");
        assert_eq!(
            fault,
            CrossTreeFault::InvokingTreeUnknown {
                compiled_in: "/a/b/crates/x".to_string(),
            }
        );
        assert!(
            fault.message().contains("cannot decide"),
            "{}",
            fault.message()
        );
    }

    /// A deleted bake tree does not canonicalize. The fallback must refuse, not excuse:
    /// treating "cannot resolve" as "probably the same" would silently readmit exactly
    /// the artifact this module exists to reject.
    #[test]
    fn an_unresolvable_bake_tree_still_refuses() {
        let invoked_from = env!("CARGO_MANIFEST_DIR");
        assert!(
            cross_tree_fault("/no/such/worktree/crates/x", Some(invoked_from)).is_some(),
            "an unresolvable differing path must not be excused"
        );
    }

    /// Two spellings of one directory are the same checkout. Without this the guard would
    /// fire on any symlinked path and become a gate people learn to bypass — the
    /// franken_lean-e5k7 shape.
    #[test]
    fn symlinked_spellings_of_one_tree_are_the_same_tree() {
        let real = env!("CARGO_MANIFEST_DIR");
        let doubled = format!("{real}/./");
        assert_eq!(
            cross_tree_fault(real, Some(&doubled)),
            None,
            "canonically equal paths are one checkout"
        );
    }

    /// The live run must be self-consistent: this very binary was compiled for the tree
    /// running it. If the suite is ever executed from a foreign checkout, this is the
    /// assertion that says so first.
    #[test]
    fn this_binary_was_compiled_for_the_tree_running_it() {
        let root = checked_workspace_root!();
        assert!(
            root.join("AGENTS.md").is_file(),
            "the resolved workspace root has no AGENTS.md: {}",
            root.display()
        );
    }

    /// The needles are assembled from fragments, so prove on synthetic input that they
    /// still match the real spellings — an escaped needle that matches nothing would make
    /// every count below a confident zero (`fln-8zsq`'s lesson, one floor down).
    #[test]
    fn the_census_finds_a_planted_site_of_each_kind() {
        let raw = "fn r() { Path::new(env!(\"CARGO_MANIFEST_DIR\")).join(\"..\") }";
        let checked = "fn r() { fln_conformance::checked_workspace_root!() }";
        let crate_rel = "fn r() { fln_conformance::checked_manifest_dir!().join(\"x\") }";

        let planted = census([("a.rs", raw), ("b.rs", checked), ("c.rs", crate_rel)]);
        assert_eq!(planted.files, 3);
        assert_eq!(planted.raw_sites, 1, "the compile-time form must be found");
        assert_eq!(planted.checked_sites, 2, "both checked forms must be found");
        assert_eq!(
            planted
                .raw_files
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>(),
            vec!["a.rs"],
            "the offending file must be named, not merely counted"
        );
    }

    /// A tree with nothing in it censuses to zero. That is the state the live guard must
    /// refuse rather than report as clean, which is why it carries a floor on `files`.
    #[test]
    fn an_empty_scan_is_zero_and_therefore_indistinguishable_from_a_clean_one() {
        assert_eq!(census([]), RootResolutionCensus::default());
        assert_eq!(census([("empty.rs", "fn main() {}")]).raw_sites, 0);
    }

    /// The coverage claim, bound to a count that is re-derived every run.
    ///
    /// **One-way, plus floors**, because equality in both directions is a wall that
    /// reddens a correct repair — converting a rig would fail a test that demanded the
    /// old number. So: the unprotected population may **shrink** freely and may not grow;
    /// the protected population may **grow** freely and may not shrink; and a scan that
    /// reads almost nothing refuses instead of reporting a clean tree.
    ///
    /// Measured at the landing commit of bead `fln-cross-tree-baked-root-k60n`: **44 raw
    /// occurrences over 22 files, against 21 checked invocations, across 227 tracked
    /// sources**. Four of the 44 are in this very module — the two macro definitions,
    /// which can never go away, and two unit tests that deliberately feed the
    /// compile-time value in as a known-good input — and they are counted rather than
    /// exempted, because a guard that excuses its own file cannot see a regression added
    /// to it. The remaining 40 are rigs in eight crates outside `fln-conformance`, which
    /// cannot call these macros until someone registers the dependency edge in
    /// `ci/WORKSPACE_GRAPH.txt` (the block that stalled `franken_lean-r2st` for two
    /// days). That residue is the open remainder of the bead; the ceiling is what stops
    /// it growing quietly in the meantime.
    ///
    /// The scope is **derived** from `git ls-files`, not listed: a hand-written root list
    /// rots, and this repository has already paid for that twice
    /// (`franken_lean-ext-observable-fixture-drift-gap-vqnu`'s twelve evidence roots, and
    /// `bkw6`'s twelve throwaway fixture manifests under `scripts/e2e/artifacts/`, which
    /// a filesystem walk picks up and a tracked-file scan does not).
    ///
    /// **The ceiling is 46, two above the committed truth of 44, and that gap is not a
    /// rounding.** Contents are read from the **working tree**, so another pane's
    /// uncommitted edit counts — deliberately, since catching a new unprotected rig
    /// *before* it lands is the entire point. At `cc9ecf0f` an in-flight edit to
    /// `tests/evidence_finalization.rs` carries two raw sites beyond its committed six,
    /// and that file belongs to another pane mid-change. Setting the ceiling to 44 would
    /// have reddened the workspace for everyone over work in progress; setting it to 46
    /// leaves it two looser than the repository actually is. **Tighten it to the measured
    /// value once that edit lands** — the number is a promise about the tree, and it is
    /// currently keeping the weaker of two honest promises.
    #[test]
    fn the_tree_check_coverage_claim_matches_the_measured_workspace() {
        const RAW_CEILING: usize = 46;
        const CHECKED_FLOOR: usize = 21;
        const FILES_FLOOR: usize = 200;

        let root = checked_workspace_root!();
        let listed = std::process::Command::new("git")
            .arg("-C")
            .arg(&root)
            .args(["ls-files", "*.rs"])
            .output()
            .expect("git ls-files must run: the census scope is derived from it");
        assert!(
            listed.status.success(),
            "git ls-files failed, so the scope is unknown and no coverage claim can be \
             made: {}",
            String::from_utf8_lossy(&listed.stderr)
        );
        let paths = String::from_utf8(listed.stdout).expect("tracked paths are UTF-8");
        let sources: Vec<(String, String)> = paths
            .lines()
            .filter_map(|path| {
                std::fs::read_to_string(root.join(path))
                    .ok()
                    .map(|text| (path.to_string(), text))
            })
            .collect();
        let measured = census(sources.iter().map(|(p, t)| (p.as_str(), t.as_str())));

        assert!(
            measured.files >= FILES_FLOOR,
            "the census read {} tracked source files, below the floor of {FILES_FLOOR}. A \
             scan that reads almost nothing is a broken scan, not a clean tree",
            measured.files
        );
        assert!(
            measured.raw_sites <= RAW_CEILING,
            "{} rigs now resolve a path against the tree that COMPILED them rather than \
             the one running them, above the declared ceiling of {RAW_CEILING}. A new one \
             has appeared. Use fln_conformance::checked_workspace_root!() (or \
             checked_manifest_dir!()), or raise the ceiling deliberately and say why. \
             Bead fln-cross-tree-baked-root-k60n.\n  carried by: {:?}",
            measured.raw_sites,
            measured.raw_files
        );
        assert!(
            measured.checked_sites >= CHECKED_FLOOR,
            "only {} rigs still route through the tree check, below the floor of \
             {CHECKED_FLOOR}: protection was removed rather than added",
            measured.checked_sites
        );
    }
}
