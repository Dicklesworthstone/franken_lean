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
    /// The files carrying `raw_sites` and how many each carries, so a new one is named
    /// rather than merely counted — and so the residue can be declared **per path**
    /// instead of as one number. See [`RAW_SITE_RESIDUE`] for why that distinction is
    /// the whole guard.
    pub raw_files: std::collections::BTreeMap<String, usize>,
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
            *census.raw_files.entry(path.to_string()).or_default() += raw;
        }
        census.checked_sites +=
            contents.matches(CHECKED_ROOT).count() + contents.matches(CHECKED_DIR).count();
    }
    census
}

/// A file resolving paths against its bake tree that the declared residue does not
/// account for.
///
/// Both variants are refusals that **name the file**. The aggregate ceiling this replaced
/// could only say "the total is too high", which is the least useful thing to know about
/// a population spread over eight crates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResidueBreach {
    /// A file carrying raw sites that [`RAW_SITE_RESIDUE`] never declared.
    Undeclared {
        /// Repository-relative path of the offending file.
        path: String,
        /// How many raw sites it carries.
        sites: usize,
    },
    /// A declared file that now carries more raw sites than it was declared to.
    Grown {
        /// Repository-relative path of the offending file.
        path: String,
        /// The count the residue declares.
        declared: usize,
        /// The count measured in the tree.
        measured: usize,
    },
}

impl ResidueBreach {
    /// The operator-facing refusal, naming the file and the repair.
    pub fn message(&self) -> String {
        match self {
            Self::Undeclared { path, sites } => format!(
                "{path} resolves {sites} path(s) against the tree that COMPILED it rather \
                 than the one running it, and the declared residue does not mention this \
                 file at all. A new unprotected rig has appeared. Use \
                 fln_conformance::checked_workspace_root!() (or checked_manifest_dir!()), \
                 or — if the crate cannot reach fln-conformance yet — add the file to \
                 RAW_SITE_RESIDUE in crates/fln-conformance/src/tree_identity.rs and say \
                 why in the commit. Bead fln-cross-tree-baked-root-k60n."
            ),
            Self::Grown {
                path,
                declared,
                measured,
            } => format!(
                "{path} is declared as carrying {declared} raw root resolution(s) and now \
                 carries {measured}. The residue may shrink; it may not grow. Convert the \
                 new site with fln_conformance::checked_workspace_root!() (or \
                 checked_manifest_dir!()), or raise this file's declared count \
                 deliberately and say why. Bead fln-cross-tree-baked-root-k60n."
            ),
        }
    }
}

/// The declared per-file residue: every tracked source that still resolves a repository
/// path against the tree that **compiled** it, and how many such sites it carries.
///
/// **Why per-file and not one total.** The predecessor of this table was a single ceiling
/// (`RAW_CEILING = 46`, against a committed truth of 44). A single number is a *budget*,
/// and a budget is refilled by every repair: converting one rig frees slots that any
/// other file may then take. Measured over the 70 commits from `d40f0c0b` to `017000f0`,
/// that is not a hypothesis — it is what happened. `29cf8a8e` converted
/// `tests/evidence_finalization.rs` from six raw sites to none, dropping the total from 44
/// to 38 and opening eight slots under the ceiling. Four new unprotected sites then landed,
/// in four separate commits, in four different crates, every one of them under a green
/// guard:
///
/// | commit | file | sites |
/// |---|---|---|
/// | `b241943d` | `crates/fln-syntax/tests/golden_vellum.rs` | 0 → 1 |
/// | `6e7531e6` | `tools/structure-guard/tests/real_workspace.rs` | 6 → 7 |
/// | `1b0a9eb1` | `crates/fln-verdict/tests/input_validation.rs` | 0 → 1 |
/// | `8391bafd` | `crates/fln-checker/tests/charter_citations.rs` | 0 → 1 |
///
/// The total never exceeded 42, so the ceiling never fired once. Against this table all
/// four refuse and are named: three as [`ResidueBreach::Undeclared`], one as
/// [`ResidueBreach::Grown`]. That is the bead's acceptance criterion — *a new unprotected
/// site cannot appear silently* — and the ceiling did not meet it.
///
/// **The direction is one-way, deliberately.** Membership is checked in one direction
/// only: every measured file must be declared. A declared file that has been repaired to
/// zero is **not** a failure, because reverse membership is a wall that reddens a correct
/// repair (`franken_lean-closure-binding-exempt-rows-3s8w` states the rule this follows: a
/// declared remainder of permitted violations takes one-way plus a floor; a disclosure of
/// a measured population takes equality both ways — this is the former). The residual hole
/// is exact and worth stating: a repaired file keeps its slot until its row is deleted, so
/// **that one path** could regress up to its old count. Deleting the row is the repairer's
/// obligation, and nothing enforces it. That hole is one named path wide; the ceiling's was
/// the whole workspace.
///
/// **Counts are read from the working tree, not from `HEAD`.** So an in-flight edit that
/// adds a site fails this guard before it lands — which is the point, and which also means
/// one pane's uncommitted work can redden the others. The predecessor of this table chose
/// slack over that risk. The measurement above is why this one does not: four sites in 70
/// commits is a rate the slack cannot absorb, and every breach names the file, so its owner
/// is never in doubt.
///
/// **What is still unconverted, by why.** `fln-conformance`'s own four sites are the two
/// macro definitions and two unit tests that feed the compile-time value in as known-good
/// input; they are counted rather than exempted, because a guard that excuses its own file
/// cannot see a regression added to it. The rest divide three ways, and the division was
/// re-measured at `017000f0` rather than inherited:
///
/// * **8 sites in `tools/structure-guard`** are blocked on *one line*. It is `kind=tool` in
///   `ci/WORKSPACE_GRAPH.txt`, and `FLN-STRUCT-007` exempts tool crates from the layering
///   law outright (`checks.rs:1863`, `(CrateKind::Tool, _) => {}`), so
///   `edge structure-guard -> fln-conformance` is already legal and needs only to be
///   declared alongside a dev-dependency.
/// * **19 sites in nine product crates** are blocked on an *architectural* decision, not a
///   registration. `fln-conformance` is rank 22; every one of those crates ranks below it,
///   so a dev-dependency on it is an upward edge and `FLN-STRUCT-007` refuses it. Reaching
///   them means this check living in a low-rank crate.
/// * **11 sites in `tribunal/epoch-lab`** are in a nested workspace that the members glob
///   never walks, so they are outside the graph entirely — the shape
///   `fln-bench-apparatus-empty-referent-bkw6` warns about, where the scope you measure and
///   the scope you meant are not the same set.
pub const RAW_SITE_RESIDUE: &[(&str, usize)] = &[
    ("crates/fln-checker/tests/charter_citations.rs", 1),
    ("crates/fln-conformance/src/tree_identity.rs", 4),
    ("crates/fln-core/tests/pin_ext_observables.rs", 1),
    ("crates/fln-core/tests/pin_inventory_census.rs", 1),
    ("crates/fln-hash/src/blake3.rs", 1),
    ("crates/fln-hash/tests/domain_enforcement.rs", 1),
    ("crates/fln-hash/tests/schema_registry.rs", 1),
    ("crates/fln-olean/tests/decl_decode.rs", 1),
    ("crates/fln-olean/tests/region_read.rs", 4),
    ("crates/fln-parse/tests/parser_category_inventory.rs", 1),
    ("crates/fln-rt/tests/region_engine.rs", 1),
    ("crates/fln-rt/tests/region_fuzz.rs", 2),
    ("crates/fln-syntax/tests/golden_vellum.rs", 1),
    ("crates/fln-unsafe-region/src/tests.rs", 1),
    ("crates/fln-verdict/src/checker.rs", 1),
    ("crates/fln-verdict/tests/input_validation.rs", 1),
    ("tools/structure-guard/src/contract_handoff.rs", 1),
    ("tools/structure-guard/tests/real_workspace.rs", 7),
    ("tribunal/epoch-lab/examples/derive_report.rs", 1),
    ("tribunal/epoch-lab/src/main.rs", 1),
    ("tribunal/epoch-lab/tests/derived_input_provenance.rs", 6),
    ("tribunal/epoch-lab/tests/epoch_lab_hash_chain.rs", 1),
    ("tribunal/epoch-lab/tests/g0_spike_decision_model.rs", 1),
    ("tribunal/epoch-lab/tests/parity_row_authority.rs", 1),
];

/// Judge a census against a declared residue.
///
/// Pure, so every interesting case — a new file, a grown file, a repaired file, a residue
/// row that outlived its subject — is reachable from a test without staging a repository
/// or waiting for someone to commit the mistake. The live guard is this function plus
/// three floors.
pub fn residue_breaches(
    census: &RootResolutionCensus,
    residue: &[(&str, usize)],
) -> Vec<ResidueBreach> {
    let declared: std::collections::BTreeMap<&str, usize> = residue.iter().copied().collect();
    census
        .raw_files
        .iter()
        .filter_map(|(path, &measured)| match declared.get(path.as_str()) {
            None => Some(ResidueBreach::Undeclared {
                path: path.clone(),
                sites: measured,
            }),
            Some(&decl) if measured > decl => Some(ResidueBreach::Grown {
                path: path.clone(),
                declared: decl,
                measured,
            }),
            Some(_) => None,
        })
        .collect()
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
                .map(|(p, n)| (p.as_str(), *n))
                .collect::<Vec<_>>(),
            vec![("a.rs", 1)],
            "the offending file must be named and counted, not merely counted"
        );
    }

    /// Two sites in one file are two, not one. The per-file count is the whole difference
    /// between this guard and the ceiling it replaced, so a census that collapsed a file
    /// to a boolean would make [`ResidueBreach::Grown`] unreachable and silently readmit
    /// the growth direction.
    #[test]
    fn the_census_counts_sites_within_a_file_rather_than_marking_it() {
        let two = "env!(\"CARGO_MANIFEST_DIR\"); env!(\"CARGO_MANIFEST_DIR\")";
        let measured = census([("a.rs", two)]);
        assert_eq!(measured.raw_sites, 2);
        assert_eq!(measured.raw_files.get("a.rs"), Some(&2));
    }

    /// A tree with nothing in it censuses to zero. That is the state the live guard must
    /// refuse rather than report as clean, which is why it carries a floor on `files`.
    #[test]
    fn an_empty_scan_is_zero_and_therefore_indistinguishable_from_a_clean_one() {
        assert_eq!(census([]), RootResolutionCensus::default());
        assert_eq!(census([("empty.rs", "fn main() {}")]).raw_sites, 0);
    }

    /// A file the residue never declared is named, not merely counted.
    #[test]
    fn an_undeclared_file_is_refused_and_named() {
        let measured = census([("crates/new/tests/rig.rs", "env!(\"CARGO_MANIFEST_DIR\")")]);
        let breaches = residue_breaches(&measured, &[("crates/old/tests/rig.rs", 1)]);
        assert_eq!(
            breaches,
            vec![ResidueBreach::Undeclared {
                path: "crates/new/tests/rig.rs".to_string(),
                sites: 1,
            }]
        );
        assert!(
            breaches[0].message().contains("crates/new/tests/rig.rs"),
            "{}",
            breaches[0].message()
        );
    }

    /// A declared file that grew is refused, with both numbers. This is the case the
    /// aggregate ceiling could not express at all: the file was already in the population,
    /// so no *membership* check sees it either.
    #[test]
    fn a_declared_file_that_grew_is_refused_with_both_counts() {
        let measured = census([(
            "a.rs",
            "env!(\"CARGO_MANIFEST_DIR\") env!(\"CARGO_MANIFEST_DIR\")",
        )]);
        assert_eq!(
            residue_breaches(&measured, &[("a.rs", 1)]),
            vec![ResidueBreach::Grown {
                path: "a.rs".to_string(),
                declared: 1,
                measured: 2,
            }]
        );
    }

    /// **A repair must not redden the workspace.** Converting a rig — and, separately,
    /// leaving a declared row behind that no longer has a subject — are both clean. This
    /// is the one-way direction stated as an executable assertion rather than a comment,
    /// because the wall it avoids is what the predecessor of this guard bought its slack
    /// to avoid, and slack is what let four sites through.
    #[test]
    fn a_repair_and_the_stale_row_it_leaves_are_both_clean() {
        let repaired = census([("a.rs", "checked_workspace_root!()")]);
        assert!(residue_breaches(&repaired, &[("a.rs", 3)]).is_empty());
        assert!(residue_breaches(&repaired, &[]).is_empty());
    }

    /// The four sites that landed under the aggregate ceiling, replayed against this
    /// table's predicate.
    ///
    /// Not a historical note: it is the claim that the replacement is *stronger than the
    /// thing it replaced*, held to code. Between `d40f0c0b` and `017000f0` the total went
    /// 44 → 38 (one repair) → 42 (four new sites) and never touched the ceiling of 46, so
    /// the old guard was green for all four. Each is replayed here in the shape it actually
    /// had — three files absent from the residue of that day, one already present and
    /// grown by one — and all four must refuse.
    #[test]
    fn the_four_sites_the_aggregate_ceiling_admitted_are_each_refused_here() {
        // The residue as it stood at `d40f0c0b`, restricted to the files that moved.
        let then: &[(&str, usize)] = &[("tools/structure-guard/tests/real_workspace.rs", 6)];
        let raw = "env!(\"CARGO_MANIFEST_DIR\")";
        let now = census([
            ("crates/fln-syntax/tests/golden_vellum.rs", raw),
            ("crates/fln-verdict/tests/input_validation.rs", raw),
            ("crates/fln-checker/tests/charter_citations.rs", raw),
            (
                "tools/structure-guard/tests/real_workspace.rs",
                "env!(\"CARGO_MANIFEST_DIR\") env!(\"CARGO_MANIFEST_DIR\") \
                 env!(\"CARGO_MANIFEST_DIR\") env!(\"CARGO_MANIFEST_DIR\") \
                 env!(\"CARGO_MANIFEST_DIR\") env!(\"CARGO_MANIFEST_DIR\") \
                 env!(\"CARGO_MANIFEST_DIR\")",
            ),
        ]);
        let breaches = residue_breaches(&now, then);
        assert_eq!(
            breaches.len(),
            4,
            "all four sites that the ceiling admitted must refuse here: {breaches:?}"
        );
        assert_eq!(
            breaches
                .iter()
                .filter(|b| matches!(b, ResidueBreach::Grown { .. }))
                .count(),
            1,
            "real_workspace.rs was already declared, so its extra site is a growth, not an \
             undeclared file — the distinction the aggregate ceiling could not draw: \
             {breaches:?}"
        );
    }

    /// The residue table itself must be sorted, duplicate-free and free of zero rows.
    ///
    /// A duplicate silently shadows one entry (`BTreeMap::collect` keeps the last), and a
    /// zero row declares a file that may carry nothing, which reads as an exemption while
    /// forbidding everything — a confusing shape either way. Sorted order is what makes a
    /// diff of this table readable, which is the only review this debt gets.
    #[test]
    fn the_declared_residue_is_sorted_unique_and_carries_no_empty_rows() {
        let paths: Vec<&str> = RAW_SITE_RESIDUE.iter().map(|(p, _)| *p).collect();
        let mut sorted = paths.clone();
        sorted.sort_unstable();
        assert_eq!(paths, sorted, "RAW_SITE_RESIDUE must be sorted by path");
        let unique: std::collections::BTreeSet<&str> = paths.iter().copied().collect();
        assert_eq!(
            unique.len(),
            paths.len(),
            "RAW_SITE_RESIDUE has a duplicate"
        );
        assert!(
            RAW_SITE_RESIDUE.iter().all(|(_, n)| *n > 0),
            "a zero row declares a file that may carry nothing and forbids everything"
        );
    }

    /// The coverage claim, re-derived every run and judged **per file**.
    ///
    /// Three assertions, each with a direction chosen deliberately and stated in
    /// [`RAW_SITE_RESIDUE`]: the unprotected population may shrink freely and may not grow
    /// *in any file*; the protected population may grow freely and may not shrink; and a
    /// scan that reads almost nothing refuses rather than reporting a clean tree.
    ///
    /// The scope is **derived** from `git ls-files`, not listed: a hand-written root list
    /// rots, and this repository has already paid for that twice
    /// (`franken_lean-ext-observable-fixture-drift-gap-vqnu`'s twelve evidence roots, and
    /// `bkw6`'s twelve throwaway fixture manifests under `scripts/e2e/artifacts/`, which
    /// a filesystem walk picks up and a tracked-file scan does not).
    ///
    /// **The checked floor excludes this file, and the raw ceiling does not.** The
    /// asymmetry is not convenience, it is the direction of each error. Raw sites are
    /// bounded from *above*, so counting this module's own occurrences is conservative and
    /// a regression added here is still seen. Checked invocations are floored from
    /// *below*, so this module's prose — the two failure messages naming
    /// `checked_workspace_root!()` as the repair — would *inflate* the floor and let real
    /// invocations disappear behind the guard's own advice. That is `fln-8zsq`'s lesson
    /// exactly: the guard's own text is inside its search space, and the fix is to scope
    /// the assertion to the site that must carry the evidence. Measured here: 35 raw
    /// matches of the checked needles, of which **10 are in this file and only 25 are
    /// invocations elsewhere**. The exclusion is derived from [`file!`] rather than
    /// written down, and the derivation refuses if it fails to resolve.
    #[test]
    fn the_tree_check_coverage_claim_matches_the_measured_workspace() {
        const CHECKED_FLOOR: usize = 25;
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

        // Anti-vacuity for the raw needle, scoped to the one site that can never stop
        // carrying it. The two macro definitions below are themselves occurrences, so an
        // empty result here means the needle stopped matching, not that the tree is clean
        // — and a broken needle would otherwise make every count a confident zero.
        let definition_site: Vec<&String> = measured
            .raw_files
            .keys()
            .filter(|path| path.ends_with(file!()))
            .collect();
        assert_eq!(
            definition_site.len(),
            1,
            "the census must find exactly one tracked source ending in {:?} carrying the \
             compile-time form — this module defines the macros in terms of it, so zero \
             means the needle has stopped matching and every count below is a confident \
             zero. Found: {definition_site:?}",
            file!()
        );
        let definition_site = definition_site[0].clone();

        let breaches = residue_breaches(&measured, RAW_SITE_RESIDUE);
        assert!(
            breaches.is_empty(),
            "{}",
            breaches
                .iter()
                .map(ResidueBreach::message)
                .collect::<Vec<_>>()
                .join("\n\n")
        );

        // The floor counts invocations elsewhere; see this test's docs for why this file
        // is excluded here and counted above.
        let elsewhere = census(
            sources
                .iter()
                .filter(|(path, _)| *path != definition_site)
                .map(|(p, t)| (p.as_str(), t.as_str())),
        );
        assert!(
            elsewhere.checked_sites >= CHECKED_FLOOR,
            "only {} rigs outside {definition_site} route through the tree check, below the \
             floor of {CHECKED_FLOOR}: protection was removed rather than added",
            elsewhere.checked_sites
        );
    }
}
