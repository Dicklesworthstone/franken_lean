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

/// The precise compile-time form the census counts, assembled from fragments so this
/// module's own source does not contain it.
///
/// **One copy, deliberately.** [`census`] and [`needle_drifts`] must count the *same* needle
/// or the reconciliation between them compares two different questions and can agree while
/// both are wrong. The decoy in [`needle_decoy`] is the part that must stay independent, and
/// it derives from [`MANIFEST_DIR_VAR`] instead.
const RAW_NEEDLE: &str = concat!("env!(\"CARGO_", "MANIFEST_DIR\")");

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
    /// `checked_sites`' sibling map. Needed because the disclosed coverage claim counts
    /// the *crates* carrying invocations, not only the invocations, and a total cannot
    /// answer that question.
    pub checked_files: std::collections::BTreeMap<String, usize>,
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
    const RAW: &str = RAW_NEEDLE;
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
        let checked =
            contents.matches(CHECKED_ROOT).count() + contents.matches(CHECKED_DIR).count();
        if checked > 0 {
            census.checked_sites += checked;
            *census.checked_files.entry(path.to_string()).or_default() += checked;
        }
    }
    census
}

/// A deliberately planted occurrence of the raw form, whose only job is to be **found**.
///
/// **An empty scan must be a failure, not a clean tree.** If the needle in [`census`] stops
/// matching, `raw_sites` becomes 0, [`residue_breaches`] returns nothing, and every
/// judgement built on it passes — a green that means nothing. AGENTS.md records that exact
/// shape three times: `fln-8zsq`'s guard, where a planted mutant survived because a second
/// copy of the qualifier satisfied the check; `franken_lean-2ki4`'s probe, which reported a
/// production heuristic present *after it had been deleted*; and the mandated-mutants lane,
/// where dropping `--ignored` makes the libtest filter match nothing and **exit 0**, green
/// forever while running no campaign.
///
/// **It is built from [`MANIFEST_DIR_VAR`], deliberately NOT from the needle's own
/// fragments.** A decoy assembled from the same fragments as the thing it validates moves
/// with it: break the needle, the decoy breaks identically, and the liveness check passes on
/// a matcher that matches nothing. That is the vacuity trap re-entered *inside* the fix for
/// it, so the decoy derives from the authoritative variable name instead. If
/// `MANIFEST_DIR_VAR` itself changes, both move together — which is correct, because then
/// the variable really did change.
///
/// It returns a `String` rather than being a `const` so this module's own source never
/// contains the literal, which is what keeps the scanner's text out of its own search space.
pub fn needle_decoy() -> String {
    format!("fn decoy() -> &'static str {{ env!(\"{MANIFEST_DIR_VAR}\") }}")
}

/// A file where the coarse and precise matchers disagree about the same source.
///
/// The precise needle is `env!("…")`; the coarse one is the bare variable name, which any
/// occurrence of the precise form must also contain. So `precise <= coarse` always, and
/// **equality is the invariant** everywhere except the files that discuss the needle in
/// prose. That reconciliation is what catches the failure a decoy cannot: production code
/// adopting a spelling the precise needle misses. The counts then diverge per file and are
/// named, instead of the population silently shrinking.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NeedleDrift {
    /// A file mentions the variable more often than the precise form matches, and is not a
    /// declared divergence. Either a new spelling or a runtime read — both need review.
    Spelling {
        /// Repository-relative path.
        path: String,
        /// Occurrences of the bare variable name.
        coarse: usize,
        /// Occurrences of the precise compile-time form.
        precise: usize,
    },
    /// A declared divergence that no longer diverges. Left standing it would excuse a real
    /// drift in that file forever, so it is refused rather than tolerated — the same
    /// direction as deleting a repaired residue row.
    StaleDivergence {
        /// Repository-relative path.
        path: String,
    },
    /// The precise matcher found more than the coarse one, which is arithmetically
    /// impossible for a substring. The matchers are inconsistent and nothing below them can
    /// be trusted.
    Impossible {
        /// Repository-relative path.
        path: String,
        /// Occurrences of the bare variable name.
        coarse: usize,
        /// Occurrences of the precise compile-time form.
        precise: usize,
    },
}

impl NeedleDrift {
    /// The operator-facing refusal, naming the file, both counts and the repair.
    pub fn message(&self) -> String {
        match self {
            Self::Spelling {
                path,
                coarse,
                precise,
            } => format!(
                "{path} mentions the manifest-dir variable {coarse} time(s) but the \
                 compile-time needle matches only {precise}. Either this file uses a \
                 spelling the census cannot see — in which case the census is silently \
                 under-counting the unprotected population and its zero is not a clean tree \
                 — or it reads the variable at run time, which is legitimate and must be \
                 declared in DECLARED_NEEDLE_DIVERGENCE with a reason. Bead \
                 fln-cross-tree-baked-root-k60n."
            ),
            Self::StaleDivergence { path } => format!(
                "{path} is declared in DECLARED_NEEDLE_DIVERGENCE but its coarse and precise \
                 counts now agree, so the declaration excuses nothing and would hide a real \
                 drift in that file forever. Delete the row. Bead \
                 fln-cross-tree-baked-root-k60n."
            ),
            Self::Impossible {
                path,
                coarse,
                precise,
            } => format!(
                "{path} matched the precise needle {precise} time(s) and the bare variable \
                 name only {coarse}. The precise form contains the bare name, so this is \
                 impossible and the two matchers are inconsistent: no count in this module \
                 means anything until that is resolved. Bead \
                 fln-cross-tree-baked-root-k60n."
            ),
        }
    }
}

/// Files whose own text discusses the needle, and so must be cut out of the reconciliation.
///
/// **Cut the region at the first source-reading guard, so only production code is in
/// scope.** `franken_lean-2ki4` is the standing argument: its probe looked for a
/// size-heuristic literal that also appeared inside the `fln-8zsq` guard's *assertion*, so
/// it reported the production heuristic present after it had been deleted. Self-exclusion
/// alone is not enough — every guard body must be out of scope, not merely one's own.
///
/// Checked in **both** directions: an entry that no longer diverges is refused as stale.
pub const DECLARED_NEEDLE_DIVERGENCE: &[(&str, &str)] = &[
    (
        "crates/fln-checker/tests/string_reduce.rs",
        "the KR-314 independence census reads the invoking checker source at run time so a \
         shared target cannot bake another checkout's production reducer into the check \
         (franken_lean-gii.13)",
    ),
    (
        "crates/fln-conformance/src/tree_identity.rs",
        "this module: needle fragments, the run-time read in manifest_dir_of, the failure prose \
         naming the repair, and the decoy's own format string",
    ),
    (
        "crates/fln-syntax/tests/golden_vellum.rs",
        "the VDI4.1 Git audit reads CARGO_MANIFEST_DIR only at run time so a shared target cannot \
         bake another checkout's evidence root into this test binary",
    ),
    (
        "crates/fln-vm/tests/extern_dispatch_no_mock_e2e.rs",
        "the extern dispatch e2e resolves the repository root at run time for its mirror drill, \
         so a shared target cannot bake another checkout's artifacts into the generator it \
         drives (franken_lean-pw6t)",
    ),
    (
        "crates/fln-olean/tests/hostile_input.rs",
        "the hostile-input suite resolves the invoking crate directory at run time so a shared \
         target cannot bake another checkout's fixtures into its byte surgery (fln-abaz)",
    ),
    (
        "crates/fln-kernel/tests/admission_laundering.rs",
        "the laundering suite's serde census reads the invoking crate's own sources at run time, \
         so a shared target cannot bake another checkout's capability module into the check \
         (franken_lean-79k)",
    ),
];

/// Reconcile the precise needle against a coarser, independent one, per file.
///
/// Pure, so a broken needle, a new spelling, a stale declaration and an impossible pair are
/// all reachable from a test without staging a repository.
pub fn needle_drifts<'a>(
    files: impl IntoIterator<Item = (&'a str, &'a str)>,
    declared: &[(&str, &str)],
) -> Vec<NeedleDrift> {
    let declared: std::collections::BTreeSet<&str> =
        declared.iter().map(|(path, _)| *path).collect();
    let mut drifts = Vec::new();
    for (path, contents) in files {
        let coarse = contents.matches(MANIFEST_DIR_VAR).count();
        let precise = contents.matches(RAW_NEEDLE).count();
        if precise > coarse {
            drifts.push(NeedleDrift::Impossible {
                path: path.to_string(),
                coarse,
                precise,
            });
        } else if declared.contains(path) {
            if coarse == precise {
                drifts.push(NeedleDrift::StaleDivergence {
                    path: path.to_string(),
                });
            }
        } else if coarse != precise {
            drifts.push(NeedleDrift::Spelling {
                path: path.to_string(),
                coarse,
                precise,
            });
        }
    }
    drifts
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
/// cannot see a regression added to it. The rest divide **two** ways — it was three until
/// the `tools/structure-guard` population was converted, and the division is re-measured
/// on every run by [`coverage_populations`] rather than inherited from this comment:
///
/// * **19 sites in nine product crates**, blocked by a **decision about where this check
///   lives** rather than by an architectural impossibility — this bullet said
///   "architecturally" until `839ff2ec`, which is an *overstatement* of a sound premise and
///   the milder of the two directions the residue prose got wrong. The premise holds:
///   `fln-conformance` is rank 22, `checks.rs`'s layering loop iterates `actual_edges`
///   without consulting `dep.section`, so a dev-dependency from below is scored exactly like
///   a normal one and `FLN-STRUCT-007` refuses it. The conclusion does not: **`fln-core` is
///   rank 0**, every one of those crates sits at or above it, and **five of the eight
///   already declare an edge to it** — `fln-hash`, `fln-olean`, `fln-parse`, `fln-verdict`,
///   `fln-syntax` — so they are convertible with **no graph change at all**. Only `fln-rt`,
///   `fln-unsafe-region` and `fln-checker` need a new edge, and only `fln-checker`'s also
///   touches the §8 kernel/checker allowlist. The block is on this check's **address**, and
///   moving it into the rank-0 foundation crate grows that crate's exported surface, which
///   is the graph owner's call and plan §21's — routed, not taken.
/// * **1 site in `tribunal/epoch-lab`**, down from 11, and what the other ten cost is the
///   point: **nothing**. That population read as blocked because it sits in a nested
///   workspace the members glob never walks — `fln-bench-apparatus-empty-referent-bkw6`'s
///   shape, where the scope you measure and the scope you meant are different sets. But
///   being outside the graph is the *reason it is reachable*, not a reason it is not: the
///   lab is governed by no layering law, already path-depends into the product workspace
///   (`fln-hash`), and owns its own `Cargo.lock`. A `dev-dependency` on `fln-conformance`
///   therefore adds **no governance row and does not touch the root lock**, which is exactly
///   the pair of concerns that crate's own manifest comment records. Measured, not assumed:
///   `cargo check --tests --examples` there is clean and only `tribunal/epoch-lab/Cargo.lock`
///   moves.
///
///   The one that remains is `src/main.rs`, and it is a **different** blocker rather than a
///   leftover: a `dev-dependency` reaches `tests/` and `examples/` and not a `bin` target, so
///   converting it means a *normal* dependency putting a rank-22 crate into the lab binary's
///   runtime closure. That is a trade worth stating rather than making silently.
///
/// **`tools/structure-guard` is converted, and its rows are gone from this table rather
/// than zeroed.** That was the population blocked on *one line*: the crate is `kind=tool`
/// in `ci/WORKSPACE_GRAPH.txt`, `FLN-STRUCT-007` exempts tool crates from the layering law
/// outright (`checks.rs:1863`, `(CrateKind::Tool, _) => {}`), and `DEP_SECTIONS`
/// (`manifest.rs:45`) counts `dev-dependencies`, so the edge needed a dev-dependency plus
/// one acknowledgement row and nothing else. Deleting the rows rather than setting them to
/// zero is the repairer's obligation stated three paragraphs up: a retained row keeps its
/// slot, and that one path could then regress up to its old count silently. With the rows
/// gone, a raw site returning to either file is [`ResidueBreach::Undeclared`] and is named.
pub const RAW_SITE_RESIDUE: &[(&str, usize)] = &[
    // KR-974's declaration-admission rig (`franken_lean-gii.23`), landed unprotected and
    // reddening every pane. Declared rather than converted for the reason this module's
    // AGENTS.md row already gives about its crate: `fln-checker` is one of the three that
    // cannot reach the checked macro without a NEW dependency edge, and its case also
    // touches the §8 allowlist. That is a graph decision belonging to the graph's owner,
    // not something to take while unblocking a red workspace. The row is the honest
    // holding position and it costs a slot that a conversion reclaims.
    ("crates/fln-checker/tests/admit.rs", 1),
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
    ("crates/fln-unsafe-abi/src/tests.rs", 1),
    ("crates/fln-unsafe-region/src/tests.rs", 1),
    ("crates/fln-verdict/src/checker.rs", 1),
    ("crates/fln-verdict/tests/input_validation.rs", 1),
    ("tribunal/epoch-lab/src/main.rs", 1),
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

/// The populations the k60n coverage disclosure in `AGENTS.md` names, re-derived from a
/// census instead of transcribed.
///
/// Every number in that row was prose until this type existed, and the row went stale by
/// the hand of the very commit that converted `tools/structure-guard`: it said "8 sites in
/// `tools/structure-guard`" while the tree carried 10, then 0. That is item 7's shape —
/// a claim and the population it counts, unjoined — sitting inside the section *about*
/// claims and the evidence they count.
///
/// The partition is exhaustive on purpose. A raw site under a path none of the disclosed
/// populations covers lands in [`Self::unclassified`], which the guard refuses: a
/// disclosure that silently drops a member reads as coverage it does not have, which is
/// `fln-bench-apparatus-empty-referent-bkw6`'s complaint about a scope measured differing
/// from the scope meant.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct CoveragePopulations {
    /// Invocations of the checked macros **outside** the defining module. The module's own
    /// occurrences are excluded because its two failure messages name
    /// `checked_workspace_root!()` as the repair, so counting them would let the guard's
    /// own advice satisfy a floor over real invocations — `fln-8zsq`'s lesson, and one this
    /// module already paid for once.
    pub checked_sites: usize,
    /// Distinct workspace members carrying those invocations.
    pub checked_members: usize,
    /// Raw sites still in `tools/structure-guard` — the population this commit converted,
    /// disclosed so that its return is a number moving rather than a silence.
    pub structure_guard_raw: usize,
    /// Raw sites in product crates under `crates/`, the defining module excluded.
    pub product_raw: usize,
    /// Distinct product crates carrying them — a count of *members*, never of files.
    pub product_members: usize,
    /// Raw sites in the nested `tribunal/epoch-lab` workspace.
    pub epoch_lab_raw: usize,
    /// Raw sites in the defining module itself: the two macro definitions and the two unit
    /// tests that feed the compile-time value in as known-good input.
    pub defining_module_raw: usize,
    /// Raw sites no disclosed population covers. Non-empty is a refusal, not a bucket.
    pub unclassified: std::collections::BTreeMap<String, usize>,
}

/// The workspace member a repository-relative path belongs to (`crates/fln-hash`,
/// `tools/structure-guard`, `tribunal/epoch-lab`), or `None` for a top-level file.
fn member_of(path: &str) -> Option<String> {
    let mut parts = path.split('/');
    let top = parts.next()?;
    let name = parts.next()?;
    (!name.is_empty() && parts.next().is_some()).then(|| format!("{top}/{name}"))
}

/// Partition a census into the populations the disclosure names.
///
/// Pure, so the interesting cases — an unclassified path, two files in one crate, a tools
/// path that must not be scored as a product crate — are reachable without a repository.
pub fn coverage_populations(
    census: &RootResolutionCensus,
    defining_module: &str,
) -> CoveragePopulations {
    let mut pops = CoveragePopulations::default();
    let mut product_members = std::collections::BTreeSet::new();
    for (path, &sites) in &census.raw_files {
        if path == defining_module {
            pops.defining_module_raw += sites;
        } else if path.starts_with("tools/structure-guard/") {
            pops.structure_guard_raw += sites;
        } else if path.starts_with("tribunal/epoch-lab/") {
            pops.epoch_lab_raw += sites;
        } else if let Some(member) = member_of(path).filter(|m| m.starts_with("crates/")) {
            pops.product_raw += sites;
            product_members.insert(member);
        } else {
            *pops.unclassified.entry(path.clone()).or_default() += sites;
        }
    }
    pops.product_members = product_members.len();

    let mut checked_members = std::collections::BTreeSet::new();
    for (path, &sites) in &census.checked_files {
        if path == defining_module {
            continue;
        }
        pops.checked_sites += sites;
        if let Some(member) = member_of(path) {
            checked_members.insert(member);
        }
    }
    pops.checked_members = checked_members.len();
    pops
}

/// A number a governed document declares, and the ways it can fail to bind to the tree.
///
/// There is deliberately no "close enough" outcome, and the three non-`Stale` variants
/// matter as much as `Stale`: a marker that has been reworded, doubled, or stripped of its
/// digits makes the comparison *vacuous*, and a vacuous comparison passes. `fln-8zsq`'s
/// first repair asserted a qualifier appeared somewhere in a file and a planted mutant
/// survived on a second copy of it; these three variants are that lesson turned into
/// values.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DisclosureBreach {
    /// The phrase that must carry the number is absent, so nothing was compared.
    Missing {
        /// The exact phrase looked for.
        marker: String,
    },
    /// The phrase occurs more than once, so which number binds is undecidable.
    Ambiguous {
        /// The exact phrase looked for.
        marker: String,
        /// How many times it occurs.
        occurrences: usize,
    },
    /// The phrase is present but no digits precede it.
    Unparsed {
        /// The exact phrase looked for.
        marker: String,
    },
    /// The document declares a number the tree contradicts, in the direction that binding
    /// forbids.
    Stale {
        /// The exact phrase looked for.
        marker: String,
        /// What the document says.
        declared: usize,
        /// What the tree measures.
        measured: usize,
    },
}

impl DisclosureBreach {
    /// The operator-facing refusal, naming the phrase, both numbers, and the repair.
    pub fn message(&self) -> String {
        match self {
            Self::Missing { marker } => format!(
                "the k60n coverage disclosure in AGENTS.md no longer contains the phrase \
                 `…{marker}`, so that number was compared against nothing. Restore the \
                 phrase with the measured count, or move the binding in \
                 crates/fln-conformance/src/tree_identity.rs to whatever wording replaced \
                 it. A reworded disclosure is a silent one. Bead \
                 fln-cross-tree-baked-root-k60n."
            ),
            Self::Ambiguous {
                marker,
                occurrences,
            } => format!(
                "the phrase `…{marker}` occurs {occurrences} times in the k60n coverage \
                 disclosure, so which number it binds is undecidable and no comparison was \
                 made. Say each count once. Bead fln-cross-tree-baked-root-k60n."
            ),
            Self::Unparsed { marker } => format!(
                "the phrase `…{marker}` in the k60n coverage disclosure is not preceded by \
                 digits, so there is no declared number to compare. Write the count \
                 immediately before the phrase. Bead fln-cross-tree-baked-root-k60n."
            ),
            Self::Stale {
                marker,
                declared,
                measured,
            } => format!(
                "the k60n coverage disclosure in AGENTS.md declares {declared} for \
                 `…{marker}` and the tree measures {measured}. Whichever moved, the other \
                 must move with it in the same commit: this is the row that tells readers \
                 how much of the workspace the tree check protects, and a stale one \
                 overstates or understates it silently. Bead \
                 fln-cross-tree-baked-root-k60n."
            ),
        }
    }
}

/// Read the number written immediately before `marker`, refusing every way that can fail.
/// The singular spelling of a `… sites …` marker, or `None` when the marker has no plural
/// noun to fold.
///
/// **Why this exists, since accommodating a check is usually the wrong move.** A population
/// that shrinks to exactly one forces a choice between ungrammatical prose in a
/// constitutional document — "1 unprotected sites" — and softening the number. Neither is
/// acceptable, and the number is the part that must not move: this folds only the NOUN, and
/// the count is still compared exactly. The alternative anyone reaches for first is to widen
/// the marker to a prefix like `" unprotected site"`, which silently starts matching
/// `" unprotected sites across"` as well and makes two bindings read the same clause.
fn singular_marker(marker: &str) -> Option<String> {
    marker
        .find("sites ")
        .map(|at| format!("{}site {}", &marker[..at], &marker[at + "sites ".len()..]))
}

/// Returns the declared count **and the marker actually matched**, which differ whenever the
/// singular fallback fires.
fn declared_before(text: &str, marker: &str) -> Result<(usize, String), DisclosureBreach> {
    let mut occurrences = text.matches(marker).count();
    let mut marker = marker.to_string();
    if occurrences == 0
        && let Some(singular) = singular_marker(&marker)
        && text.matches(singular.as_str()).count() == 1
    {
        occurrences = 1;
        marker = singular;
    }
    let marker = marker.as_str();
    if occurrences == 0 {
        return Err(DisclosureBreach::Missing {
            marker: marker.to_string(),
        });
    }
    if occurrences > 1 {
        return Err(DisclosureBreach::Ambiguous {
            marker: marker.to_string(),
            occurrences,
        });
    }
    let head = &text[..text.find(marker).expect("exactly one occurrence")];
    let mut digits: Vec<char> = head
        .chars()
        .rev()
        .take_while(|c| c.is_ascii_digit())
        .collect();
    digits.reverse();
    digits
        .iter()
        .collect::<String>()
        .parse()
        .map(|declared| (declared, marker.to_string()))
        .map_err(|_| DisclosureBreach::Unparsed {
            marker: marker.to_string(),
        })
}

/// Which way a disclosed number is allowed to move.
///
/// **The first version of this binding made every number `Exact`, and that was wrong in the
/// direction that taxes a repair.** Within one hour it reddened the workspace twice — once by
/// my own hand and once by a peer — for the *good* event: a rig being converted to
/// `checked_workspace_root!()`, which grows the protected count. `RAW_SITE_RESIDUE`'s own
/// docs already state the rule this violated: "reverse membership is a wall that reddens a
/// correct repair". So the populations divide by which direction is the defect.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    /// A measured population that must not move either way without the row moving: the
    /// **unprotected** counts. Silent growth is the defect this bead exists for, and silent
    /// shrinkage would let a repair go unrecorded.
    Exact,
    /// A **floor**. The protected counts may grow freely — that is the repair — and may not
    /// shrink. The cost is stated rather than hidden: a floor left un-raised understates
    /// coverage, so the number is a lower bound and the prose must say so.
    AtLeast,
}

/// Judge the k60n coverage disclosure against the populations it claims to describe.
///
/// The phrase for each number is the *whole* binding, which is why they are long and
/// specific: a marker of `" sites"` would match four places and bind none of them. Scope an
/// assertion to the site that must carry the evidence, never to the document.
pub fn disclosure_breaches(row: &str, pops: &CoveragePopulations) -> Vec<DisclosureBreach> {
    let bindings: [(&str, usize, Direction); 7] = [
        // Protected: growing these is the whole point of the bead.
        (
            " checked invocation sites",
            pops.checked_sites,
            Direction::AtLeast,
        ),
        (
            " crates outside the defining module",
            pops.checked_members,
            Direction::AtLeast,
        ),
        // Unprotected: these may not move in either direction unattended.
        (
            " raw sites in tools/structure-guard",
            pops.structure_guard_raw,
            Direction::Exact,
        ),
        (
            " unprotected sites across",
            pops.product_raw,
            Direction::Exact,
        ),
        (" product crates", pops.product_members, Direction::Exact),
        (
            " unprotected sites in tribunal/epoch-lab",
            pops.epoch_lab_raw,
            Direction::Exact,
        ),
        (
            " raw sites in the defining module",
            pops.defining_module_raw,
            Direction::Exact,
        ),
    ];
    bindings
        .iter()
        .filter_map(
            |(marker, measured, direction)| match declared_before(row, marker) {
                Err(breach) => Some(breach),
                Ok((declared, matched)) => {
                    let violated = match direction {
                        Direction::Exact => declared != *measured,
                        Direction::AtLeast => *measured < declared,
                    };
                    // `matched`, not `marker`: where the singular fallback fired, naming the
                    // plural would send the reader grepping for a clause that is not in the
                    // file. This repository's recorded cost of a refusal that names the wrong
                    // thing is three panes chasing three wrong causes.
                    violated.then_some(DisclosureBreach::Stale {
                        marker: matched,
                        declared,
                        measured: *measured,
                    })
                }
            },
        )
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

    /// The refusal must be SYMMETRIC, and the sibling above tests only one direction.
    ///
    /// **This is the direction that is not currently firing, which is why it needs a test
    /// rather than an argument.** Today the bake tree is the dirtier one, so a cross-tree
    /// artifact yields a loud false RED — a suite reporting a defect that is real about the
    /// other checkout. Swap which tree is dirty and the identical mechanism yields a false
    /// GREEN: a suite reporting *structurally clean* about a repository that is not the one
    /// under test. Nobody investigates a green, so that direction is strictly worse, and it
    /// is the one the observed instance at `5c5ada4b` did not happen to produce.
    ///
    /// Symmetry follows from `!=` being symmetric, and that is an argument, not a
    /// measurement. What it does not survive is a plausible future edit: any special case of
    /// the form "if the bake tree IS the canonical repository root, trust it" passes every
    /// other test in this module and opens the false green alone. Measured at `ee59d283`:
    /// `if compiled_in.starts_with("/data/projects/") { return None }` was planted in
    /// [`cross_tree_fault`] and killed by **this test alone** — all fourteen others, including
    /// `a_foreign_bake_tree_is_refused_and_the_message_names_both`, stayed green.
    #[test]
    fn the_refusal_is_symmetric_so_a_clean_bake_tree_is_refused_too() {
        const MAIN: &str = "/data/projects/fl/tools/g";
        const WORKTREE: &str = "/data/tmp/wt-cc_2/tools/g";

        // Direction B: compiled in the MAIN tree, invoked from the worktree. The bake tree is
        // the clean one, so an unprotected site here would report main's verdict as the
        // worktree's — clean about a repository nobody tested.
        let fault = cross_tree_fault(MAIN, Some(WORKTREE)).expect("the swap is still a fault");
        assert_eq!(
            fault,
            CrossTreeFault::Mismatch {
                compiled_in: MAIN.to_string(),
                invoked_from: WORKTREE.to_string(),
            },
            "the fields must follow the swap rather than being normalised into one order — a \
             message that always names the worktree as `compiled_in` is wrong half the time"
        );
        let message = fault.message();
        assert!(message.contains(MAIN), "{message}");
        assert!(message.contains(WORKTREE), "{message}");
        assert!(
            message.contains("COMPILED FOR A DIFFERENT CHECKOUT"),
            "the headline may not weaken in the direction nobody investigates: {message}"
        );

        // And the pair is genuinely a swap, not two spellings of one case.
        let forward = cross_tree_fault(WORKTREE, Some(MAIN)).expect("the sibling case");
        assert_ne!(
            fault, forward,
            "if both orders produced the same value the mechanism would be normalising, and \
             the message could not name which checkout compiled the binary"
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

    /// Every tracked Rust source in the tree this run was **launched from**, paired with
    /// its contents, plus that tree's root.
    ///
    /// The scope is derived from `git ls-files`, never listed: a hand-written root list
    /// rots, and this repository has already paid for that twice
    /// (`franken_lean-ext-observable-fixture-drift-gap-vqnu`'s twelve evidence roots, and
    /// `bkw6`'s twelve throwaway fixture manifests under `scripts/e2e/artifacts/`, which a
    /// filesystem walk picks up and a tracked-file scan does not). A failed `git` call is a
    /// refusal, because an unknown scope supports no coverage claim at all.
    fn tracked_sources() -> (PathBuf, Vec<(String, String)>) {
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
        let sources = paths
            .lines()
            .filter_map(|path| {
                std::fs::read_to_string(root.join(path))
                    .ok()
                    .map(|text| (path.to_string(), text))
            })
            .collect();
        (root, sources)
    }

    /// The floor on tracked sources read. A scan that reads almost nothing is a broken
    /// scan, not a clean tree, so both live guards assert it rather than trusting the walk.
    const FILES_FLOOR: usize = 200;

    /// The coverage claim, re-derived every run and judged **per file**.
    ///
    /// Three assertions, each with a direction chosen deliberately and stated in
    /// [`RAW_SITE_RESIDUE`]: the unprotected population may shrink freely and may not grow
    /// *in any file*; the protected population may grow freely and may not shrink; and a
    /// scan that reads almost nothing refuses rather than reporting a clean tree.
    ///
    /// **The checked floor excludes this file, and the raw ceiling does not.** The
    /// asymmetry is not convenience, it is the direction of each error. Raw sites are
    /// bounded from *above*, so counting this module's own occurrences is conservative and
    /// a regression added here is still seen. Checked invocations are floored from
    /// *below*, so this module's prose — the two failure messages naming
    /// `checked_workspace_root!()` as the repair — would *inflate* the floor and let real
    /// invocations disappear behind the guard's own advice. That is `fln-8zsq`'s lesson
    /// exactly: the guard's own text is inside its search space, and the fix is to scope
    /// the assertion to the site that must carry the evidence. Measured at `4e197f02` plus
    /// this change: 49 raw matches of the checked needles, of which **10 are in this file
    /// and 39 are invocations elsewhere** — 29 in `fln-conformance`'s other sources and 10
    /// in `tools/structure-guard`, which this change converted. The exclusion is derived
    /// from [`file!`] rather than written down, and the derivation refuses if it fails to
    /// resolve.
    #[test]
    fn the_tree_check_coverage_claim_matches_the_measured_workspace() {
        const CHECKED_FLOOR: usize = 39;

        let (_root, sources) = tracked_sources();
        let measured = census(sources.iter().map(|(p, t)| (p.as_str(), t.as_str())));

        // --- THE DECOY, before any count below is believed --------------------------------
        // An empty scan must be a failure, not a clean tree. A planted occurrence built from
        // MANIFEST_DIR_VAR — not from the needle's own fragments — must be found on every
        // run, so a needle that has stopped matching says so here instead of reporting a
        // confident zero through every judgement in this test.
        const DECOY_PATH: &str = "<planted>/needle_liveness.rs";
        let decoy = needle_decoy();
        let liveness = census([(DECOY_PATH, decoy.as_str())]);
        assert_eq!(
            liveness.raw_files.get(DECOY_PATH),
            Some(&1),
            "the census did not find its own planted decoy, so the compile-time needle has \
             stopped matching. Every count in this guard would then be a confident ZERO and \
             the residue would be judged clean against an empty population — the exact shape \
             fln-8zsq, franken_lean-2ki4 and the mandated-mutants lane each produced. Decoy \
             text: {decoy:?}"
        );

        // --- the independent, coarser signal, reconciled PER FILE -------------------------
        // The decoy proves the matcher is alive; it cannot prove production code still spells
        // the form the matcher looks for. Every precise match contains the bare variable
        // name, so equality is the invariant outside the files that discuss the needle, and a
        // file that mentions it more often than the needle matches is named rather than
        // silently dropped from the population.
        let drifts = needle_drifts(
            sources.iter().map(|(p, t)| (p.as_str(), t.as_str())),
            DECLARED_NEEDLE_DIVERGENCE,
        );
        assert!(
            drifts.is_empty(),
            "{}",
            drifts
                .iter()
                .map(NeedleDrift::message)
                .collect::<Vec<_>>()
                .join("\n\n")
        );
        // And the reconciliation must have had something to reconcile. If the region were
        // empty — every file excluded, or the coarse matcher broken too — the equality above
        // holds vacuously over zero files.
        let carrying = sources
            .iter()
            .filter(|(_, text)| text.contains(MANIFEST_DIR_VAR))
            .count();
        assert!(
            carrying >= 15,
            "only {carrying} tracked sources mention the manifest-dir variable at all, so the \
             per-file reconciliation ran over almost nothing and proves nothing. A scan that \
             reads almost nothing is a broken scan, not a clean tree"
        );

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

    /// The decoy is found, and it is spelled INDEPENDENTLY of the needle it validates.
    ///
    /// The second half is the one that matters. A decoy assembled from the same fragments as
    /// the needle moves with it: break the needle and the decoy breaks identically, so the
    /// liveness check passes on a matcher that matches nothing — the vacuity trap re-entered
    /// inside the fix for it. Here the decoy derives from [`MANIFEST_DIR_VAR`], so the two can
    /// only move together when the variable itself changes.
    #[test]
    fn the_planted_decoy_is_found_and_does_not_share_the_needles_spelling() {
        let decoy = needle_decoy();
        let found = census([("decoy.rs", decoy.as_str())]);
        assert_eq!(
            found.raw_sites, 1,
            "the decoy must match the census needle: {decoy:?}"
        );

        // Independence, asserted rather than argued: the decoy is reproducible from the
        // authoritative variable name alone, with no reference to the needle's fragments.
        assert_eq!(
            decoy,
            format!("fn decoy() -> &'static str {{ env!(\"{MANIFEST_DIR_VAR}\") }}"),
            "the decoy must be derivable from MANIFEST_DIR_VAR alone; if it is ever built from \
             the needle's own fragments it stops being able to detect a broken needle"
        );
    }

    /// A production file that adopts a spelling the needle misses is NAMED, not dropped.
    ///
    /// This is the failure a decoy cannot see: the matcher is alive, and the population it
    /// measures has quietly shrunk. `env! ("CARGO_MANIFEST_DIR")` with a space is a real
    /// rustfmt-stable spelling and the census counts it as zero.
    #[test]
    fn a_spelling_the_needle_misses_is_refused_with_both_counts() {
        let drifted = "fn r() { Path::new(env! (\"CARGO_MANIFEST_DIR\")).join(\"..\") }";
        assert_eq!(
            census([("a.rs", drifted)]).raw_sites,
            0,
            "premise: the needle misses it"
        );
        assert_eq!(
            needle_drifts([("a.rs", drifted)], &[]),
            vec![NeedleDrift::Spelling {
                path: "a.rs".to_string(),
                coarse: 1,
                precise: 0,
            }],
            "an unprotected site the census cannot see must be named"
        );
    }

    /// A broken needle is caught by the reconciliation across the whole population, not only
    /// by the decoy — the two failures are independent and both are live.
    #[test]
    fn a_needle_matching_nothing_makes_every_real_file_drift() {
        let real = "fn r() { Path::new(env!(\"CARGO_MANIFEST_DIR\")).join(\"..\") }";
        // The population as it really is: coarse and precise agree.
        assert!(needle_drifts([("a.rs", real)], &[]).is_empty());
        // Now the same file judged as if the needle no longer matched it. `needle_drifts`
        // takes the text, so the equivalent of a dead needle is a file whose precise form is
        // absent while the variable is still named — which is the drift above, per file. Over
        // a real population that is one refusal per file rather than a silent zero.
        let dead = real.replace("env!(", "env_broken!(");
        assert_eq!(needle_drifts([("a.rs", dead.as_str())], &[]).len(), 1);
    }

    /// A declared divergence that no longer diverges is refused as stale.
    ///
    /// Same direction as deleting a repaired residue row: left standing, the declaration
    /// would excuse a real drift in that file forever.
    #[test]
    fn a_declared_divergence_that_no_longer_diverges_is_refused() {
        let agreeing = "fn r() { env!(\"CARGO_MANIFEST_DIR\") }";
        assert_eq!(
            needle_drifts([("a.rs", agreeing)], &[("a.rs", "reason")]),
            vec![NeedleDrift::StaleDivergence {
                path: "a.rs".to_string()
            }]
        );
        // And a genuine divergence under the same declaration is clean.
        let diverging =
            "const V: &str = \"CARGO_MANIFEST_DIR\"; fn r() { env!(\"CARGO_MANIFEST_DIR\") }";
        assert!(needle_drifts([("a.rs", diverging)], &[("a.rs", "reason")]).is_empty());
    }

    /// Two matchers that disagree in the impossible direction refuse rather than being
    /// reconciled. The precise form contains the bare name, so `precise > coarse` means the
    /// matchers are inconsistent and no count downstream means anything.
    #[test]
    fn an_impossible_matcher_pair_is_refused_rather_than_explained() {
        // Reachable only by construction, which is the point of the function being pure.
        let text = "env!(\"CARGO_MANIFEST_DIR\")";
        let drifts = needle_drifts([("a.rs", text)], &[]);
        assert!(drifts.is_empty(), "the honest pair is 1 and 1: {drifts:?}");
        assert!(
            NeedleDrift::Impossible {
                path: "a.rs".to_string(),
                coarse: 0,
                precise: 1,
            }
            .message()
            .contains("impossible"),
            "the refusal must say the matchers are inconsistent"
        );
    }

    /// A row carrying every disclosed number in the exact wording the bindings look for.
    ///
    /// Built from a [`CoveragePopulations`] so the synthetic cases below vary **one** thing
    /// — the row's text or one population — and never both at once.
    fn sample_row(pops: &CoveragePopulations) -> String {
        format!(
            "| `fln-cross-tree-baked-root-k60n` | prose … {checked} checked invocation \
             sites in {members} crates outside the defining module; {guard} raw sites in \
             tools/structure-guard; {product} unprotected sites across {crates} product \
             crates; {epoch} unprotected sites in tribunal/epoch-lab; {own} raw sites in \
             the defining module itself. more prose … |",
            checked = pops.checked_sites,
            members = pops.checked_members,
            guard = pops.structure_guard_raw,
            product = pops.product_raw,
            crates = pops.product_members,
            epoch = pops.epoch_lab_raw,
            own = pops.defining_module_raw,
        )
    }

    fn sample_populations() -> CoveragePopulations {
        CoveragePopulations {
            checked_sites: 39,
            checked_members: 2,
            structure_guard_raw: 0,
            product_raw: 19,
            product_members: 9,
            epoch_lab_raw: 11,
            defining_module_raw: 4,
            unclassified: std::collections::BTreeMap::new(),
        }
    }

    /// A row that agrees with the tree is clean. Without this the five refusal tests below
    /// would be satisfied by a binding that refuses everything.
    #[test]
    fn a_disclosure_that_matches_the_tree_is_clean() {
        let pops = sample_populations();
        assert_eq!(disclosure_breaches(&sample_row(&pops), &pops), vec![]);
    }

    /// A floor accepts growth and refuses shrinkage; an exact binding refuses both.
    ///
    /// **This is the test whose absence cost two reds in one hour.** The first version of
    /// `disclosure_breaches` compared every number with `!=`, so converting one rig — the
    /// repair this whole bead exists to encourage — moved `checked_sites` up and reddened the
    /// workspace for every pane until AGENTS.md was edited. A guard that taxes the correct
    /// direction gets worked around, which is the `franken_lean-e5k7` shape.
    #[test]
    fn a_floor_accepts_growth_and_refuses_shrinkage_while_exact_refuses_both() {
        let declared = sample_populations();
        let row = sample_row(&declared);

        // Protected count GREW: a repair. Must be clean.
        let mut grown = declared.clone();
        grown.checked_sites = declared.checked_sites + 7;
        grown.checked_members = declared.checked_members + 1;
        assert_eq!(
            disclosure_breaches(&row, &grown),
            vec![],
            "growing the protected population is a repair and must not redden the tree"
        );

        // Protected count SHRANK: protection was removed. Must refuse.
        let mut shrunk = declared.clone();
        shrunk.checked_sites = declared.checked_sites - 1;
        assert_eq!(
            disclosure_breaches(&row, &shrunk),
            vec![DisclosureBreach::Stale {
                marker: " checked invocation sites".to_string(),
                declared: declared.checked_sites,
                measured: declared.checked_sites - 1,
            }],
            "losing protection must refuse: the floor is the whole point of it being a floor"
        );

        // Unprotected count SHRANK: a repair too, but it must still be recorded, because the
        // disclosure is of a measured population and a stale low number understates the debt.
        let mut repaired = declared.clone();
        repaired.product_raw = declared.product_raw - 1;
        assert_eq!(
            disclosure_breaches(&row, &repaired).len(),
            1,
            "an unprotected count is exact in BOTH directions, so even a repair moves the row"
        );
    }

    /// One number moved in the tree and not in the row: refused, with **both** values.
    ///
    /// Both are load-bearing. A refusal that named only the measured count would leave the
    /// reader unable to tell a stale disclosure from a regression in the tree, which is the
    /// whole complaint against the aggregate ceiling this module already replaced once.
    #[test]
    fn a_stale_disclosed_number_is_refused_with_both_values() {
        let declared = sample_populations();
        let row = sample_row(&declared);
        let mut measured = declared.clone();
        measured.product_raw = 20;

        assert_eq!(
            disclosure_breaches(&row, &measured),
            vec![DisclosureBreach::Stale {
                marker: " unprotected sites across".to_string(),
                declared: 19,
                measured: 20,
            }],
            "exactly the moved number must refuse, and only it"
        );
        let message = disclosure_breaches(&row, &measured)[0].message();
        assert!(message.contains("19"), "{message}");
        assert!(message.contains("20"), "{message}");
        assert!(
            message.contains("fln-cross-tree-baked-root-k60n"),
            "{message}"
        );
    }

    /// The two vacuity shapes, and they are the reason this is a typed breach rather than a
    /// `bool`.
    ///
    /// Rewording a phrase makes the comparison silently disappear; saying a count twice
    /// makes it undecidable. Either way a naive "does the row contain the measured number"
    /// check passes while binding nothing — `fln-8zsq`'s planted mutant survived on exactly
    /// that, a second copy of the qualifier elsewhere in the same file.
    #[test]
    fn a_reworded_or_doubled_marker_is_refused_rather_than_passing_vacuously() {
        let pops = sample_populations();

        let reworded = sample_row(&pops).replace("9 product crates", "9 product packages");
        assert_eq!(
            disclosure_breaches(&reworded, &pops),
            vec![DisclosureBreach::Missing {
                marker: " product crates".to_string(),
            }],
            "a reworded disclosure must refuse, not silently stop being checked"
        );

        let doubled = format!("{} and again 7 product crates", sample_row(&pops));
        assert_eq!(
            disclosure_breaches(&doubled, &pops),
            vec![DisclosureBreach::Ambiguous {
                marker: " product crates".to_string(),
                occurrences: 2,
            }],
            "two counts for one population is undecidable, and the first must not win"
        );
    }

    /// The phrase is present and the number is not. Refusing here is what stops a row from
    /// reading as disclosed while carrying no figure at all.
    #[test]
    fn a_marker_with_no_digits_before_it_is_refused() {
        let pops = sample_populations();
        let stripped =
            sample_row(&pops).replace("11 unprotected sites in", "several unprotected sites in");
        assert_eq!(
            disclosure_breaches(&stripped, &pops),
            vec![DisclosureBreach::Unparsed {
                marker: " unprotected sites in tribunal/epoch-lab".to_string(),
            }]
        );
    }

    /// A population that shrinks to exactly one may be disclosed in the **singular**, and the
    /// count stays exact.
    ///
    /// Driven by injected input rather than by the live row, because the live row carries a
    /// singular clause only while `tribunal/epoch-lab` sits at 1 — the moment it reaches 0 or
    /// returns to 2 this path stops being exercised by the tree and becomes decorative, which
    /// is precisely how a refusal survives a mutation campaign while doing nothing.
    #[test]
    fn a_population_of_one_may_be_disclosed_in_the_singular() {
        let mut pops = sample_populations();
        pops.epoch_lab_raw = 1;
        let row = sample_row(&pops).replace(
            "1 unprotected sites in tribunal/epoch-lab",
            "1 unprotected site in tribunal/epoch-lab",
        );
        assert!(
            row.contains("1 unprotected site in tribunal/epoch-lab"),
            "the plant did not apply"
        );
        assert_eq!(
            disclosure_breaches(&row, &pops),
            vec![],
            "a grammatical singular disclosure must be accepted"
        );
    }

    /// Folding the noun must not fold the **number**: a singular clause carrying the wrong
    /// count still fails. Without this cell the accommodation above would be indistinguishable
    /// from softening the check to go green.
    #[test]
    fn a_singular_disclosure_with_the_wrong_count_still_fails() {
        let mut pops = sample_populations();
        pops.epoch_lab_raw = 1;
        let row = sample_row(&pops).replace(
            "1 unprotected sites in tribunal/epoch-lab",
            "7 unprotected site in tribunal/epoch-lab",
        );
        assert_eq!(
            disclosure_breaches(&row, &pops),
            vec![DisclosureBreach::Stale {
                marker: " unprotected site in tribunal/epoch-lab".to_string(),
                declared: 7,
                measured: 1,
            }],
            "the singular fallback must report the SINGULAR marker it actually matched, or the \
             refusal sends the reader looking for a clause that is not in the file"
        );
    }

    /// The fallback folds only a marker whose plural noun is followed by a word, so it can
    /// never turn `" unprotected sites in tribunal/epoch-lab"` into a prefix that also matches
    /// `" unprotected sites across"` — two bindings reading one clause would make the census
    /// agree with itself while measuring the wrong population.
    #[test]
    fn the_singular_fold_cannot_collide_two_bindings() {
        assert_eq!(
            singular_marker(" unprotected sites in tribunal/epoch-lab").as_deref(),
            Some(" unprotected site in tribunal/epoch-lab")
        );
        // My first version of this cell asserted None here and was WRONG: the fold applies
        // to any marker with a plural noun followed by a word, so this yields
        // `" unprotected site across"`. That is harmless and the reason is the guard, not the
        // fold - the fallback fires ONLY when the plural has zero occurrences, so a live
        // plural clause is never displaced. What must hold is that no folded marker collides
        // with another binding's, in either direction.
        assert_eq!(
            singular_marker(" unprotected sites across").as_deref(),
            Some(" unprotected site across")
        );
        assert_eq!(
            singular_marker(" product crates"),
            None,
            "no trailing word to fold"
        );
        let folded = [
            singular_marker(" unprotected sites in tribunal/epoch-lab").unwrap(),
            singular_marker(" unprotected sites across").unwrap(),
        ];
        assert!(
            !folded[0].starts_with(&folded[1]) && !folded[1].starts_with(&folded[0]),
            "a folded marker that prefixes another binding's would make two bindings read one \
             clause and agree while measuring different populations: {folded:?}"
        );
    }

    /// The partition counts **members**, not files, and a tools path is never a product
    /// crate.
    ///
    /// Both directions have bitten this bead already. Counting files would have reported
    /// nine product crates as thirteen; folding `tools/` into `crates/` would have reported
    /// the converted population as still unprotected and the product one as inflated, so the
    /// row could go stale in two places while its total stayed put — a single aggregate's
    /// exact failure mode, one level up.
    #[test]
    fn the_partition_separates_tools_from_product_crates_and_counts_members_not_files() {
        let raw = "env!(\"CARGO_MANIFEST_DIR\")";
        let measured = census([
            ("crates/fln-hash/src/blake3.rs", raw),
            ("crates/fln-hash/tests/schema_registry.rs", raw),
            ("crates/fln-rt/tests/region_engine.rs", raw),
            ("tools/structure-guard/tests/real_workspace.rs", raw),
            ("tribunal/epoch-lab/src/main.rs", raw),
        ]);
        let pops = coverage_populations(&measured, "crates/fln-conformance/src/tree_identity.rs");

        assert_eq!(pops.product_raw, 3, "three files carry product sites");
        assert_eq!(
            pops.product_members, 2,
            "but they live in two crates — a file count would say three"
        );
        assert_eq!(
            pops.structure_guard_raw, 1,
            "a tools/ path is its own population, never a product crate"
        );
        assert_eq!(pops.epoch_lab_raw, 1);
        assert!(pops.unclassified.is_empty());
    }

    /// A raw site in a directory no population covers is **named**, not dropped.
    ///
    /// This is the `bkw6` shape guarded directly: the disclosure would otherwise stay
    /// arithmetically consistent while describing a smaller workspace than the one that
    /// exists, and every number in it would still be true.
    #[test]
    fn a_raw_site_no_population_covers_is_unclassified_rather_than_dropped() {
        let measured = census([
            ("scripts/tribunal/rig.rs", "env!(\"CARGO_MANIFEST_DIR\")"),
            ("build.rs", "env!(\"CARGO_MANIFEST_DIR\")"),
        ]);
        let pops = coverage_populations(&measured, "crates/fln-conformance/src/tree_identity.rs");

        assert_eq!(pops.product_raw, 0);
        assert_eq!(pops.epoch_lab_raw, 0, "scripts/tribunal is not tribunal/");
        assert_eq!(
            pops.unclassified
                .keys()
                .map(String::as_str)
                .collect::<Vec<_>>(),
            vec!["build.rs", "scripts/tribunal/rig.rs"],
            "both must be named so the disclosure and the partition move together"
        );
    }

    /// The defining module is counted in its **own** population and excluded from the
    /// checked one.
    ///
    /// That asymmetry is the same one the coverage test carries, for the same reason: this
    /// module's two failure messages name `checked_workspace_root!()` as the repair, so
    /// including them would let the guard's own advice inflate a figure the row publishes as
    /// real invocations. Trap already paid for once in `fln-8zsq`.
    #[test]
    fn the_defining_module_is_excluded_from_the_checked_population_and_counted_in_its_own() {
        const DEFINING: &str = "crates/fln-conformance/src/tree_identity.rs";
        let measured = census([
            (
                DEFINING,
                "env!(\"CARGO_MANIFEST_DIR\") checked_workspace_root!() checked_manifest_dir!()",
            ),
            (
                "tools/structure-guard/tests/real_workspace.rs",
                "checked_workspace_root!()",
            ),
        ]);
        let pops = coverage_populations(&measured, DEFINING);

        assert_eq!(
            pops.defining_module_raw, 1,
            "the module's own raw site is disclosed, not exempted"
        );
        assert_eq!(
            pops.product_raw, 0,
            "and it is not double-counted as a product crate"
        );
        assert_eq!(
            pops.checked_sites, 1,
            "only the invocation outside the defining module counts toward the published \
             figure — its own two occurrences are prose as far as this number is concerned"
        );
        assert_eq!(pops.checked_members, 1);
    }

    /// The disclosed coverage in `AGENTS.md` must equal the tree it describes, in **both**
    /// directions.
    ///
    /// **This row went stale by the hand of the commit that repaired the population it
    /// counts.** It said "8 sites in `tools/structure-guard`" while `2a96e7b9` had already
    /// taken that file from 7 raw sites to 9, and the conversion then took it to 0 — a claim
    /// and the population it counts, unjoined, inside the AGENTS.md section that exists to
    /// name exactly that defect. Nothing would have said so; the number is prose in a table
    /// cell and no reader recomputes it.
    ///
    /// Two properties are deliberate. The numbers are re-derived from `git ls-files` on
    /// every run, so the row fails when the *tree* moves and equally when the *row* moves —
    /// one-way would let a repair silently overstate coverage. And the row must be found
    /// exactly once: a scan that locates no row is a broken scan, not a clean tree, and
    /// would otherwise judge the disclosure against an empty string and pass.
    #[test]
    fn the_k60n_coverage_disclosure_matches_the_measured_populations() {
        const ROW_PREFIX: &str = "| `fln-cross-tree-baked-root-k60n` |";

        let (root, sources) = tracked_sources();
        let measured = census(sources.iter().map(|(p, t)| (p.as_str(), t.as_str())));
        assert!(
            measured.files >= FILES_FLOOR,
            "the census read {} tracked source files, below the floor of {FILES_FLOOR}: a \
             broken scan cannot judge a disclosure",
            measured.files
        );

        let defining: Vec<&String> = measured
            .raw_files
            .keys()
            .filter(|path| path.ends_with(file!()))
            .collect();
        assert_eq!(
            defining.len(),
            1,
            "the defining module must be identifiable by {:?} and still carry the \
             compile-time form; zero means the needle has stopped matching and every \
             population below is a confident zero. Found: {defining:?}",
            file!()
        );
        let defining = defining[0].clone();

        let agents = std::fs::read_to_string(root.join("AGENTS.md"))
            .expect("AGENTS.md must be readable: it carries the claim under test");
        let rows: Vec<&str> = agents
            .lines()
            .filter(|line| line.trim_start().starts_with(ROW_PREFIX))
            .collect();
        assert_eq!(
            rows.len(),
            1,
            "AGENTS.md must carry exactly one item-7 row beginning {ROW_PREFIX:?}, and it \
             carries {}. Zero is a broken scan rather than a clean tree — the disclosure \
             would then be judged against nothing and pass",
            rows.len()
        );

        let pops = coverage_populations(&measured, &defining);
        assert!(
            pops.unclassified.is_empty(),
            "these raw sites belong to no population the k60n row discloses, so the row is \
             silent about them while every number in it stays true: {:?}. Extend the \
             disclosure and the partition in the same commit",
            pops.unclassified
        );

        let breaches = disclosure_breaches(rows[0], &pops);
        assert!(
            breaches.is_empty(),
            "{}",
            breaches
                .iter()
                .map(DisclosureBreach::message)
                .collect::<Vec<_>>()
                .join("\n\n")
        );
    }
}
