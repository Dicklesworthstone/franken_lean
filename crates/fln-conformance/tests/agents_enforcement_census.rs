//! AGENTS.md's enforcement-claim census, bound to the file it describes
//! (bead `franken_lean-pfei`, R1).
//!
//! # Why a census of a documentation file is a per-commit gate
//!
//! Four enforcement claims in AGENTS.md were measured **false** in two days, each found by a
//! person reading rather than by a check, and two of the four cost a lane. AGENTS.md is read by
//! every agent at session start, so a false enforcement claim propagates to six panes before
//! anybody measures it. R1 asks for the population to be *derived* and for the number to fail
//! when it moves in **either** direction.
//!
//! # The exclusion that inverted the answer, and why it fails closed
//!
//! Item 7's table is a catalogue of past defects. Its rows quote every phrase the scan searches
//! for, because quoting them is what the rows are *for*. The first version of this census
//! declared that exclusion in a `META_HEADINGS` constant and **never applied it** — the constant
//! appeared exactly once in the file, at its own definition.
//!
//! That was not cosmetic. Measured across three commits (`94902fb7`, `4e197f02`, `7d7fe137`) the
//! reported figure moved 26 → 27 → 28, and was re-anchored each time across three handoffs as
//! evidence that "a count of claims is itself a claim". Every one of those movements was a
//! catalogue row. The live population never moved from 22. A gate bound to the unfiltered figure
//! would have reddened on precisely the commits that record good work — item 7 being the section
//! this repository edits most often — and would have been ignored within a week.
//!
//! So the scan **refuses** when it cannot locate the catalogue region, and **refuses** when the
//! region excludes nothing. Both are failures rather than a silently wider scan, because a
//! census that has lost its scope looks exactly like a clean file.
//!
//! # What this does not earn
//!
//! `bound` means a producer is **named in the same sentence**, never that the producer exists,
//! runs, or enforces what the sentence says. A claim citing a deleted test still counts as
//! bound. Making the producer *denote* is pfei R2 and is not built.

#![forbid(unsafe_code)]

use std::path::PathBuf;
use std::process::Command;

const CENSUS: &str = "scripts/agents_enforcement_census.py";

fn workspace_root() -> PathBuf {
    // Through the tree check, not this file's compile-time manifest dir: a binary compiled in
    // another checkout would otherwise census that tree's AGENTS.md and report the verdict here
    // (bead `fln-cross-tree-baked-root-k60n`).
    fln_conformance::checked_workspace_root!()
        .canonicalize()
        .expect("real repository root")
}

/// Run the census, returning (exit code, stdout+stderr).
fn run(agents: Option<&PathBuf>) -> (i32, String) {
    let root = workspace_root();
    let mut command = Command::new("python3");
    command.arg("-I").arg("-S").arg("-B").arg(root.join(CENSUS));
    command.arg("--check");
    if let Some(path) = agents {
        command.arg("--agents").arg(path);
    } else {
        command.arg("--agents").arg(root.join("AGENTS.md"));
    }
    let out = command
        .current_dir(&root)
        .output()
        .unwrap_or_else(|err| panic!("{CENSUS} must be runnable: {err}"));
    let mut text = String::from_utf8_lossy(&out.stdout).into_owned();
    text.push_str(&String::from_utf8_lossy(&out.stderr));
    // A signal-killed run has no code; treat it as a failure that is not one of the census's
    // own typed exits, so it can never be mistaken for either a pass or a planted red.
    (out.status.code().unwrap_or(-1), text)
}

fn doctored(edit: impl Fn(String) -> String) -> (tempdir::Guard, PathBuf) {
    let root = workspace_root();
    let text = std::fs::read_to_string(root.join("AGENTS.md")).expect("AGENTS.md is readable");
    let guard = tempdir::Guard::new();
    let path = guard.path().join("AGENTS.md");
    std::fs::write(&path, edit(text)).expect("doctored copy is writable");
    (guard, path)
}

/// A scratch directory that removes only what this test created.
mod tempdir {
    use std::path::{Path, PathBuf};
    use std::sync::atomic::{AtomicUsize, Ordering};

    pub struct Guard(PathBuf);

    impl Guard {
        pub fn new() -> Self {
            static COUNTER: AtomicUsize = AtomicUsize::new(0);
            let unique = format!(
                "fln-enforcement-census-{}-{}",
                std::process::id(),
                COUNTER.fetch_add(1, Ordering::Relaxed)
            );
            let dir = std::env::temp_dir().join(unique);
            std::fs::create_dir_all(&dir).expect("scratch directory");
            Self(dir)
        }

        pub fn path(&self) -> &Path {
            &self.0
        }
    }

    impl Drop for Guard {
        fn drop(&mut self) {
            // Only ever the single AGENTS.md copy this guard wrote, then the directory.
            let _ = std::fs::remove_file(self.0.join("AGENTS.md"));
            let _ = std::fs::remove_dir(&self.0);
        }
    }
}

#[test]
fn the_agents_enforcement_census_matches_the_file_it_describes() {
    let (code, output) = run(None);
    assert_eq!(
        code, 0,
        "AGENTS.md's enforcement-census disclosure disagrees with the derivation, or the scan \
         lost its scope.\n\n{output}\n\nRe-derive with `python3 -I -S -B {CENSUS}` and update the \
         `enforcement-census:` line in AGENTS.md. Do NOT soften enforcement sentences to make \
         this pass — that is pfei R5, the cheapest way to go green and the one that destroys \
         the reason anyone reads the file."
    );
    assert!(
        output.contains("enforcement-census: OK"),
        "the census must report its own numbers on success, so a reader of a passing run can \
         see what was counted rather than inferring it from an exit code:\n{output}"
    );
}

/// The comparison is real, not a constant agreeing with itself.
///
/// Without this, a census that always returned the disclosed numbers — or one whose `--check`
/// silently short-circuited — would pass identically.
#[test]
fn a_disclosure_that_disagrees_with_the_derivation_is_refused() {
    let (_guard, path) = doctored(|text| {
        assert!(
            text.contains("live=22"),
            "this control doctors the live count; if the real disclosure has moved off 22, \
             update the needle rather than deleting the control"
        );
        text.replace("live=22", "live=99")
    });
    let (code, output) = run(Some(&path));
    assert_eq!(code, 1, "a doctored disclosure must be refused:\n{output}");
    assert!(
        output.contains("stated 99") && output.contains("derived 22"),
        "the refusal must name BOTH numbers, so the reader learns which way it moved rather \
         than only that something is wrong:\n{output}"
    );
}

/// The decoy: a new live claim must be SEEN (pfei R4).
///
/// The three other controls all pass against a scan that returned a hard-coded 22 no matter
/// what the file said — two of them doctor the disclosure or the region rather than the
/// population. This one moves the population itself and requires the derived number to follow,
/// which is what separates a census from a constant.
///
/// The decoy is planted **outside** the catalogue region deliberately: planted inside it, the
/// count must NOT move, and that is the distinction this whole binding turns on.
#[test]
fn a_planted_live_claim_moves_the_derived_population() {
    let decoy = "\nA planted decoy for the census control: CI refuses every unbound decoy.\n";
    let (_guard, path) = doctored(|text| text + decoy);
    let (code, output) = run(Some(&path));
    assert_eq!(
        code, 1,
        "a planted live claim must move the count:\n{output}"
    );
    assert!(
        output.contains("live: stated 22, derived 23"),
        "the decoy must be counted as one new LIVE claim — if the derived number did not move, \
         the scan is not reading the file it claims to census:\n{output}"
    );
    assert!(
        output.contains("unbound: stated 12, derived 13"),
        "the decoy names no producer, so it must land in the UNBOUND half; a scan that counted \
         it as bound would be finding producers that are not there:\n{output}"
    );
}

/// The same decoy inside the catalogue region must NOT move the live count.
///
/// This is the property the whole repair rests on, asserted rather than assumed: it is why the
/// figure drifted 26 → 27 → 28 while nothing about enforcement changed.
#[test]
fn a_claim_planted_inside_the_catalogue_does_not_move_the_live_population() {
    let anchor = "   A twelfth is already filed and deliberately unmechanised:";
    let (_guard, path) = doctored(|text| {
        assert!(
            text.contains(anchor),
            "this control plants inside item 7's section; if that anchor moved, re-point it \
             rather than deleting the control"
        );
        text.replace(
            anchor,
            "   A planted decoy inside the catalogue: CI refuses every catalogued decoy.\n\n\
             \x20  A twelfth is already filed and deliberately unmechanised:",
        )
    });
    let (code, output) = run(Some(&path));
    assert_eq!(
        code, 1,
        "the catalogued count must still move, or the plant landed outside the region and this \
         control proves nothing:\n{output}"
    );
    assert!(
        output.contains("catalogued: stated 7, derived 8") && !output.contains("live:"),
        "a claim inside item 7's catalogue must move ONLY the catalogued count. If `live` moved \
         too, the region is not being excluded and the census has regressed to the figure that \
         drifted 26 -> 27 -> 28 while enforcement never changed:\n{output}"
    );
}

/// Losing the catalogue region is a FAILURE, never a wider scan.
///
/// This is the mutant that matters. With the heading gone the scan still finds plenty of
/// claims — it simply counts item 7's catalogue of past defects among them, which is exactly
/// the state that produced the drifting 26 → 27 → 28 while the live population stood still.
/// A scan that degraded quietly here would report a larger, wronger number and look healthy.
#[test]
fn a_census_that_cannot_find_its_catalogue_region_refuses_rather_than_widening() {
    let (_guard, path) = doctored(|text| {
        let heading = "The recurring defect: evidence must be produced where the claim is made";
        assert!(
            text.contains(heading),
            "the catalogue heading must exist to be removed"
        );
        text.replace(
            heading,
            "The recurring defect: REWORDED BY A PLANTED MUTANT",
        )
    });
    let (code, output) = run(Some(&path));
    assert_eq!(
        code, 2,
        "a census that cannot locate the region it must exclude has lost its scope and must \
         exit 2, not report a larger population as though it were clean:\n{output}"
    );
    assert!(
        output.contains("cannot find the catalogue heading"),
        "the refusal must name the missing heading, since the repair is to update the constant \
         and not to delete the check:\n{output}"
    );
}
