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
//! bound.
//!
//! Making the producer *denote* is pfei R2, and **one kind of referent is now walked**: line
//! citations, below. That is the kind whose denotation is mechanical, and it was also the worst
//! — eight of twelve were pointing at the wrong code. The other referent kinds the census
//! recognises are **not** resolved here: a cited test function is not required to exist or to
//! run, a cited lane is not required to be registered in `scripts/check.sh` and `ci.yml`, and a
//! cited bead is not required to be in the tracker. Read the census's `bound` figure with that
//! scope in mind — R2 is part walked, not done.

#![forbid(unsafe_code)]

use std::collections::BTreeSet;
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

/// The four counts AGENTS.md discloses about itself, read from the file rather than transcribed.
///
/// These controls used to hard-code `live=22` in five places. That is the same defect the census
/// exists for, one floor down: a number transcribed into a test drifts from the thing it
/// describes, so every legitimate edit to AGENTS.md by any pane reddened three controls that had
/// nothing to say about the edit. Deriving them keeps the controls exact — they still assert an
/// exact before/after pair — while letting the population move for good reasons.
fn disclosed_counts() -> (usize, usize, usize, usize) {
    let root = workspace_root();
    let text = std::fs::read_to_string(root.join("AGENTS.md")).expect("AGENTS.md is readable");
    let line = text
        .lines()
        .find(|line| line.contains("enforcement-census: live="))
        .unwrap_or_else(|| {
            panic!(
                "AGENTS.md states no `enforcement-census:` disclosure. These controls doctor that \
                 line, so without it they would silently prove nothing."
            )
        });
    let field = |key: &str| -> usize {
        line.split_once(key)
            .and_then(|(_, rest)| {
                let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
                digits.parse().ok()
            })
            .unwrap_or_else(|| panic!("cannot read `{key}` from the disclosure line: {line:?}"))
    };
    (
        field("live="),
        field("bound="),
        field("unbound="),
        field("catalogued="),
    )
}

/// The comparison is real, not a constant agreeing with itself.
///
/// Without this, a census that always returned the disclosed numbers — or one whose `--check`
/// silently short-circuited — would pass identically.
#[test]
fn a_disclosure_that_disagrees_with_the_derivation_is_refused() {
    let (live, ..) = disclosed_counts();
    assert_ne!(
        live, 99,
        "this control doctors the live count to 99; if the real population ever reaches 99, \
         pick a different sentinel rather than deleting the control"
    );
    let (_guard, path) = doctored(move |text| text.replace(&format!("live={live}"), "live=99"));
    let (code, output) = run(Some(&path));
    assert_eq!(code, 1, "a doctored disclosure must be refused:\n{output}");
    assert!(
        output.contains("stated 99") && output.contains(&format!("derived {live}")),
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
    let (live, _, unbound, _) = disclosed_counts();
    let decoy = "\nA planted decoy for the census control: CI refuses every unbound decoy.\n";
    let (_guard, path) = doctored(|text| text + decoy);
    let (code, output) = run(Some(&path));
    assert_eq!(
        code, 1,
        "a planted live claim must move the count:\n{output}"
    );
    assert!(
        output.contains(&format!("live: stated {live}, derived {}", live + 1)),
        "the decoy must be counted as one new LIVE claim — if the derived number did not move, \
         the scan is not reading the file it claims to census:\n{output}"
    );
    assert!(
        output.contains(&format!(
            "unbound: stated {unbound}, derived {}",
            unbound + 1
        )),
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
    let (.., catalogued) = disclosed_counts();
    assert!(
        output.contains(&format!(
            "catalogued: stated {catalogued}, derived {}",
            catalogued + 1
        )) && !output.contains("live:"),
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

// ------------------------------------------------------------------------------------------
// pfei R2 — the document's own line citations, bound to what they point at.
//
// R1 counted the claims; `bound` there means only "names a candidate referent in the same
// sentence". This is the next question: does the referent DENOTE? For a line citation the
// answer is mechanical, and at `c0f2ace5` it was **no** for eight of twelve. All twelve
// resolved to a real file at an in-range line — an existence check passes 12/12 and
// establishes nothing — while eight pointed at code that does not support the sentence.
//
// Every one of the eight had been correct when written. The four reaching into
// `tools/structure-guard/src/checks.rs` had each drifted by exactly +40, from two commits
// inserting above line 1488. One of those same commits moved `FLN-STRUCT-037` in
// `fln-checker`'s charter from 983 to 1014 — and *that* went red within hours, because
// `crates/fln-checker/tests/charter_citations.rs` parses a citation registry the charter
// carries. The identical drift in AGENTS.md was invisible. This is that proven mechanism
// applied to the file that teaches item 7, deliberately in the same shape rather than a
// second design.
// ------------------------------------------------------------------------------------------

/// One `cite <path>:<start>[-<end>] :: <construct>` row of AGENTS.md's citation registry.
#[derive(Debug)]
struct Citation {
    path: String,
    start: usize,
    end: usize,
    construct: String,
}

fn agents_md() -> String {
    std::fs::read_to_string(workspace_root().join("AGENTS.md")).expect("AGENTS.md is readable")
}

/// The registry AGENTS.md carries. Parsed, never transcribed: a second copy of the pairs here
/// would be free to drift from the document's, which is the defect this whole bead is about.
fn citation_registry(text: &str) -> Vec<Citation> {
    text.lines()
        .filter_map(|raw| {
            let rest = raw.trim_start().strip_prefix("cite ")?;
            let (locator, construct) = rest.split_once(" :: ")?;
            let (path, span) = locator.rsplit_once(':')?;
            let (start, end) = match span.split_once('-') {
                Some((a, b)) => (a.trim().parse().ok()?, b.trim().parse().ok()?),
                None => {
                    let only = span.trim().parse().ok()?;
                    (only, only)
                }
            };
            Some(Citation {
                path: path.trim().to_string(),
                start,
                end,
                construct: construct.trim().to_string(),
            })
        })
        .collect()
}

/// Every `<path>.<ext>:<line>` the prose cites, keyed by basename and start line.
///
/// Two kinds are deliberately skipped, and each must SAY so rather than be quietly dropped:
/// the registry's own `cite ` rows, and a citation marked `(historical)` — one that names a
/// location as it was, cited to narrate a defect. Requiring the past to still be true would be
/// a different and wrong demand. An UNMARKED citation is a live claim and must be registered.
/// This is the `fln-8zsq` trap met head-on: the section explaining this check contains the very
/// citations it scans for, so the marker is load-bearing rather than decorative.
fn prose_citations(text: &str) -> BTreeSet<(String, usize)> {
    let mut found = BTreeSet::new();
    for raw in text.lines() {
        if raw.trim_start().starts_with("cite ") {
            continue;
        }
        let chars: Vec<char> = raw.chars().collect();
        let mut index = 0;
        while index < chars.len() {
            if chars[index] != ':' {
                index += 1;
                continue;
            }
            let mut digits_end = index + 1;
            while digits_end < chars.len() && chars[digits_end].is_ascii_digit() {
                digits_end += 1;
            }
            if digits_end == index + 1 {
                index += 1;
                continue;
            }
            let start: usize = chars[index + 1..digits_end]
                .iter()
                .collect::<String>()
                .parse()
                .unwrap_or(0);
            let mut token_start = index;
            while token_start > 0
                && (chars[token_start - 1].is_ascii_alphanumeric()
                    || matches!(chars[token_start - 1], '_' | '.' | '/' | '-'))
            {
                token_start -= 1;
            }
            let token: String = chars[token_start..index].iter().collect();
            let extension = token
                .rsplit_once('.')
                .map(|(_, ext)| ext)
                .unwrap_or_default();
            let looks_like_a_file = !extension.is_empty()
                && extension.len() <= 5
                && extension.chars().all(|c| c.is_ascii_alphabetic());
            if !looks_like_a_file || start == 0 {
                index = digits_end;
                continue;
            }
            let mut span_end = digits_end;
            if span_end < chars.len() && chars[span_end] == '-' {
                let mut tail = span_end + 1;
                while tail < chars.len() && chars[tail].is_ascii_digit() {
                    tail += 1;
                }
                if tail > span_end + 1 {
                    span_end = tail;
                }
            }
            let trailer: String = chars[span_end..].iter().collect();
            if !trailer
                .trim_start_matches(['`', ' '])
                .starts_with("(historical)")
            {
                let base = token.rsplit('/').next().unwrap_or(&token).to_string();
                found.insert((base, start));
            }
            index = span_end;
        }
    }
    found
}

/// Every registry row's cited region must still contain the construct it names.
#[test]
fn every_agents_line_citation_points_at_the_construct_it_names() {
    let root = workspace_root();
    let text = agents_md();
    let rows = citation_registry(&text);
    assert!(
        rows.len() >= 8,
        "parsed only {} citation row(s) from AGENTS.md's registry. Twelve citations were live \
         when this binding was written and eight of them were wrong, so a parse that cannot see \
         the registry is a broken scan and is refused rather than reported as a clean document.",
        rows.len()
    );

    for Citation {
        path,
        start,
        end,
        construct,
    } in &rows
    {
        let body = std::fs::read_to_string(root.join(path))
            .unwrap_or_else(|err| panic!("AGENTS.md cites {path}, which is unreadable: {err}"));
        let lines: Vec<&str> = body.lines().collect();
        assert!(
            *start >= 1 && *end >= *start && *end <= lines.len(),
            "AGENTS.md cites {path}:{start}-{end}, but that file has {} lines",
            lines.len()
        );
        let region = lines[start - 1..*end].join("\n");
        if region.contains(construct.as_str()) {
            continue;
        }
        // A line number is mechanical to repair once you know where the construct went, so the
        // refusal computes that rather than leaving the reader to grep. `hugg`'s lesson: a
        // failure that names the wrong cause costs more than the defect.
        let moved: Vec<usize> = lines
            .iter()
            .enumerate()
            .filter(|(_, line)| line.contains(construct.as_str()))
            .map(|(index, _)| index + 1)
            .collect();
        let span = if end == start {
            format!("{start}")
        } else {
            format!("{start}-{end}")
        };
        let whereabouts = if moved.is_empty() {
            format!("`{construct}` appears nowhere in {path}; it was renamed or deleted")
        } else {
            format!("`{construct}` is now at line(s) {moved:?}")
        };
        panic!(
            "AGENTS.md cites {path}:{span} for `{construct}`, and that region no longer contains \
             it.\n  {whereabouts}.\n\nUpdate BOTH the prose citation and its `cite` row in \
             AGENTS.md — they must move together, and do not relax this test. Eight of twelve \
             citations were already wrong when this binding landed, and every one of the eight \
             had been correct on the day it was written."
        );
    }
}

/// Conservation, in both directions.
///
/// One-way would let the registry under-cover the document while looking complete — the
/// `fln-8zsq` lesson — and the other one-way would let a row outlive the sentence it served,
/// silently overstating coverage, which is `k60n`'s. So: no prose citation without a row, and
/// no row without a prose citation.
#[test]
fn no_line_citation_in_agents_md_escapes_the_citation_registry() {
    let text = agents_md();
    let covered: BTreeSet<(String, usize)> = citation_registry(&text)
        .into_iter()
        .map(|row| {
            (
                row.path.rsplit('/').next().unwrap_or(&row.path).to_string(),
                row.start,
            )
        })
        .collect();
    let prose = prose_citations(&text);

    assert!(
        !prose.is_empty(),
        "scanned AGENTS.md and found NO line citations. Twelve were live when this binding was \
         written, so an empty scan is a broken scanner and never a clean document."
    );
    assert!(
        !covered.is_empty(),
        "AGENTS.md's citation registry parsed to nothing, which would make the check below pass \
         vacuously against any prose at all."
    );

    let uncovered: Vec<_> = prose.difference(&covered).collect();
    assert!(
        uncovered.is_empty(),
        "AGENTS.md's prose cites {uncovered:?}, which the citation registry does not cover. An \
         uncovered citation is a line number nothing checks — the state this bead was filed for. \
         Add a `cite <path>:<line> :: <construct>` row naming what that line holds, or mark the \
         citation `(historical)` if it deliberately names a past state.\nRegistry covers: \
         {covered:?}"
    );

    let orphaned: Vec<_> = covered.difference(&prose).collect();
    assert!(
        orphaned.is_empty(),
        "AGENTS.md's citation registry carries rows for {orphaned:?} that the prose no longer \
         cites. A row outliving its sentence overstates how much of this document is bound — \
         remove the row, or restore the citation it was written for.\nProse cites: {prose:?}"
    );
}
