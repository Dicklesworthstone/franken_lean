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
//! Making the producer *denote* is pfei R2, and **four kinds of referent are now walked**. Line
//! citations came first: the kind whose denotation is mechanical, and also the worst — eight of
//! twelve were pointing at the wrong code. **Test-function names came second**, at `984a1555`,
//! and are the kind whose denotation is load-bearing: a cited test is how a sentence claims to
//! be enforced per commit, so a cited test that does not exist, is ambiguous, is `#[ignore]`d or
//! sits outside every walked member is a claim with no producer. **Operational referents came
//! third**: lane and workflow paths must exist and be reachable from CI, and bead IDs must resolve
//! in the tracker. The Python census remains the sole sentence extractor; this Rust side consumes
//! its line protocol rather than reimplementing the enforcement-claim regex.
//!
//! R3 binds every still-unbound claim to one reviewed-unwalked row, under a ceiling. That is an
//! honest inventory, not executable proof of each reason. R5 adds an independent live-population
//! floor, so softening a sentence, lowering the disclosure, and deleting its review row is a typed
//! refusal. What remains unwatched is semantic truth: an existing test, lane, workflow, bead, or
//! source site can still fail to enforce the sentence's argument.

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;

use fln_conformance::execution::{
    Field, TriggerReachability, ignored_tests, logical_lines, record_field, test_functions,
    trigger_reachability, workspace_member_patterns,
};

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
    let anchor = "   A thirteenth is already filed and deliberately unmechanised:";
    let (_guard, path) = doctored(|text| {
        assert!(
            text.contains(anchor),
            "this control plants inside item 7's section; if that anchor moved, re-point it \
             rather than deleting the control"
        );
        text.replace(
            anchor,
            "   A planted decoy inside the catalogue: CI refuses every catalogued decoy.\n\n\
             \x20  A thirteenth is already filed and deliberately unmechanised:",
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
    /// The item the cited line sits inside, for rows whose construct RECURS in its file.
    site: Option<String>,
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
            let (construct, site) = match construct.split_once(" @@ ") {
                Some((construct, site)) => (construct, Some(site.trim().to_string())),
                None => (construct, None),
            };
            Some(Citation {
                path: path.trim().to_string(),
                start,
                end,
                construct: construct.trim().to_string(),
                site,
            })
        })
        .collect()
}

/// `pub`, `pub(crate)`, `pub(super)` — removed so a visibility change is not a false drift.
fn strip_visibility(text: &str) -> &str {
    let Some(rest) = text.strip_prefix("pub") else {
        return text;
    };
    let rest = rest.trim_start();
    let rest = if rest.starts_with('(') {
        rest.split_once(')').map_or(rest, |(_, after)| after)
    } else {
        rest
    };
    rest.trim_start()
}

/// The nearest item header at or above `line` (1-indexed): the citation's *site*.
fn enclosing_item(lines: &[&str], line: usize) -> String {
    const KINDS: [&str; 7] = ["fn", "impl", "struct", "enum", "trait", "const", "static"];
    for raw in lines[..line.min(lines.len())].iter().rev() {
        let text = strip_visibility(raw.trim_start());
        let text = text.strip_prefix("async ").unwrap_or(text);
        for kind in KINDS {
            let Some(rest) = text
                .strip_prefix(kind)
                .and_then(|rest| rest.strip_prefix(' '))
            else {
                continue;
            };
            let name: String = rest
                .chars()
                .take_while(|c| {
                    c.is_alphanumeric() || matches!(c, '_' | ' ' | ':' | '<' | '>' | '\'')
                })
                .collect();
            return format!("{kind} {}", name.trim());
        }
    }
    "<top of file>".to_string()
}

/// Every way a row can RESOLVE while DENOTING something else, refused.
///
/// `region.contains(construct)` under-reports drift, and by how much was measured rather than
/// reasoned: `0f2ae0ba` shifted four of this file's citations by 45 lines and only two
/// reddened. Two shapes did it — a wide region absorbing the shift, and a needle recurring
/// inside the region so another occurrence satisfied the check.
///
/// Measured over all 11 rows at `b58d0b09` before this rule existed: the recurring-in-region
/// shape was **absent** and the wide-region shape covered **six** rows, worst tolerance 50
/// lines. So the repair is width 1, which drives that tolerance to zero by construction, plus
/// a site declaration for the one row whose construct recurs in its FILE — the only vector
/// left once a citation names a single line.
///
/// The site field is required ONLY where the needle recurs. Elsewhere any shift already breaks
/// containment, so a second assertion could never fail and would be decoration.
fn denotation_complaints(citation: &Citation, body: &str) -> Vec<String> {
    let lines: Vec<&str> = body.lines().collect();
    let Citation {
        path,
        start,
        end,
        construct,
        site,
    } = citation;
    let mut out = Vec::new();

    if end != start {
        out.push(format!(
            "AGENTS.md cites {path}:{start}-{end}, a {}-line RANGE. A range tolerates any shift \
             that keeps the construct inside it — measured at up to 50 lines on this registry — \
             so a citation can resolve while denoting something else. Cite the single line the \
             construct sits on. Width 1 reddens on any insertion above it, which is the point: \
             it fails loudly where a range failed silently.",
            end - start + 1
        ));
    }

    let occurrences = lines
        .iter()
        .filter(|line| line.contains(construct.as_str()))
        .count();
    if occurrences > 1 {
        match site {
            None => out.push(format!(
                "AGENTS.md cites `{construct}` in {path}, where it occurs {occurrences} times. At \
                 width 1 a shift landing exactly on another occurrence still resolves, so this \
                 row must name the item it sits inside: `cite {path}:{start} :: {construct} @@ \
                 fn <name>`."
            )),
            Some(declared) => {
                let actual = enclosing_item(&lines, *start);
                if &actual != declared {
                    out.push(format!(
                        "AGENTS.md's row for {path}:{start} declares it sits inside `{declared}`, \
                         but that line is inside `{actual}`. `{construct}` occurs {occurrences} \
                         times, so the line still CONTAINS it and containment stays green — this \
                         is the tolerance containment cannot see. Re-derive the citation."
                    ));
                }
            }
        }
    }
    out
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

    for citation in &rows {
        let Citation {
            path,
            start,
            end,
            construct,
            ..
        } = citation;
        let body = std::fs::read_to_string(root.join(path))
            .unwrap_or_else(|err| panic!("AGENTS.md cites {path}, which is unreadable: {err}"));
        let lines: Vec<&str> = body.lines().collect();
        assert!(
            *start >= 1 && *end >= *start && *end <= lines.len(),
            "AGENTS.md cites {path}:{start}-{end}, but that file has {} lines",
            lines.len()
        );

        // RESOLVING is weaker than DENOTING, and the gap was measured at up to 50 lines on
        // this very registry. Checked before containment because a range is refused outright.
        let denotation = denotation_complaints(citation, &body);
        assert!(
            denotation.is_empty(),
            "AGENTS.md's citation registry no longer denotes what it names:\n  {}",
            denotation.join("\n  ")
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

/// The denotation rules fire, are correctly scoped, and their MEASURED LIMIT is pinned here.
///
/// Driven over injected text, not the tree, and that is load-bearing rather than stylistic:
/// after the repair AGENTS.md has **zero** rows whose construct recurs, so the site branch has
/// no members and the real registry can never exercise it. A repaired population's live guard
/// is unkillable; only a planted member still catches the mutant.
#[test]
fn the_denotation_rules_fire_and_their_measured_limit_is_pinned() {
    let two_homes = "\
fn first_home() {
    let x = MARKER;
}

fn second_home() {
    let y = MARKER;
}
";
    let one_item = "\
fn only_home() {
    let a = MARKER;
    let b = MARKER;
}
";
    let unique = "fn solo_home() {\n    let z = SOLO;\n}\n";

    let cite = |start: usize, end: usize, construct: &str, site: Option<&str>| Citation {
        path: "tools/structure-guard/src/checks.rs".into(),
        start,
        end,
        construct: construct.into(),
        site: site.map(str::to_string),
    };

    // NEGATIVE CONTROL FIRST, or every cell below proves only that the function complains.
    assert!(
        denotation_complaints(&cite(2, 2, "SOLO", None), unique).is_empty(),
        "a width-1 row with a unique construct must be silent"
    );

    // A range is refused outright — the shape that absorbed a 45-line shift.
    let ranged = denotation_complaints(&cite(1, 7, "SOLO", None), unique);
    assert!(
        ranged.iter().any(|line| line.contains("7-line RANGE")),
        "a range must be refused, naming its width: {ranged:?}"
    );

    // A recurring construct with no site declared is refused, naming the count.
    let unsited = denotation_complaints(&cite(2, 2, "MARKER", None), two_homes);
    assert!(
        unsited
            .iter()
            .any(|l| l.contains("occurs 2 times") && l.contains("@@")),
        "an unsited recurring row must say why and how to repair it: {unsited:?}"
    );

    // Declared and wrong.
    let wrong = denotation_complaints(&cite(2, 2, "MARKER", Some("fn second_home")), two_homes);
    assert!(
        wrong
            .iter()
            .any(|l| l.contains("fn first_home") && l.contains("fn second_home")),
        "a wrong site must name both declared and actual: {wrong:?}"
    );

    // Declared and right.
    assert!(
        denotation_complaints(&cite(6, 6, "MARKER", Some("fn second_home")), two_homes).is_empty(),
        "a correct site must be accepted"
    );

    // SCOPING: a unique construct is exempt even with a wrong site, because containment
    // already catches any shift and a second check there could never fail.
    assert!(
        denotation_complaints(&cite(2, 2, "SOLO", Some("fn nonsense")), unique).is_empty(),
        "the site rule must not reach a construct that occurs once"
    );

    // THE MEASURED LIMIT, pinned so nobody reads the site rule as total. Two occurrences
    // INSIDE ONE ITEM: the enclosing item is a coarser identity than the occurrence, so a
    // citation on the wrong one is NOT caught. Measured against the real `FLN-STRUCT-024`
    // row, whose seven occurrences all sit in `fn validate_constitutional_baseline`; that row
    // was repaired by taking a unique needle instead, not by this mechanism.
    assert!(
        denotation_complaints(&cite(2, 2, "MARKER", Some("fn only_home")), one_item).is_empty()
            && denotation_complaints(&cite(3, 3, "MARKER", Some("fn only_home")), one_item)
                .is_empty(),
        "this cell documents a KNOWN BLIND SPOT: within one item the site cannot discriminate. \
         If it now fails, the rule got stronger — delete this cell and say so, do not weaken \
         the rule to restore it."
    );
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

// ------------------------------------------------------------------------------------------
// pfei R2, second referent kind — the tests this document names must exist AND RUN.
//
// R2's first half bound the line citations, and its own closing note said what was still
// open: "a cited test function is not required to exist or to RUN". This is that half.
//
// **Why this kind rots the same way the line citations did, measured rather than assumed.**
// The population of test names AGENTS.md cites went 0 -> 20 over the three days to
// `984a1555`, moving on 16 of the file's last 40 revisions — and every single movement was an
// ADDITION. Twenty citations accreted in three days with nothing checking one. Because the
// prose side only ever grows, the rot vector is never "the sentence drops the name"; it is
// "the test is renamed, deleted, `#[ignore]`d or moved into a package `cargo test` does not
// walk, while the sentence stays". So the population is derived from the PROSE and resolved
// against the TREE. Deriving it from the tree instead is the trap this lineage already
// recorded: two derived sets that both shrink agree perfectly, and a deleted test would
// simply leave the population rather than fail it.
//
// **The predicates are borrowed, never re-implemented.** `execution::{test_functions,
// ignored_tests, workspace_member_patterns}` already judge exactly these questions for
// `ci/VERIFICATION_MANIFEST.jsonl` (bead `fln-rgha`). A second copy of "what is a test" here
// would be free to drift from the one the manifest is judged by — the defect this bead's
// whole family is about. It also inherits a trap paid for twice: `#[test]` and `#[ignore]`
// appear in this workspace inside doc comments and guard assertions, so the construct is
// recognised by the ATTRIBUTE at line start, never by the token. Writing that scan afresh
// reproduces the bug — measured, while deriving this population: a window-based reading
// reported `corpus_census_keeps_disclosing_its_claim_class` as `#[ignore]`d because a doc
// comment six lines above it discusses `#[ignore]`d tests. It is not ignored.
//
// **Two tiers, because the shape rule is only needed in one direction.** Tier 1 takes EVERY
// backticked snake_case token and, if it resolves to a real `#[test]`, requires that test to
// run: no threshold, because demanding that an already-resolving test still run cannot
// produce a false positive. Tier 2 requires a token that resolves to NOTHING to be declared,
// and that is where a wrong guess reddens a peer's tree, so it is bounded to tokens with at
// least four underscores. Measured at `984a1555`: all 17 cited tests clear that bar and only
// three non-test tokens do, so the declared remainder is three rows rather than fifty-two.
//
// **The remainder is bound, the total deliberately is NOT.** Binding `cited=20` would redden
// on precisely the commits that add a good citation — the cry-wolf failure this bead already
// measured once, when a census counted item 7's catalogue and drifted 26 -> 27 -> 28 while
// the live population stood still. What must be declared is what is NOT verified: the three
// non-tests and the one cited test that does not run per commit.
// ------------------------------------------------------------------------------------------

/// Tokens AGENTS.md cites in the test-name shape that are **not** test functions.
///
/// Each row says what the token really is, so the next reader can tell a deliberate exclusion
/// from a citation nobody repaired. Checked in both directions and under a ceiling: a row whose
/// token has left AGENTS.md is stale and must be removed, so this list can only shrink without a
/// deliberate, reviewable bump.
const NON_TEST_TOKENS: &[(&str, &str)] = &[
    (
        "governed_input_mutation_during_initial_hash",
        "a failure name `scripts/check.sh` prints for M4, not a Rust item",
    ),
    (
        "not_applicable_no_supported_inputs",
        "one of UBS's six terminal-mode classes",
    ),
    (
        "validate_level_is_supported_by_its_oracle",
        "a `pub fn` in crates/fln-conformance/src/ledger.rs — a producer the Parity Ledger guard \
         calls, not a `#[test]`",
    ),
];

/// The ceiling on that allowance. Growth is legitimate and must be deliberate, never silent.
const NON_TEST_CEILING: usize = 4;

/// Cited tests that do **not** run under plain `cargo test`, with the reason that is honest.
///
/// A cited test which is `#[ignore]`d is the hollow-green shape: the sentence reads as a
/// per-commit mechanism and nothing executes. It is legitimate only when the document says so in
/// the same breath, which for this one it does — the corpus matrix is an on-demand lane and
/// AGENTS.md states the PG-5 shortfall and its waiver beside it.
const IGNORED_CITATIONS: &[(&str, &str)] = &[(
    "present_olean_corpus_thread_matrix_compares_stream_digests",
    "the on-demand corpus thread-matrix lane; AGENTS.md declares the PG-5 per-commit shortfall \
     and its expiring waiver in the same section",
)];

/// Every `#[test]` in the workspace, and where cargo would run it from.
struct TestIndex {
    /// name -> the walked files declaring it. A set, because a name is not an identity.
    walked: BTreeMap<String, BTreeSet<String>>,
    /// name -> files OUTSIDE any walked member target (nested workspaces, benches, examples).
    unwalked: BTreeMap<String, BTreeSet<String>>,
    /// Names carrying `#[ignore]`, by the attribute rather than the token.
    ignored: BTreeSet<String>,
    members: usize,
    files: usize,
    attributes: usize,
}

/// Resolve the root manifest's own `members` globs, then walk each member's `src` and `tests`.
///
/// `member/{src,tests}` is what cargo compiles for a workspace-root `cargo test`, and it excludes
/// the two nested workspaces (`tools/structure-guard/kernel-ownership-publisher`,
/// `tribunal/epoch-lab`) structurally rather than by name — the hand-listed-scope defect this
/// session's own guard already reproduced once. Everything else under the repository is indexed
/// separately as `unwalked`, so a citation to a test that exists but cannot run gets told which
/// of the two it is instead of a misleading "no such test".
fn index_tests(root: &Path) -> TestIndex {
    let manifest = std::fs::read_to_string(root.join("Cargo.toml")).expect("root Cargo.toml");
    let patterns = workspace_member_patterns(&manifest)
        .expect("the root Cargo.toml must declare a non-empty [workspace] members array");
    let mut member_dirs = BTreeSet::new();
    for pattern in patterns {
        match pattern.strip_suffix("/*") {
            Some(prefix) => {
                let Ok(entries) = std::fs::read_dir(root.join(prefix)) else {
                    continue;
                };
                for entry in entries.flatten() {
                    if entry.path().is_dir() {
                        let name = entry.file_name().to_string_lossy().into_owned();
                        member_dirs.insert(format!("{prefix}/{name}"));
                    }
                }
            }
            None => {
                if root.join(&pattern).is_dir() {
                    member_dirs.insert(pattern);
                }
            }
        }
    }
    let compiled: BTreeSet<String> = member_dirs
        .iter()
        .flat_map(|dir| [format!("{dir}/src/"), format!("{dir}/tests/")])
        .collect();

    let mut index = TestIndex {
        walked: BTreeMap::new(),
        unwalked: BTreeMap::new(),
        ignored: BTreeSet::new(),
        members: member_dirs.len(),
        files: 0,
        attributes: 0,
    };
    let mut sources = BTreeMap::new();
    collect_rust_sources(root, root, &mut sources);
    for (relative, text) in sources {
        index.files += 1;
        let is_compiled = compiled.iter().any(|prefix| relative.starts_with(prefix));
        for name in test_functions(&text) {
            index.attributes += 1;
            let bucket = if is_compiled {
                &mut index.walked
            } else {
                &mut index.unwalked
            };
            bucket.entry(name).or_default().insert(relative.clone());
        }
        for (name, _reason) in ignored_tests(&text) {
            index.ignored.insert(name);
        }
    }
    index
}

/// Collect every Rust source under the repository, skipping build and vendored trees.
///
/// A node this cannot read is a refusal, never a skip: a file dropped silently is exactly the
/// one nobody is looking at. Symlinks are not descended — cargo does not compile through a
/// directory symlink, and refusing removes the only way this walk fails to terminate.
fn collect_rust_sources(dir: &Path, root: &Path, out: &mut BTreeMap<String, String>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(entries) => entries,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return,
        Err(error) => panic!(
            "test-citation scan: {} is unreadable: {error}",
            dir.display()
        ),
    };
    for entry in entries {
        let entry = entry.expect("a readable directory entry");
        let kind = entry.file_type().expect("a readable file type");
        if kind.is_symlink() {
            continue;
        }
        let path = entry.path();
        if kind.is_dir() {
            let name = entry.file_name().to_string_lossy().into_owned();
            // Neither is source this workspace compiles, and `vendor/` alone is 652 MB.
            if matches!(name.as_str(), "target" | "vendor" | ".git" | "node_modules") {
                continue;
            }
            collect_rust_sources(&path, root, out);
            continue;
        }
        if !path.extension().is_some_and(|ext| ext == "rs") {
            continue;
        }
        let text = std::fs::read_to_string(&path).unwrap_or_else(|error| {
            panic!(
                "test-citation scan: {} could not be read ({error}). A Rust file dropped here is \
                 one this scan never judges — refuse rather than narrow the scope silently.",
                path.display()
            )
        });
        let relative = path
            .strip_prefix(root)
            .expect("a scanned path lies under the repository")
            .to_string_lossy()
            .replace('\\', "/");
        out.insert(relative, text);
    }
}

/// Every backticked `snake_case` identifier AGENTS.md carries, with its underscore count.
///
/// A `path::to::name` citation is split, so `evidence_finalization.rs::the_evidence_surface_…`
/// yields the function. The threshold is applied by the caller, not here, because the two tiers
/// need different ones.
fn backticked_identifiers(text: &str) -> BTreeSet<String> {
    let mut found = BTreeSet::new();
    // Pairing is LINE-SCOPED, which is not a detail. Pairing across the whole file lets the three
    // backticks of a ``` fence shift every subsequent pair by one, so a real citation after a
    // fenced block silently stops being scanned — a narrower population that still clears the
    // floor and reads as a clean document.
    for line in text.lines() {
        let mut rest = line;
        while let Some(open) = rest.find('`') {
            let after = &rest[open + 1..];
            let Some(close) = after.find('`') else { break };
            let span = &after[..close];
            for piece in span.split("::") {
                let piece = piece.trim();
                let shaped = !piece.is_empty()
                    && piece.contains('_')
                    && piece.starts_with(|c: char| c.is_ascii_lowercase())
                    && piece
                        .chars()
                        .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_');
                if shaped {
                    found.insert(piece.to_string());
                }
            }
            rest = &after[close + 1..];
        }
    }
    found
}

/// The tier-2 threshold, and the only place a wrong guess can redden a healthy tree.
const DECLARATION_THRESHOLD: usize = 4;

/// Judge AGENTS.md's test citations against the tree. Pure, so mutants are planted in the
/// arguments rather than in the repository.
fn judge_test_citations(text: &str, index: &TestIndex) -> Vec<String> {
    let mut findings = Vec::new();
    let candidates = backticked_identifiers(text);
    let long: BTreeSet<&String> = candidates
        .iter()
        .filter(|token| token.matches('_').count() >= DECLARATION_THRESHOLD)
        .collect();

    // Anti-vacuity first. A scan that walked nothing and a document that cites nothing produce
    // the identical empty finding list, and one of those is a broken scan.
    if index.members < 20 {
        findings.push(format!(
            "scan floor: resolved only {} workspace members from the root manifest's globs; 33 \
             were present when this binding landed. A collapsed member set silently empties the \
             test index.",
            index.members
        ));
    }
    if index.attributes < 800 {
        findings.push(format!(
            "scan floor: found only {} `#[test]` attributes across {} Rust files; 1887 across 244 \
             were present when this binding landed at `984a1555`. That is the WHOLE repository, \
             not just the walked members — 1678 of them across 208 files sit under a member's \
             `src/` or `tests/`, and the rest are what makes `cited-but-unreachable` reportable. \
             A broken walk and a clean tree are the same green, so this refuses rather than \
             reports nothing to check.",
            index.attributes, index.files
        ));
    }
    if long.len() < 12 {
        findings.push(format!(
            "scan floor: AGENTS.md yielded only {} test-shaped citations; 20 were live when this \
             binding landed and the population has never once shrunk. An empty or thin scan is a \
             broken scanner, never a clean document.",
            long.len()
        ));
    }

    for token in &candidates {
        // Tier 1: it resolves, so it must actually run. No threshold — this cannot false-positive.
        if let Some(paths) = index.walked.get(token) {
            if paths.len() > 1 {
                findings.push(format!(
                    "ambiguous-citation: AGENTS.md cites `{token}`, and {} different files declare \
                     a `#[test] fn {token}`: {paths:?}. The citation denotes two things, so the \
                     reader cannot tell which sentence's evidence is which. Eight test names in \
                     this workspace are already non-unique — a name is not an identity.",
                    paths.len()
                ));
                continue;
            }
            let declared = IGNORED_CITATIONS.iter().any(|(name, _)| name == token);
            if index.ignored.contains(token) && !declared {
                findings.push(format!(
                    "cited-but-not-run: AGENTS.md cites `{token}` ({}), and it is `#[ignore]`d, so \
                     plain `cargo test` never runs it. The sentence reads as a per-commit \
                     mechanism and nothing executes — the hollow-green shape. Either remove the \
                     `#[ignore]`, or declare it in IGNORED_CITATIONS with the reason AGENTS.md \
                     gives, and say in the prose that it does not run per commit.",
                    paths.iter().next().map(String::as_str).unwrap_or("?")
                ));
            }
            continue;
        }
        if !long.contains(token) {
            continue;
        }
        // Tier 2: it resolves nowhere cargo walks, and it is shaped like a test name.
        if NON_TEST_TOKENS.iter().any(|(name, _)| name == token) {
            continue;
        }
        if let Some(paths) = index.unwalked.get(token) {
            findings.push(format!(
                "cited-but-unreachable: AGENTS.md cites `{token}`, which exists at {paths:?} — but \
                 that path is not under any workspace member's `src/` or `tests/`, so a \
                 workspace-root `cargo test` never compiles it. A libtest filter matching nothing \
                 exits 0, which is why this is a finding and not a silence."
            ));
            continue;
        }
        findings.push(format!(
            "citation-denotes-nothing: AGENTS.md cites `{token}` in the shape of a test name, and \
             no `#[test] fn {token}` exists anywhere in this repository. Either the test was \
             renamed or deleted and the prose was left behind — repair the sentence — or the token \
             is not a test, in which case add it to NON_TEST_TOKENS saying what it actually is. \
             Eight of twelve line citations in this file were already rot when they were measured, \
             and every one had been correct on the day it was written."
        ));
    }

    // The declared remainders, in the direction that makes them shrink with repair.
    if NON_TEST_TOKENS.len() > NON_TEST_CEILING {
        findings.push(format!(
            "allowance ceiling: {} declared non-test tokens against a ceiling of \
             {NON_TEST_CEILING}. Growth here is legitimate and must be deliberate — raise the \
             ceiling in the same commit that adds the row, so it is reviewed rather than absorbed.",
            NON_TEST_TOKENS.len()
        ));
    }
    for (token, reason) in NON_TEST_TOKENS {
        if !candidates.contains(*token) {
            findings.push(format!(
                "stale allowance: NON_TEST_TOKENS declares `{token}` ({reason}), which AGENTS.md no \
                 longer cites. A row outliving its sentence overstates how much of this document \
                 is bound — remove it."
            ));
        }
    }
    for (token, reason) in IGNORED_CITATIONS {
        if !candidates.contains(*token) {
            findings.push(format!(
                "stale allowance: IGNORED_CITATIONS declares `{token}` ({reason}), which AGENTS.md \
                 no longer cites. Remove the row."
            ));
        } else if !index.ignored.contains(*token) {
            findings.push(format!(
                "stale allowance: IGNORED_CITATIONS declares `{token}` as not running per commit, \
                 but it is no longer `#[ignore]`d. The allowance must shrink when the thing it \
                 excused is repaired — remove the row."
            ));
        }
    }
    findings
}

/// Every test AGENTS.md names must exist, be unambiguous, and actually run.
#[test]
fn every_agents_test_citation_names_a_test_that_runs() {
    let root = workspace_root();
    let index = index_tests(&root);
    let findings = judge_test_citations(&agents_md(), &index);
    assert!(
        findings.is_empty(),
        "AGENTS.md names tests that do not denote what the prose claims:\n\n{}\n\nThis is pfei R2's \
         second referent kind. `bound` in the enforcement census means only that a producer is \
         NAMED in the sentence; this is the check that it exists and runs.",
        findings.join("\n\n")
    );
}

// ---- controls (pfei R4): a decoy the scan must see, and its deletion it must notice ----

fn index_for_controls() -> TestIndex {
    index_tests(&workspace_root())
}

/// The decoy. A planted citation to a test that does not exist must be FOUND.
///
/// Without this the binding above passes identically against a scan that returns an empty finding
/// list no matter what the document says — which is what a census that has lost its scope looks
/// like, and is how this bead's R1 figure was wrong for a day.
#[test]
fn a_planted_citation_to_a_missing_test_is_caught() {
    let index = index_for_controls();
    let decoy = "`this_planted_test_name_denotes_absolutely_nothing`";
    let doctored = format!("{}\n\nThe guard cites {decoy} here.\n", agents_md());
    let findings = judge_test_citations(&doctored, &index);
    assert!(
        findings
            .iter()
            .any(|f| f.starts_with("citation-denotes-nothing")
                && f.contains("this_planted_test_name_denotes_absolutely_nothing")),
        "a planted citation to a nonexistent test was not reported: {findings:?}"
    );
}

/// The mutant that DELETES the decoy: with it gone the scan must go quiet again.
///
/// A guard that reports the decoy while also reporting the healthy document is not discriminating
/// — it is failing. This is the half that proves the finding above came from the plant.
#[test]
fn removing_the_planted_citation_returns_the_scan_to_silence() {
    let index = index_for_controls();
    let findings = judge_test_citations(&agents_md(), &index);
    assert!(
        findings.is_empty(),
        "with no decoy planted the real document must judge clean; got: {findings:?}"
    );
}

/// A planted citation that RESOLVES must not be a finding.
///
/// The negative control that keeps this from being a blanket refusal of new tokens: 17 of the 20
/// citations that accreted in three days were legitimate, and a guard that taxed each of them
/// would be relaxed within a week.
#[test]
fn a_planted_citation_that_resolves_is_not_a_finding() {
    let index = index_for_controls();
    let real = "every_agents_test_citation_names_a_test_that_runs";
    assert!(
        index.walked.contains_key(real),
        "this control needs a test that really exists"
    );
    let doctored = format!("{}\n\nA sentence citing `{real}`.\n", agents_md());
    assert!(
        judge_test_citations(&doctored, &index).is_empty(),
        "a citation to a test that exists and runs must be silent, not taxed"
    );
}

/// A cited test that stops running is caught — both ways it can stop.
#[test]
fn a_cited_test_that_stops_running_is_caught() {
    let mut index = index_for_controls();
    let cited = "the_evidence_surface_refuses_a_gitdir_pointer_root";
    assert!(
        index.walked.contains_key(cited),
        "control needs a live citation"
    );

    let mut ignored_now = index_for_controls();
    ignored_now.ignored.insert(cited.to_string());
    let findings = judge_test_citations(&agents_md(), &ignored_now);
    assert!(
        findings
            .iter()
            .any(|f| f.starts_with("cited-but-not-run") && f.contains(cited)),
        "a cited test becoming `#[ignore]`d must be reported: {findings:?}"
    );

    let paths = index.walked.remove(cited).expect("the cited test");
    index.unwalked.insert(cited.to_string(), paths);
    let findings = judge_test_citations(&agents_md(), &index);
    assert!(
        findings
            .iter()
            .any(|f| f.starts_with("cited-but-unreachable") && f.contains(cited)),
        "a cited test moving out of every walked member must be reported: {findings:?}"
    );
}

/// A cited name declared by two files is refused rather than silently resolved.
///
/// Eight names in this workspace are already non-unique. A citation keyed on one would be a key
/// treated as an identity with nobody checking injectivity — the shape this lineage has paid for
/// repeatedly.
#[test]
fn a_cited_test_declared_twice_is_refused_rather_than_resolved() {
    let mut index = index_for_controls();
    let cited = "the_build_gate_table_names_every_freeze_mechanism_in_the_code";
    index
        .walked
        .get_mut(cited)
        .expect("control needs a live citation")
        .insert("crates/fln-somewhere-else/tests/twin.rs".to_string());
    let findings = judge_test_citations(&agents_md(), &index);
    assert!(
        findings
            .iter()
            .any(|f| f.starts_with("ambiguous-citation") && f.contains(cited)),
        "a doubly-declared cited test must be refused: {findings:?}"
    );
}

/// An empty or collapsed scan refuses instead of reporting a clean document.
#[test]
fn an_empty_scan_refuses_rather_than_reporting_a_clean_document() {
    let index = index_for_controls();
    let findings = judge_test_citations("AGENTS.md with no citations at all.\n", &index);
    assert!(
        findings.iter().any(|f| f.starts_with("scan floor")),
        "a document yielding no citations must be refused as a broken scan: {findings:?}"
    );

    let collapsed = TestIndex {
        walked: BTreeMap::new(),
        unwalked: BTreeMap::new(),
        ignored: BTreeSet::new(),
        members: 0,
        files: 0,
        attributes: 0,
    };
    let findings = judge_test_citations(&agents_md(), &collapsed);
    assert!(
        findings
            .iter()
            .filter(|f| f.starts_with("scan floor"))
            .count()
            >= 2,
        "an index that walked nothing must refuse on its own floors before judging citations: \
         {findings:?}"
    );
}

/// A declared allowance that has outlived its reason is refused.
#[test]
fn an_allowance_that_outlived_its_reason_is_refused() {
    let index = index_for_controls();
    // The document stops citing a declared non-test token: the row is now stale.
    let without = agents_md().replace("governed_input_mutation_during_initial_hash", "M4");
    let findings = judge_test_citations(&without, &index);
    assert!(
        findings.iter().any(|f| f.starts_with("stale allowance")
            && f.contains("governed_input_mutation_during_initial_hash")),
        "an allowance row whose token left the document must be refused: {findings:?}"
    );

    // The one cited test that does not run per commit starts running: the excuse must go.
    let mut repaired = index_for_controls();
    repaired
        .ignored
        .remove("present_olean_corpus_thread_matrix_compares_stream_digests");
    let findings = judge_test_citations(&agents_md(), &repaired);
    assert!(
        findings.iter().any(|f| f.starts_with("stale allowance")
            && f.contains("present_olean_corpus_thread_matrix_compares_stream_digests")),
        "an ignored-citation allowance must shrink when the test starts running: {findings:?}"
    );
}

// ------------------------------------------------------------------------------------------
// pfei R2, operational referents — lanes/workflows must be reachable, beads must resolve.
//
// The Python census remains the only authority for which sentences are enforcement claims. It
// emits the three operational referent kinds as a deliberately tiny line protocol; this side
// resolves them against the live repository. Re-implementing ENFORCE here would create two
// populations that could shrink together and agree perfectly while dropping a claim.
// ------------------------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum OperationalKind {
    Lane,
    Workflow,
    Bead,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct OperationalReferent {
    line: usize,
    kind: OperationalKind,
    value: String,
}

fn extract_operational_referents(agents: &Path) -> Result<Vec<OperationalReferent>, String> {
    let root = workspace_root();
    let out = Command::new("python3")
        .arg("-I")
        .arg("-S")
        .arg("-B")
        .arg(root.join(CENSUS))
        .arg("--referents")
        .arg("--agents")
        .arg(agents)
        .current_dir(&root)
        .output()
        .map_err(|error| format!("{CENSUS} --referents could not run: {error}"))?;
    if !out.status.success() {
        return Err(format!(
            "{CENSUS} --referents exited {:?}:\n{}{}",
            out.status.code(),
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    let stdout = String::from_utf8(out.stdout)
        .map_err(|error| format!("{CENSUS} --referents emitted non-UTF-8: {error}"))?;
    let mut referents = Vec::new();
    for (output_line, raw) in stdout.lines().enumerate() {
        if raw.is_empty() {
            continue;
        }
        let fields: Vec<&str> = raw.split('\t').collect();
        if fields.len() != 3 {
            return Err(format!(
                "{CENSUS} --referents line {} has {} tab-separated fields, expected 3: {raw:?}",
                output_line + 1,
                fields.len()
            ));
        }
        let line = fields[0].parse().map_err(|error| {
            format!(
                "{CENSUS} --referents line {} has a non-numeric AGENTS.md line {:?}: {error}",
                output_line + 1,
                fields[0]
            )
        })?;
        let kind = match fields[1] {
            "lane" => OperationalKind::Lane,
            "workflow" => OperationalKind::Workflow,
            "bead" => OperationalKind::Bead,
            other => {
                return Err(format!(
                    "{CENSUS} --referents line {} has unknown kind {other:?}",
                    output_line + 1
                ));
            }
        };
        if fields[2].is_empty() {
            return Err(format!(
                "{CENSUS} --referents line {} has an empty value",
                output_line + 1
            ));
        }
        referents.push(OperationalReferent {
            line,
            kind,
            value: fields[2].to_string(),
        });
    }
    Ok(referents)
}

struct OperationalInputs {
    check_sh: String,
    ci: String,
    beads: String,
}

fn operational_inputs(root: &Path) -> OperationalInputs {
    let read = |path: &str| {
        std::fs::read_to_string(root.join(path)).unwrap_or_else(|error| {
            panic!("operational referent input {path} is unreadable: {error}")
        })
    };
    OperationalInputs {
        check_sh: read("scripts/check.sh"),
        ci: read(".github/workflows/ci.yml"),
        beads: read(".beads/issues.jsonl"),
    }
}

const MIN_LIVE_BEAD_REFERENTS: usize = 4;

fn judge_operational_referents(
    root: &Path,
    referents: &[OperationalReferent],
    inputs: &OperationalInputs,
) -> Vec<String> {
    let mut findings = Vec::new();
    let check_lines = logical_lines(&inputs.check_sh);
    let ci_lines = logical_lines(&inputs.ci);
    let ci_reachability = trigger_reachability(&inputs.ci);

    let mut tracker_ids = BTreeSet::new();
    let mut malformed_tracker_lines = Vec::new();
    for (index, line) in inputs.beads.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        match record_field(line, "id") {
            Some(Field::Text(id)) => {
                tracker_ids.insert(id);
            }
            _ => malformed_tracker_lines.push(index + 1),
        }
    }
    if !malformed_tracker_lines.is_empty() {
        findings.push(format!(
            "tracker-unreadable: .beads/issues.jsonl has record(s) without a decodable text id at \
             lines {malformed_tracker_lines:?}; a broken tracker reader is inconclusive, never a \
             clean referent population"
        ));
    }

    let live_beads: BTreeSet<&str> = referents
        .iter()
        .filter(|referent| referent.kind == OperationalKind::Bead)
        .map(|referent| referent.value.as_str())
        .collect();
    if live_beads.len() < MIN_LIVE_BEAD_REFERENTS {
        findings.push(format!(
            "operational scan floor: only {} unique bead referent(s) were derived; \
             {MIN_LIVE_BEAD_REFERENTS} were live when this binding landed. An empty referent \
             stream and a document with none look identical without this floor.",
            live_beads.len()
        ));
    }

    for referent in referents {
        match referent.kind {
            OperationalKind::Lane => {
                if !root.join(&referent.value).is_file() {
                    findings.push(format!(
                        "lane-denotes-nothing: AGENTS.md:{} names {}, which is not a file",
                        referent.line, referent.value
                    ));
                    continue;
                }
                if !check_lines
                    .iter()
                    .any(|line| line.contains(&referent.value))
                {
                    findings.push(format!(
                        "lane-not-registered: AGENTS.md:{} names {}, but no logical non-comment \
                         scripts/check.sh line names it",
                        referent.line, referent.value
                    ));
                }
                let invocation = format!("./{}", referent.value);
                if !ci_lines.iter().any(|line| line.contains(&invocation)) {
                    findings.push(format!(
                        "lane-not-executed: AGENTS.md:{} names {}, but .github/workflows/ci.yml \
                         never executes {invocation}",
                        referent.line, referent.value
                    ));
                }
                if ci_reachability != TriggerReachability::Reachable {
                    findings.push(format!(
                        "lane-ci-unreachable: AGENTS.md:{} names {}, but ci.yml's top-level \
                         trigger is {ci_reachability:?}; job text cannot execute from a workflow \
                         that cannot fire",
                        referent.line, referent.value
                    ));
                }
            }
            OperationalKind::Workflow => {
                let path = root.join(&referent.value);
                if !path.is_file() {
                    findings.push(format!(
                        "workflow-denotes-nothing: AGENTS.md:{} names {}, which is not a file",
                        referent.line, referent.value
                    ));
                    continue;
                }
                let body = if referent.value == ".github/workflows/ci.yml" {
                    inputs.ci.clone()
                } else {
                    match std::fs::read_to_string(&path) {
                        Ok(body) => body,
                        Err(error) => {
                            findings.push(format!(
                                "workflow-unreadable: AGENTS.md:{} names {}, which cannot be read: \
                                 {error}",
                                referent.line, referent.value
                            ));
                            continue;
                        }
                    }
                };
                match trigger_reachability(&body) {
                    TriggerReachability::Reachable => {}
                    TriggerReachability::NeverFires => findings.push(format!(
                        "workflow-never-fires: AGENTS.md:{} names {}, but it has no top-level on \
                         key",
                        referent.line, referent.value
                    )),
                    TriggerReachability::Unreadable => findings.push(format!(
                        "workflow-trigger-unreadable: AGENTS.md:{} names {}, whose trigger cannot \
                         be classified; inconclusive is not reachable",
                        referent.line, referent.value
                    )),
                }
            }
            OperationalKind::Bead => {
                if !tracker_ids.contains(&referent.value) {
                    findings.push(format!(
                        "bead-denotes-nothing: AGENTS.md:{} names {}, which has no record in \
                         .beads/issues.jsonl",
                        referent.line, referent.value
                    ));
                }
            }
        }
    }
    findings
}

#[test]
fn every_agents_operational_referent_denotes_a_reachable_producer() {
    let root = workspace_root();
    let referents = extract_operational_referents(&root.join("AGENTS.md"))
        .expect("the operational referent stream must parse");
    let findings = judge_operational_referents(&root, &referents, &operational_inputs(&root));
    assert!(
        findings.is_empty(),
        "AGENTS.md names operational producers that do not denote or cannot run:\n\n{}",
        findings.join("\n\n")
    );
}

#[test]
fn planted_missing_lane_and_bead_referents_are_refused_then_deletion_is_clean() {
    let root = workspace_root();
    let inputs = operational_inputs(&root);
    let (_guard, planted) = doctored(|text| {
        text + "\nCI refuses a planted missing lane through \
                scripts/e2e/pfei_planted_missing_lane.sh.\n\
                A planted release blocks the gate under bead \
                `fln-pfei-planted-missing-bead`.\n"
    });
    let referents = extract_operational_referents(&planted).expect("the planted stream parses");
    let findings = judge_operational_referents(&root, &referents, &inputs);
    assert!(
        findings.iter().any(|finding| {
            finding.starts_with("lane-denotes-nothing")
                && finding.contains("pfei_planted_missing_lane.sh")
        }),
        "the planted missing lane was not refused: {findings:?}"
    );
    assert!(
        findings.iter().any(|finding| {
            finding.starts_with("bead-denotes-nothing")
                && finding.contains("fln-pfei-planted-missing-bead")
        }),
        "the planted missing bead was not refused: {findings:?}"
    );

    let restored =
        extract_operational_referents(&root.join("AGENTS.md")).expect("the restored stream parses");
    let findings = judge_operational_referents(&root, &restored, &inputs);
    assert!(
        findings.is_empty(),
        "deleting only the planted referents must return the real document to silence: \
         {findings:?}"
    );
}

fn without_top_level_on(workflow: &str) -> String {
    let lines: Vec<&str> = workflow.lines().collect();
    let start = lines
        .iter()
        .position(|line| {
            !line.starts_with([' ', '\t'])
                && line
                    .split_once(':')
                    .is_some_and(|(key, _)| key.trim().trim_matches(['"', '\'']) == "on")
        })
        .expect("control needs ci.yml's top-level on key");
    let end = lines
        .iter()
        .enumerate()
        .skip(start + 1)
        .find(|(_, line)| {
            !line.trim().is_empty()
                && !line.trim_start().starts_with('#')
                && !line.starts_with([' ', '\t'])
        })
        .map_or(lines.len(), |(index, _)| index);
    let mut kept = Vec::new();
    kept.extend_from_slice(&lines[..start]);
    kept.extend_from_slice(&lines[end..]);
    kept.join("\n") + "\n"
}

#[test]
fn a_real_lane_requires_check_registration_ci_execution_and_a_reachable_trigger() {
    let root = workspace_root();
    let lane = "scripts/e2e/closure_audit.sh";
    let (_guard, planted) = doctored(|text| {
        text + "\nCI refuses a closure regression through scripts/e2e/closure_audit.sh.\n\
                CI refuses a dormant workflow through .github/workflows/ci.yml.\n"
    });
    let referents = extract_operational_referents(&planted).expect("the planted stream parses");
    let inputs = operational_inputs(&root);
    let baseline = judge_operational_referents(&root, &referents, &inputs);
    assert!(
        baseline.is_empty(),
        "the real closure-audit lane and ci workflow must be a clean positive control: {baseline:?}"
    );

    assert!(
        inputs.check_sh.contains(lane),
        "control needs the real check.sh registration"
    );
    let no_registration = OperationalInputs {
        check_sh: inputs
            .check_sh
            .replace(lane, "scripts/e2e/pfei_muted_registration.sh"),
        ci: inputs.ci.clone(),
        beads: inputs.beads.clone(),
    };
    let findings = judge_operational_referents(&root, &referents, &no_registration);
    assert!(
        findings
            .iter()
            .any(|finding| finding.starts_with("lane-not-registered")),
        "removing only the check.sh registration must be refused: {findings:?}"
    );

    let invocation = format!("./{lane}");
    assert!(
        inputs.ci.contains(&invocation),
        "control needs ci.yml's real lane execution"
    );
    let no_execution = OperationalInputs {
        check_sh: inputs.check_sh.clone(),
        ci: inputs
            .ci
            .replace(&invocation, "./scripts/e2e/pfei_muted_execution.sh"),
        beads: inputs.beads.clone(),
    };
    let findings = judge_operational_referents(&root, &referents, &no_execution);
    assert!(
        findings
            .iter()
            .any(|finding| finding.starts_with("lane-not-executed")),
        "removing only CI's execution must be refused: {findings:?}"
    );

    let unreachable = without_top_level_on(&inputs.ci);
    assert_ne!(
        trigger_reachability(&unreachable),
        TriggerReachability::Reachable,
        "the trigger mutant must actually make ci.yml unreachable"
    );
    let no_trigger = OperationalInputs {
        check_sh: inputs.check_sh,
        ci: unreachable,
        beads: inputs.beads,
    };
    let findings = judge_operational_referents(&root, &referents, &no_trigger);
    assert!(
        findings
            .iter()
            .any(|finding| finding.starts_with("lane-ci-unreachable"))
            && findings
                .iter()
                .any(|finding| finding.starts_with("workflow-never-fires")),
        "removing only the top-level trigger must redden both lane and workflow joins: \
         {findings:?}"
    );
}

// ------------------------------------------------------------------------------------------
// pfei R3/R5 — every still-unbound claim is declared; wording-only shrinkage is refused.
// ------------------------------------------------------------------------------------------

fn disclosed_reviewed_count() -> usize {
    let text = agents_md();
    let line = text
        .lines()
        .find(|line| line.contains("enforcement-census: live="))
        .expect("AGENTS.md's census disclosure");
    line.split_once("reviewed=")
        .and_then(|(_, rest)| {
            let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
            digits.parse().ok()
        })
        .unwrap_or_else(|| panic!("cannot read reviewed= from disclosure line: {line:?}"))
}

fn replace_disclosure_value(text: String, key: &str, before: usize, after: usize) -> String {
    let needle = format!("{key}={before}");
    assert_eq!(
        text.matches(&needle).count(),
        1,
        "control must change exactly the disclosure's {needle:?} field"
    );
    text.replacen(&needle, &format!("{key}={after}"), 1)
}

#[test]
fn a_new_unbound_claim_without_a_review_row_is_refused() {
    let (live, _, unbound, _) = disclosed_counts();
    let (_guard, path) = doctored(|text| {
        let text = replace_disclosure_value(text, "live", live, live + 1);
        let text = replace_disclosure_value(text, "unbound", unbound, unbound + 1);
        text + "\nA planted registry decoy: CI refuses every undeclared PFEI remainder.\n"
    });
    let (code, output) = run(Some(&path));
    assert_eq!(
        code, 1,
        "the missing review row must be a typed red:\n{output}"
    );
    assert!(
        output.contains("matches 0 reviewed-unwalked rows")
            && output.contains("undeclared PFEI remainder"),
        "the refusal must name the newly unreviewed claim: {output}"
    );
}

#[test]
fn a_claim_becoming_bound_makes_its_old_review_row_stale() {
    let (_, bound, unbound, _) = disclosed_counts();
    let needle = "documentation CI rejects wording stronger than the matrix permits";
    let (_guard, path) = doctored(|text| {
        assert_eq!(
            text.matches(needle).count(),
            1,
            "control needs the unique PFEI-U01 claim"
        );
        let text = text.replace(
            needle,
            &format!("{needle} through `scripts/agents_enforcement_census.py`"),
        );
        let text = replace_disclosure_value(text, "bound", bound, bound + 1);
        replace_disclosure_value(text, "unbound", unbound, unbound - 1)
    });
    let (code, output) = run(Some(&path));
    assert_eq!(code, 1, "a stale review row must be refused:\n{output}");
    assert!(
        output.contains("reviewed-unwalked PFEI-U01")
            && output.contains("matches 0 still-unbound claims"),
        "the stale row must be named, not silently retained: {output}"
    );
}

#[test]
fn a_seventeenth_reviewed_remainder_exceeds_the_deliberate_ceiling() {
    let (live, _, unbound, _) = disclosed_counts();
    let reviewed = disclosed_reviewed_count();
    let (_guard, path) = doctored(|text| {
        let text = replace_disclosure_value(text, "live", live, live + 1);
        let text = replace_disclosure_value(text, "unbound", unbound, unbound + 1);
        let text = replace_disclosure_value(text, "reviewed", reviewed, reviewed + 1);
        text + "\nA planted ceiling claim: CI refuses every seventeenth reviewed remainder.\n\
                > reviewed-unwalked PFEI-U17 :: CI refuses every seventeenth reviewed remainder \
                :: planted unique ceiling control\n"
    });
    let (code, output) = run(Some(&path));
    assert_eq!(code, 1, "allowance growth must be deliberate:\n{output}");
    assert!(
        output.contains("registry has 17 rows against ceiling 16"),
        "the ceiling refusal must state both populations: {output}"
    );
}

#[test]
fn softening_a_claim_lowering_counts_and_deleting_its_row_hits_the_independent_floor() {
    let (live, _, unbound, _) = disclosed_counts();
    let reviewed = disclosed_reviewed_count();
    let (_guard, path) = doctored(|text| {
        let softened = text.replace(
            "documentation CI rejects wording stronger than the matrix permits",
            "documentation CI records wording stronger than the matrix permits",
        );
        assert_ne!(softened, text, "control must soften the PFEI-U01 sentence");
        let without_row = softened
            .lines()
            .filter(|line| !line.contains("> reviewed-unwalked PFEI-U01 ::"))
            .collect::<Vec<_>>()
            .join("\n")
            + "\n";
        let text = replace_disclosure_value(without_row, "live", live, live - 1);
        let text = replace_disclosure_value(text, "unbound", unbound, unbound - 1);
        replace_disclosure_value(text, "reviewed", reviewed, reviewed - 1)
    });
    let (code, output) = run(Some(&path));
    assert_eq!(
        code, 2,
        "coordinated prose softening must hit the typed anti-softening floor:\n{output}"
    );
    assert!(
        output.contains("anti-softening floor") && output.contains("below the measured floor 33"),
        "the refusal must identify the independent floor, not a stale count: {output}"
    );
}
