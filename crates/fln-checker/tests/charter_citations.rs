//! The independence charter's line citations, bound to what they point at
//! (bead `franken_lean-checker-charter-line-citations-unbound-68ob`).
//!
//! # Why this is the first test this crate has
//!
//! `fln-checker` is a charter-only stub: its implementation arrives with `franken_lean-gii`.
//! But the charter is not inert prose — it is the constitutional statement of what
//! "independent" means for the second engine of the dual-engine claim, written deliberately
//! *before* any implementation so it cannot be back-derived from whatever the first one
//! happened to do. Its authority rests on 33 line numbers across six files in five crates that
//! it does not control, and until this test existed **nothing bound a single one of them** —
//! in a crate with no `tests/` directory, so nothing *could* have.
//!
//! That is not a hypothetical. `witness.rs:479` was claim row `B3-INDEPENDENT-CHECKER`'s
//! evidence line — the row recording that this very charter had been corrected from "a 6-line
//! charter stub" to 149 lines. Commit `f39eaa2c` inserted 25 lines above it; the content moved
//! to line 500, and line 479 came to hold `state: ClaimState::Targeted,` from a *different*
//! row. Structurally identical text, plausible to a spot-check, silently wrong. The registry
//! this test reads now cites line 496 by the row's `id:`, which is a stabler anchor than its
//! prose.
//!
//! # The shape, and why it is not a third copy
//!
//! The charter carries the registry; this test **parses** it. Transcribing the pairs here would
//! reproduce the very defect — a second list, free to drift from the first. So the registry is
//! the single source, and a citation can only be repaired by editing the charter.
//!
//! Both directions are checked, plus conservation:
//!
//! * **binding** — every registry row's cited line must contain its named construct;
//! * **conservation** — every `file.rs:NNN` the charter's prose mentions must be covered by a
//!   registry row, so a new citation cannot be added to the prose and left unbound. Without
//!   this the registry could under-cover the document while looking complete, which is the
//!   `fln-8zsq` lesson: scope an assertion to the site that must carry the evidence.

#![forbid(unsafe_code)]

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
        .to_path_buf()
}

fn charter() -> String {
    std::fs::read_to_string(workspace_root().join("crates/fln-checker/src/lib.rs"))
        .expect("the charter must be readable")
}

/// One `cite <path>:<line> :: <construct>` row of the charter's registry.
struct Citation {
    path: String,
    line: usize,
    construct: String,
}

fn registry(charter: &str) -> Vec<Citation> {
    charter
        .lines()
        .filter_map(|raw| {
            let rest = raw.trim_start().strip_prefix("//!")?.trim_start();
            let rest = rest.strip_prefix("cite ")?;
            let (locator, construct) = rest.split_once(" :: ")?;
            let (path, line) = locator.rsplit_once(':')?;
            Some(Citation {
                path: path.to_string(),
                line: line.parse().ok()?,
                construct: construct.trim().to_string(),
            })
        })
        .collect()
}

#[test]
fn every_charter_citation_points_at_the_construct_it_names() {
    let charter = charter();
    let rows = registry(&charter);
    assert!(
        rows.len() >= 10,
        "parsed only {} registry row(s); a parse that cannot see the registry reports a false \
         clean rather than an uncited charter",
        rows.len()
    );

    let root = workspace_root();
    for Citation {
        path,
        line,
        construct,
    } in &rows
    {
        let read = std::fs::read_to_string(root.join(path));
        assert!(
            read.is_ok(),
            "the charter cites {path}, which is unreadable: {:?}",
            read.as_ref().err()
        );
        let text = read.expect("asserted readable immediately above");
        let lines: Vec<&str> = text.lines().collect();
        assert!(
            *line >= 1 && *line <= lines.len(),
            "the charter cites {path}:{line}, but that file has {} lines",
            lines.len()
        );
        let actual = lines[line - 1];
        assert!(
            actual.contains(construct.as_str()),
            "the charter cites {path}:{line} for `{construct}`, but that line reads:\n  \
             {}\n\nA line number is a claim that rots the moment anyone inserts a line above \
             it, and this is the check that notices. Find where `{construct}` moved to and \
             update the registry in crates/fln-checker/src/lib.rs — do NOT relax this test, and \
             do not assume the neighbouring line is close enough: witness.rs:479 stayed \
             plausible for hours after it stopped being correct.",
            actual.trim()
        );
    }
}

#[test]
fn no_citation_in_the_charter_prose_escapes_the_registry() {
    let charter = charter();
    let covered: BTreeSet<(String, usize)> = registry(&charter)
        .into_iter()
        .map(|c| {
            (
                c.path.rsplit('/').next().unwrap_or(&c.path).to_string(),
                c.line,
            )
        })
        .collect();

    // Every `<file>.rs:<n>` the prose mentions, excluding the registry's own rows.
    let mut prose: BTreeSet<(String, usize)> = BTreeSet::new();
    for raw in charter.lines() {
        let Some(comment) = raw.trim_start().strip_prefix("//!") else {
            continue;
        };
        if comment.trim_start().starts_with("cite ") {
            continue;
        }
        for (idx, _) in comment.match_indices(".rs:") {
            let head: String = comment[..idx]
                .chars()
                .rev()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect::<Vec<_>>()
                .into_iter()
                .rev()
                .collect();
            let tail: String = comment[idx + 4..]
                .chars()
                .take_while(char::is_ascii_digit)
                .collect();
            if head.is_empty() || tail.is_empty() {
                continue;
            }
            // Two kinds of prose citation deliberately do NOT resolve, and each must SAY so
            // rather than be quietly skipped:
            //   `(historical)` — a location as it was before some named commit, cited to
            //       narrate a defect. Requiring it to resolve would demand that the past
            //       still be true.
            //   `(foreign)` — a line in a file this charter does not own, recorded so the
            //       gap is visible, whose binding belongs to that file's owner.
            // An UNMARKED citation is a real one and must be registered. This is the
            // `fln-8zsq` trap met head-on: the paragraphs explaining this defect are inside
            // the search space of the check for it, and the first version of this test failed
            // on its own narration — correctly.
            let trailer = &comment[idx + 4 + tail.len()..];
            let trailer = trailer.trim_start();
            if trailer.starts_with("(historical)") || trailer.starts_with("(foreign)") {
                continue;
            }
            if let Ok(line) = tail.parse::<usize>() {
                prose.insert((format!("{head}.rs"), line));
            }
        }
    }

    let uncovered: Vec<_> = prose.difference(&covered).collect();
    assert!(
        uncovered.is_empty(),
        "the charter's prose cites {uncovered:?}, which the citation registry does not cover. \
         An uncovered citation is exactly the state bead \
         franken_lean-checker-charter-line-citations-unbound-68ob was filed for: a line number \
         nothing checks, in a crate that had no tests. Add a `cite <path>:<line> :: <construct>` \
         row naming what that line holds.\n\
         Registry covers: {covered:?}"
    );
}
