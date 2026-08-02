//! The independence charter's claims, bound to what they point at.
//!
//! Two bindings live here, filed under two beads, because the charter makes two kinds of
//! claim about code it does not own: *where* something is (a line citation, bead
//! `franken_lean-checker-charter-line-citations-unbound-68ob`) and *whether* something is
//! enforced (a semantic-inventory classification, bead
//! `franken_lean-m5bl`). Both rot silently and
//! both rot toward claiming less than the build does.
//!
//! # Why this is the first test this crate has
//!
//! `fln-checker` began as a charter-only stub; its implementation now arrives in
//! bounded `franken_lean-gii` foundation slices. The charter is not inert prose — it
//! is the constitutional statement of what
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

/// One `cite <path>:<line> :: <construct>[ @@ <site>]` row of the charter's registry.
struct Citation {
    path: String,
    line: usize,
    construct: String,
    /// The item the cited line sits inside, for rows whose construct RECURS in its file.
    site: Option<String>,
}

fn registry(charter: &str) -> Vec<Citation> {
    charter
        .lines()
        .filter_map(|raw| {
            let rest = raw.trim_start().strip_prefix("//!")?.trim_start();
            let rest = rest.strip_prefix("cite ")?;
            let (locator, tail) = rest.split_once(" :: ")?;
            let (path, line) = locator.rsplit_once(':')?;
            let (construct, site) = match tail.split_once(" @@ ") {
                Some((construct, site)) => (construct, Some(site.trim().to_string())),
                None => (tail, None),
            };
            Some(Citation {
                path: path.to_string(),
                line: line.parse().ok()?,
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

/// The tolerance the containment check cannot see, closed.
///
/// `every_charter_citation_points_at_the_construct_it_names` asks only whether line N holds
/// construct C. Where C **recurs**, that is satisfied by ANY occurrence, so a shift can move
/// the citation onto a different site and stay green — the tolerance is the distance between
/// occurrences. AGENTS.md measured this exact shape: `0f2ae0ba` shifted four of its own
/// citations by 45 lines and only two of them reddened, because a wide region and a recurring
/// needle absorbed the other two.
///
/// Measured before building this: all six recurring rows here were still on their original
/// occurrence and inside their original item, so the tolerance was real and **unexercised**.
/// It is closed now rather than disclosed, because the next shift is the one nobody watches.
///
/// Scoped to recurring constructs DELIBERATELY. Where a construct occurs once, any shift
/// already makes the line stop containing it, so containment catches it first and a site
/// assertion could never fail — and a check that cannot fail is decoration that reads as
/// coverage.
fn site_drift(citation: &Citation, text: &str) -> Option<String> {
    let lines: Vec<&str> = text.lines().collect();
    let occurrences = lines
        .iter()
        .filter(|line| line.contains(&citation.construct))
        .count();
    if occurrences <= 1 {
        return None;
    }
    let Citation {
        path,
        line,
        construct,
        site,
    } = citation;
    let Some(declared) = site.as_deref() else {
        return Some(format!(
            "{path}:{line} cites `{construct}`, which occurs {occurrences} times in that file. \
             A citation to a recurring construct is satisfied by ANY of them, so a shift can \
             move it onto a different site and stay green. Name the item it sits inside: \
             `cite {path}:{line} :: {construct} @@ fn <name>`."
        ));
    };
    let actual = enclosing_item(&lines, *line);
    (actual != declared).then(|| {
        format!(
            "{path}:{line} declares it sits inside `{declared}`, but that line is inside \
             `{actual}`. `{construct}` occurs {occurrences} times in the file, so the line \
             still CONTAINS it and the containment check stays green — this is precisely the \
             tolerance that check cannot see. Re-derive the citation; do not relax this."
        )
    })
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
    for citation in &rows {
        let Citation {
            path,
            line,
            construct,
            ..
        } = citation;
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

        // A green above does NOT mean the citation points where it was written to point.
        assert!(
            site_drift(citation, &text).is_none(),
            "{}",
            site_drift(citation, &text).expect("asserted present immediately above")
        );
    }
}

/// The recurring-needle rule fires, and it is scoped so it cannot fire where it would be
/// decoration.
///
/// Driven over INJECTED text rather than the tree, for the reason `build_gate_governed_sets`
/// records: a rule whose real population is currently clean can never exercise its own
/// branches, so the checks that exist for the day something breaks are exactly the ones a
/// healthy tree cannot prove. All six real rows are correct today — which is why the cells
/// below are synthetic.
#[test]
fn a_recurring_needle_must_name_its_site_and_the_site_is_checked() {
    // Two occurrences of one construct, in two different functions. Line 6 is the second.
    let text = "\
fn first_home(&self) {
    let x = MARKER;
}

fn second_home(&self) {
    let y = MARKER;
}
";
    let cite = |line: usize, site: Option<&str>| Citation {
        path: "crates/fln-kernel/src/tc.rs".into(),
        line,
        construct: "MARKER".into(),
        site: site.map(str::to_string),
    };

    // The negative control FIRST: a correct row must be silent, or every cell below proves
    // nothing but that the function complains.
    assert!(
        site_drift(&cite(6, Some("fn second_home")), text).is_none(),
        "a row naming the site it really sits in must be accepted"
    );

    // A recurring construct with no site declared is refused, naming the occurrence count.
    let missing = site_drift(&cite(6, None), text).expect("an unsited recurring row must fail");
    assert!(
        missing.contains("occurs 2 times") && missing.contains("@@"),
        "the refusal must say why and how to repair it: {missing}"
    );

    // THE CASE THE CONTAINMENT CHECK CANNOT SEE: the citation has drifted onto the OTHER
    // occurrence. Line 2 still contains `MARKER`, so containment is green and only this fires.
    assert!(
        text.lines().nth(1).is_some_and(|l| l.contains("MARKER")),
        "the fixture must keep containment satisfied, or it tests the wrong refusal"
    );
    let drifted =
        site_drift(&cite(2, Some("fn second_home")), text).expect("a moved citation must fail");
    assert!(
        drifted.contains("fn first_home") && drifted.contains("fn second_home"),
        "the refusal must name both the declared and the actual site: {drifted}"
    );

    // SCOPING: a construct occurring once is left alone even with a wrong site, because
    // containment already catches any shift and a second check there could never fail.
    let unique = "fn only_home() {\n    let z = SOLO;\n}\n";
    assert!(
        site_drift(
            &Citation {
                path: "p".into(),
                line: 2,
                construct: "SOLO".into(),
                site: Some("fn something_else".into()),
            },
            unique
        )
        .is_none(),
        "a unique construct must not be subject to the site rule"
    );
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

/// How many names the charter declares SEMANTIC and deliberately leaves out of the rule.
///
/// Pinned, and equality both ways, because this is a **measured population** rather than a
/// shrinking allowance: a one-way floor would let a fourth unwalked declaration land quietly,
/// and a one-way ceiling would redden a correct repair. Moving this number is the point —
/// it forces whoever adds or removes an unenforced declaration to say so.
const REVIEWED_REMAINDER: usize = 3;

/// Every string literal in `src`, in order, with escapes and `\`-continuations consumed.
fn string_literals(src: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut chars = src.chars();
    while let Some(c) = chars.next() {
        if c != '"' {
            continue;
        }
        let mut literal = String::new();
        loop {
            match chars.next() {
                None | Some('"') => break,
                // Consumes `\"` and, just as importantly, the `\<newline>` continuations the
                // rationale strings use — a continuation must not be read as a literal ending.
                Some('\\') => {
                    chars.next();
                }
                Some(ch) => literal.push(ch),
            }
        }
        out.push(literal);
    }
    out
}

/// The rule's own inventory: `structure_guard::checks::CHECKER_SEMANTIC`, read as source text.
///
/// It is read rather than imported because `fln-checker` may not depend on `structure-guard`
/// — and must not: this crate's whole charter is about *not* sharing implementations. That
/// makes the parse the weak point, so the parse is defended rather than trusted. The array
/// declares its own cardinality as `[(&str, &str); N]`, and a `(name, why)` pair contributes
/// exactly two literals, so `2 * N` literals must be scanned. A parse that silently sees
/// nothing then fails as a broken scan instead of reporting an empty inventory that agrees
/// with an empty charter — the `98np R1` lesson, where a derived zero looked exactly like a
/// lane that governed nothing.
fn producer_inventory() -> (usize, Vec<String>) {
    const PRODUCER: &str = "tools/structure-guard/src/checks.rs";
    let text = std::fs::read_to_string(workspace_root().join(PRODUCER)).unwrap_or_else(|err| {
        panic!(
            "the rule at {PRODUCER} must be readable; this test establishes nothing without \
             it, so an unreadable producer is a failure and never a pass: {err}"
        )
    });
    let lines: Vec<&str> = text.lines().collect();
    let start = lines
        .iter()
        .position(|line| line.trim_start().starts_with("pub const CHECKER_SEMANTIC:"))
        .unwrap_or_else(|| {
            panic!(
                "{PRODUCER} no longer declares `pub const CHECKER_SEMANTIC`. If the inventory \
                 was renamed or made private, this binding is broken — repair it here rather \
                 than deleting it, or the charter goes back to describing the rule from memory."
            )
        });
    let end = lines[start..]
        .iter()
        .position(|line| line.trim() == "];")
        .map(|offset| start + offset)
        .unwrap_or_else(|| panic!("{PRODUCER}: CHECKER_SEMANTIC has no closing `];`"));

    let header = lines[start];
    let declared: usize = header
        .rsplit_once("; ")
        .and_then(|(_, rest)| rest.split(']').next())
        .and_then(|digits| digits.trim().parse().ok())
        .unwrap_or_else(|| panic!("{PRODUCER}: cannot read a cardinality from {header:?}"));

    let body = lines[start + 1..end].join("\n");
    let literals = string_literals(&body);
    assert_eq!(
        literals.len(),
        2 * declared,
        "{PRODUCER}: CHECKER_SEMANTIC declares {declared} entries, so {} string literals were \
         expected and {} were scanned. This is a broken parse, not a finding about the \
         inventory — fix the scan before reading anything into the sets below.",
        2 * declared,
        literals.len()
    );

    let names = literals.into_iter().step_by(2).collect();
    (declared, names)
}

/// One `semantic <name> :: walked|reviewed [reason]` row of the charter's registry.
fn semantic_registry(charter: &str) -> Vec<(String, String)> {
    charter
        .lines()
        .filter_map(|raw| {
            let rest = raw.trim_start().strip_prefix("//!")?.trim_start();
            let rest = rest.strip_prefix("semantic ")?;
            let (name, status) = rest.split_once(" :: ")?;
            let status = status.trim();
            let word = status.split_whitespace().next().unwrap_or_default();
            Some((name.trim().to_string(), word.to_string()))
        })
        .collect()
}

/// The charter's enforcement classification, bound to the rule that actually enforces it
/// (bead `franken_lean-m5bl`).
///
/// # The defect this exists for
///
/// The charter said `NOT ENFORCED. … a rule refusing Canonical::read_body /
/// from_canonical_bytes … does not exist, so that half remains a document.` Both names had
/// been in `FLN-STRUCT-037`'s inventory since `18b6d14b`, an **ancestor** of `a22c64f2` — the
/// commit that wrote the sentence, whose subject is "re-measure the two doctrine claims in
/// its charter, both of which outlived the work that satisfied them". It was false when
/// written, survived two later edits to the file, and `franken_lean-r0xu`'s closing judgement
/// contradicted it the whole time. Nothing could have noticed: the inventory was stated in
/// three places — the rule, a transcription in the seeded campaign, and this prose — with no
/// join between any two of them.
///
/// # Both directions, and why neither alone is enough
///
/// * a `walked` row absent from the rule is a **prohibition nobody enforces** — the charter
///   claiming more than the build does;
/// * a rule entry no row declares is **enforcement nobody can read** — the build refusing
///   something the constitutional document never mentions, which is how
///   `from_canonical_bytes_budgeted` sat enforced and undeclared;
/// * a `reviewed` row that *is* in the rule is the original defect exactly: a "not enforced"
///   claim that outlived its own enforcement landing.
#[test]
fn the_charter_and_the_rule_declare_the_same_semantic_inventory() {
    let charter = charter();
    let rows = semantic_registry(&charter);
    let (declared, produced) = producer_inventory();
    assert!(
        declared >= 12,
        "the rule declares only {declared} semantic items; it held twelve when this binding \
         was written, and a shrink is a decision that must be argued, not absorbed"
    );

    let mut walked: BTreeSet<String> = BTreeSet::new();
    let mut reviewed: BTreeSet<String> = BTreeSet::new();
    for (name, status) in &rows {
        match status.as_str() {
            "walked" => &mut walked,
            "reviewed" => &mut reviewed,
            other => panic!(
                "the charter's registry marks `{name}` as `{other}`, which is not a status this \
                 binding recognises. Use `walked` (in the rule) or `reviewed` (declared \
                 SEMANTIC and deliberately not in the rule, with the reason on the same line)."
            ),
        }
        .insert(name.clone());
    }
    assert_eq!(
        walked.len() + reviewed.len(),
        rows.len(),
        "the charter's registry names the same item twice; a duplicated row would let one \
         copy be repaired while the other kept making the stale claim"
    );

    let produced: BTreeSet<String> = produced.into_iter().collect();

    let claimed_not_enforced: Vec<&String> = walked.difference(&produced).collect();
    assert!(
        claimed_not_enforced.is_empty(),
        "the charter marks {claimed_not_enforced:?} `walked`, but they are not in \
         CHECKER_SEMANTIC. That is a prohibition this document claims and the build does not \
         enforce. Either add it to the rule, or change the row to `reviewed` with the reason \
         and raise REVIEWED_REMAINDER — do not delete the declaration."
    );

    // ORDER IS LOAD-BEARING, and getting it wrong made one of these assertions dead code.
    // `stale` and `enforced_not_declared` overlap: an item in `reviewed ∩ produced` is, unless
    // it is also duplicated into `walked`, necessarily in `produced - walked` too. Written the
    // other way round, `enforced_not_declared` fired first on every input that could reach
    // `stale`, so no mutant could ever kill the `stale` assertion and its careful message was
    // unreachable text. Checking the specific case before the general one makes both live —
    // the recurring "declared set subsumed by a broader rule in the same predicate" shape.
    let stale: Vec<&String> = reviewed.intersection(&produced).collect();
    assert!(
        stale.is_empty(),
        "the charter marks {stale:?} `reviewed` — declared SEMANTIC but deliberately outside \
         the rule — and the rule enforces them. This is the exact defect this test was built \
         for: a `NOT ENFORCED` claim that outlived its own enforcement landing, false for two \
         days inside a commit whose purpose was re-measuring it. Mark them `walked` and lower \
         REVIEWED_REMAINDER."
    );

    let enforced_not_declared: Vec<&String> = produced.difference(&walked).collect();
    assert!(
        enforced_not_declared.is_empty(),
        "CHECKER_SEMANTIC refuses {enforced_not_declared:?} inside fln-checker and the charter \
         declares nothing about them. Enforcement the constitutional document does not mention \
         is enforcement nobody can read — add a `semantic <name> :: walked` row and describe \
         the item in the SEMANTIC sections above."
    );

    assert_eq!(
        reviewed.len(),
        REVIEWED_REMAINDER,
        "the charter declares {} names SEMANTIC-but-unwalked ({reviewed:?}) and this binding \
         pins the remainder at {REVIEWED_REMAINDER}. Equality both ways is deliberate: a \
         growing remainder must be disclosed by whoever grows it, and a shrinking one must be \
         claimed by whoever repaired it.",
        reviewed.len()
    );
}
