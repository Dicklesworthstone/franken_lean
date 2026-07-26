//! The join between AGENTS.md §18's mandated mutant list and the tests that kill them.
//!
//! # What this is for
//!
//! AGENTS.md §18 names five seeded defects and requires that each "must each be *killed* by
//! a named test; a surviving critical mutant blocks the gate." Measured on 2026-07-26 by
//! planting all three that can be planted, the rig is in good shape: three of three
//! applicable mutants die, two of them against tests that quote the policy verbatim in a
//! `MANDATED MUTANT` comment. **This guard is not evidence that the mutation rig is broken.
//! It is not.** What was missing is the *join*: nothing read §18's list and asked whether
//! each name was accounted for.
//!
//! That gap has a shape and a direction. The two names that do **not** apply yet —
//! `leaked transaction assignment` (Athanor's `ElabTxn`) and `stale cache hit accepted`
//! (the Ledger) — are the dangerous ones, because `fln-elab` and `fln-ledger` are
//! charter-only stubs today. When they land, the reminder to seed their mutants has to
//! *already exist* or it never fires. That is bead
//! `fln-term-plane-population-differential-wv4u`'s R4 applied here: the enforcement law
//! lands **with** the rig rather than after it.
//!
//! # How the two directions work
//!
//! A name is accounted for if it is **marked** by a `MANDATED MUTANT` comment, or if it is
//! **declared not-yet-seeded** against a crate that still says `Stub crate: charter only.`
//! in its root. Both halves are checked both ways:
//!
//! * a name that is neither marked nor declared fails — the list cannot grow silently;
//! * a declared name whose crate has **stopped being a stub** fails, which is the reminder
//!   firing at exactly the moment the subsystem arrives;
//! * a declared name that has since been marked fails, so the remainder shrinks with the
//!   repair instead of outliving it.
//!
//! # The two traps this guard is built to avoid, both already paid for once
//!
//! **The guard's own text is inside its search space** (`fln-8zsq`). This file necessarily
//! contains the marker pattern and two of the five names, so a naive scan would find its
//! own assertions and stay green after every real marker was deleted.
//!
//! **Excluding only yourself is not enough** (`franken_lean-2ki4`, whose probe matched a
//! literal living inside another guard's assertion). So the exclusion here is uniform
//! rather than self-referential: **every** scanned file is cut at its first source-reading
//! construct, because a file that reads source at test time is a guard from that point on,
//! and a guard's assertions are claims about markers rather than markers. This file is cut
//! by the same rule as every other, not by its own path.
//!
//! That rule is safe for the real markers only because the files carrying them —
//! `crates/fln-kernel/tests/k1_judgments.rs` and `crates/fln-unsafe-abi/src/tests.rs` —
//! read no source at all, so their cut is the whole file. `the_exclusion_rule_does_not_hide_a_real_marker`
//! pins that, so the rule cannot start swallowing markers unnoticed.
//!
//! **One honest limitation, stated because it is the kind of thing this table is about.**
//! A marker *is* a comment, so unlike the prior art this scan cannot strip comments to
//! separate "code that does X" from "prose describing X". Prose outside a guard body that
//! reproduced the exact marker form would be counted. The cut rule removes the place such
//! prose actually lives; it does not make the confusion unrepresentable.

#![forbid(unsafe_code)]

// Declared first, deliberately: this constant is itself the earliest source-reading token in
// this file, so the uniform cut below excludes everything after it — including the pattern,
// the allowance, and every assertion. The exclusion applies to this file through the same
// rule as every other, which is the `franken_lean-2ki4` correction.
const SOURCE_READING: [&str; 2] = ["include_str!", "read_to_string"];

/// The marker a killing test carries to claim one of §18's names.
const MARKER: &str = "MANDATED MUTANT (AGENTS testing policy: \"";

/// The decoy, and why a decoy is load-bearing rather than cute.
///
/// The first version of this file had NO literal marker in it: [`MARKER`] escapes its inner
/// quote, so the source text reads `policy: \"` and never matches the runtime needle. That
/// made `this_guards_own_text_is_outside_its_search_space` **vacuous** — it asserted this
/// file yields no markers, which was true whether or not the exclusion worked, and a planted
/// mutant that deleted the exclusion entirely SURVIVED. That is `fln-8zsq`'s defect
/// reproduced one level up: a check that passes for a reason unrelated to the property.
///
/// So the line below is the exact marker form, verbatim and unescaped, sitting after the
/// cut. It names a sentinel rather than one of §18's five, so if the exclusion ever stops
/// excluding, this file contributes a marker for a name that does not exist and the
/// self-check fails loudly instead of quietly widening the search space.
///
/// MANDATED MUTANT (AGENTS testing policy: "decoy-sentinel-never-a-real-mandated-name")
const DECOY_SENTINEL: &str = "decoy-sentinel-never-a-real-mandated-name";

/// Names whose subsystem does not exist yet, each against the crate that must still be a
/// stub for the excuse to hold. When that crate stops being a stub, this entry fails and the
/// person landing the subsystem is told to seed the mutant — which is the entire point.
const NOT_YET_SEEDED: [(&str, &str); 2] = [
    ("leaked transaction assignment", "fln-elab"),
    ("stale cache hit accepted", "fln-ledger"),
];

/// The sentence in a crate root that declares it unimplemented.
const STUB_DECLARATION: &str = "Stub crate: charter only.";

// ---------------------------------------------------------------------------
// Deriving the obligation from AGENTS.md, never transcribing it
// ---------------------------------------------------------------------------

/// §18's five names, read out of AGENTS.md at test time.
///
/// Derived rather than listed because a transcription is correct the day it is written and
/// silently wrong afterwards — bead `franken_lean-869w` hand-copied ten G0 questions and all
/// ten were wrong, discovered only when someone finally derived them. A guard whose
/// obligation is a copy of the obligation enforces the copy.
fn mandated_names(agents_md: &str) -> Vec<String> {
    let anchor = "Seeded defects (";
    let start = agents_md.find(anchor).expect(
        "AGENTS.md must state the seeded-defect list; if that sentence moved, this \
                 guard is enforcing an obligation that no longer exists and must be updated \
                 rather than quietly passing",
    ) + anchor.len();
    let rest = &agents_md[start..];
    let end = rest
        .find(')')
        .expect("the seeded-defect list must be a parenthesised list");
    rest[..end]
        .split(',')
        .map(|name| name.trim().to_string())
        .filter(|name| !name.is_empty())
        .collect()
}

// ---------------------------------------------------------------------------
// Scanning, with every guard body cut out
// ---------------------------------------------------------------------------

/// The part of `source` that is production text rather than a guard's assertions.
///
/// Cut at the first source-reading construct: from there on the file is reasoning *about*
/// source, and a claim about a marker is not a marker.
fn before_any_guard(source: &str) -> &str {
    let cut = SOURCE_READING
        .iter()
        .filter_map(|needle| source.find(needle))
        .min()
        .unwrap_or(source.len());
    &source[..cut]
}

fn rust_files(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            if path.file_name().is_some_and(|n| n == "target") {
                continue;
            }
            rust_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
}

/// Every `(name, file)` pair claimed by a marker in production text.
fn markers(root: &std::path::Path) -> Vec<(String, String)> {
    let mut files = Vec::new();
    rust_files(&root.join("crates"), &mut files);
    files.sort();
    let mut found = Vec::new();
    for path in files {
        let Ok(source) = std::fs::read_to_string(&path) else {
            continue;
        };
        let rel = path
            .strip_prefix(root)
            .unwrap_or(&path)
            .to_string_lossy()
            .into_owned();
        let mut rest = before_any_guard(&source);
        while let Some(at) = rest.find(MARKER) {
            let tail = &rest[at + MARKER.len()..];
            if let Some(close) = tail.find('"') {
                found.push((tail[..close].to_string(), rel.clone()));
            }
            rest = &rest[at + MARKER.len()..];
        }
    }
    found
}

fn workspace_root() -> std::path::PathBuf {
    fln_conformance::pin::workspace_root()
}

fn agents_md() -> String {
    std::fs::read_to_string(workspace_root().join("AGENTS.md")).expect("AGENTS.md is readable")
}

/// Whether `krate` still declares itself unimplemented.
fn is_stub(root: &std::path::Path, krate: &str) -> bool {
    std::fs::read_to_string(root.join("crates").join(krate).join("src/lib.rs"))
        .map(|source| source.contains(STUB_DECLARATION))
        .unwrap_or(false)
}

// ---------------------------------------------------------------------------
// The law
// ---------------------------------------------------------------------------

/// Every name §18 mandates is either killed by a marked test or declared not-yet-seeded
/// against a crate that is still a stub — and the declaration expires by itself.
#[test]
fn every_mandated_mutant_is_killed_by_a_marked_test_or_declared_not_yet_seeded() {
    let root = workspace_root();
    let names = mandated_names(&agents_md());
    assert!(
        names.len() >= 5,
        "parsed only {} seeded-defect names out of AGENTS.md; a parse that silently returns \
         a short list would make this whole guard vacuous: {names:?}",
        names.len()
    );

    let found = markers(&root);
    let marked: Vec<&str> = found.iter().map(|(name, _)| name.as_str()).collect();
    let mut failures: Vec<String> = Vec::new();

    for name in &names {
        let is_marked = marked.contains(&name.as_str());
        let declared = NOT_YET_SEEDED.iter().find(|(n, _)| n == name);
        match (is_marked, declared) {
            (true, None) => {}
            (false, Some((_, krate))) if is_stub(&root, krate) => {}
            (false, Some((_, krate))) => failures.push(format!(
                "`{name}` is declared not-yet-seeded because `{krate}` was a stub, and \
                 `{krate}` is no longer a stub. THIS IS THE REMINDER: the subsystem has \
                 landed, so seed the mutant, give it a test carrying the {MARKER}{name}\") \
                 marker, and drop this entry from NOT_YET_SEEDED"
            )),
            (true, Some((_, krate))) => failures.push(format!(
                "`{name}` is BOTH marked by a test and still declared not-yet-seeded against \
                 `{krate}` — the declaration outlived the defect it recorded and must be \
                 removed, or the remainder stops shrinking"
            )),
            (false, None) => failures.push(format!(
                "`{name}` is mandated by AGENTS.md §18 and nothing accounts for it: no test \
                 carries the {MARKER}{name}\") marker, and it is not declared not-yet-seeded. \
                 Either seed and mark it, or declare it against the stub crate whose absence \
                 excuses it"
            )),
        }
    }

    assert!(
        failures.is_empty(),
        "{} of {} mandated mutants are unaccounted for:\n  {}",
        failures.len(),
        names.len(),
        failures.join("\n  ")
    );

    println!(
        "mandated_mutants: {} of {} §18 names killed by a marked test; {} declared \
         not-yet-seeded against stub crates. Declarations expire automatically when their \
         crate stops being a stub. This counts MARKERS, not kills - that three of three \
         applicable mutants actually die was established by planting them, and is not \
         re-established by this run.",
        names.len() - NOT_YET_SEEDED.len(),
        names.len(),
        NOT_YET_SEEDED.len()
    );
}

/// The exclusion must not be self-exclusion, and it must be shown to work on this file.
///
/// If the cut rule breaks, this file's own `MARKER` constant and `NOT_YET_SEEDED` entries
/// become "markers" and the law above passes while every real marker is gone. So the check
/// is that this file contributes **zero** markers, which fails loudly the moment the
/// exclusion stops excluding.
#[test]
fn this_guards_own_text_is_outside_its_search_space() {
    let found = markers(&workspace_root());
    let mine: Vec<&(String, String)> = found
        .iter()
        .filter(|(_, file)| file.ends_with("mandated_mutants.rs"))
        .collect();
    assert!(
        mine.is_empty(),
        "this guard matched its own text as if it were a marker ({mine:?}) — the exclusion is \
         broken and the law above is checking its own assertions. The expected match here is \
         `{DECOY_SENTINEL}`, planted below the cut precisely so this failure is reachable"
    );
    // The decoy must actually BE in this file, or the assertion above is vacuous again — the
    // exact way the first version of this test failed to test anything.
    let own = std::fs::read_to_string(
        workspace_root().join("crates/fln-conformance/tests/mandated_mutants.rs"),
    )
    .expect("this guard can read itself");
    assert!(
        own.contains(&format!("{MARKER}{DECOY_SENTINEL}\")")),
        "the decoy marker is gone from this file, so the exclusion has nothing to remove and \
         the check above proves nothing"
    );
    assert!(
        !found.is_empty(),
        "the scan found no markers anywhere, which means it is broken rather than that the \
         tree is clean — a scan that can only return empty proves nothing"
    );
}

/// The uniform cut must not swallow a real marker.
///
/// The rule is only safe because the files carrying markers read no source. If one of them
/// grows an `include_str!` above its markers, the law above would silently report those
/// names unaccounted. This pins the property rather than the current file contents.
#[test]
fn the_exclusion_rule_does_not_hide_a_real_marker() {
    let root = workspace_root();
    let mut files = Vec::new();
    rust_files(&root.join("crates"), &mut files);
    let mut hidden = Vec::new();
    for path in files {
        let Ok(source) = std::fs::read_to_string(&path) else {
            continue;
        };
        if path.ends_with("mandated_mutants.rs") {
            continue; // this file's occurrences are assertions, and that is the point
        }
        let visible = before_any_guard(&source).matches(MARKER).count();
        let total = source.matches(MARKER).count();
        if total > visible {
            hidden.push(format!(
                "{}: {} of {} markers sit after a source-reading construct and are invisible \
                 to the law",
                path.strip_prefix(&root).unwrap_or(&path).to_string_lossy(),
                total - visible,
                total
            ));
        }
    }
    assert!(
        hidden.is_empty(),
        "the cut rule is hiding real markers, so the law is weaker than it reads:\n  {}",
        hidden.join("\n  ")
    );
}

/// The cut itself, tested directly on synthetic text rather than only through its effect.
///
/// The self-check above needs the decoy to be reachable; this needs nothing but the function,
/// so the two fail independently. A marker after a source-reading construct is a guard's
/// claim about a marker and must not count as one.
#[test]
fn the_cut_removes_everything_from_the_first_source_reading_construct_onward() {
    let production_only = "// MANDATED MUTANT (AGENTS testing policy: \"a\")\nfn t() {}\n";
    assert_eq!(
        before_any_guard(production_only),
        production_only,
        "a file that reads no source must be searched whole"
    );

    let guarded = "// MANDATED MUTANT (AGENTS testing policy: \"a\")\n\
                   let s = include_str!(\"x.rs\");\n\
                   // MANDATED MUTANT (AGENTS testing policy: \"b\")\n";
    let visible = before_any_guard(guarded);
    assert_eq!(visible.matches(MARKER).count(), 1, "{visible:?}");
    assert!(
        visible.contains("\"a\")") && !visible.contains("\"b\")"),
        "the cut must keep what precedes the guard and drop what follows: {visible:?}"
    );

    // read_to_string counts too, and the EARLIEST construct wins even when it comes second
    // in the needle list — otherwise the cut depends on declaration order.
    let by_read =
        "x\nlet s = read_to_string(p);\n// MANDATED MUTANT (AGENTS testing policy: \"c\")\n";
    assert_eq!(before_any_guard(by_read).matches(MARKER).count(), 0);
}

/// The derivation must read AGENTS.md's words, not a paraphrase of them.
#[test]
fn the_names_come_from_agents_md_and_a_short_parse_is_refused() {
    let names = mandated_names(&agents_md());
    assert!(
        names.iter().any(|n| n == "skipped positivity check")
            && names.iter().any(|n| n == "dropped retain"),
        "the parse lost names it must contain: {names:?}"
    );
    // A list that is not parenthesised, or an anchor that moved, must not degrade to a
    // shorter list that this guard would then enforce as if it were complete.
    let truncated = mandated_names("Seeded defects (only one thing) must each be killed");
    assert_eq!(truncated, vec!["only one thing"]);
    let synthetic = mandated_names("Seeded defects (a, b, c) must each be killed");
    assert_eq!(synthetic, vec!["a", "b", "c"], "the split must be total");
}
