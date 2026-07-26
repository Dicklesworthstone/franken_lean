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

// ---------------------------------------------------------------------------
// From a marker to an actual KILL — the half the guard above cannot reach
// ---------------------------------------------------------------------------
//
// Everything above joins §18's list to a *marker*. A marker is a comment: a test could be
// gutted while keeping it and every check above stays green. That remaining gap was this
// bead's own honest disclosure ("THE GUARD CHECKS MARKERS, NOT KILLS"), and closing it needs
// two things that must land together, because either alone is the defect again:
//
//   * a **campaign** that actually plants each mutant and watches the named test die
//     (`the_mandated_mutants_are_planted_and_their_killers_die`, `#[ignore]`d — it edits
//     source, so it must never run by accident); and
//   * a **receipt** binding that measurement to the exact text it was measured against, so
//     the kill expires by itself when either half moves
//     (`the_recorded_kills_still_describe_this_tree`, which runs in ordinary `cargo test`).
//
// The receipt is the load-bearing part, and it is `franken_lean-p6x1`'s shape reused: there,
// the corpus-matrix receipt is keyed by the Reference pin, so advancing `SUITE.lock` expires
// the observation *mechanically* rather than by anyone remembering. Here the key is a digest
// over the mutated production site and the killer bodies, which is the same move against a
// different clock — the thing that can silently invalidate a kill is not a pin, it is an edit
// to either side of it.
//
// **What this still does not earn.** A campaign run is one measurement at one commit on one
// host, class `bounded_model` — the same class AGENTS.md gives the corpus matrix, and for the
// same reason. It is not a per-commit mutation gate: what runs per commit is the *retention*
// check, which proves the recorded kill still describes this tree, not that the mutant dies
// today. Those are different claims and stacking them does not make one.

/// One killing test, named the way libtest names it.
struct Killer {
    /// The exact libtest path, which is what `--exact` matches. Not the bare fn name:
    /// `fln-unsafe-abi`'s killers live in a `tests` module and answer to `tests::…`, and a
    /// filter that matches nothing exits **0** — a vacuum this campaign would otherwise
    /// report as a clean control run.
    path: &'static str,
    /// The bare fn name, used to extract the body the receipt is bound to.
    func: &'static str,
    /// The file defining it, which must also carry this mutant's marker.
    file: &'static str,
    /// A substring the failure must contain when the mutant is planted.
    ///
    /// Dying is not enough; dying *for the right reason* is the claim. Measured live on
    /// 2026-07-26: with positivity skipped, the bad block is still **rejected** — for
    /// "block declares 0 recursors" — and only the pinned-message assertion notices the
    /// substitution. A campaign that accepted any non-zero exit would have scored that
    /// mutant killed by a test that had stopped testing positivity at all.
    expect: &'static str,
}

/// One mandated mutant, as a plantable edit plus the tests that must die under it.
struct Plant {
    /// Must equal one of §18's names, checked against the derived list rather than trusted.
    name: &'static str,
    /// Repo-relative production file.
    file: &'static str,
    /// The exact production text to replace. Required to occur **exactly once** in `file`
    /// (`every_plant_still_targets_a_live_production_site`), so this is also the tripwire
    /// that fires when the site moves, is duplicated, or is deleted.
    find: &'static str,
    /// The mutation.
    replace: &'static str,
    /// `cargo test -p <package>`.
    package: &'static str,
    /// The target selector, e.g. `["--test", "k1_judgments"]` or `["--lib"]`.
    target: &'static [&'static str],
    killers: &'static [Killer],
}

/// The three mandated mutants that can be planted today.
///
/// The two absent names are not omissions: `leaked transaction assignment` and
/// `stale cache hit accepted` are in [`NOT_YET_SEEDED`] because their subsystems are
/// charter-only stubs, and `no_plant_exists_for_a_name_that_cannot_be_seeded_yet` refuses a
/// recipe for either — a plant against a stub could only ever be theatre.
const PLANTS: &[Plant] = &[
    Plant {
        name: "skipped positivity check",
        file: "crates/fln-kernel/src/admit.rs",
        // Short-circuiting the recursive-occurrence test makes `check_positivity` return
        // `Ok(())` for every argument, which is precisely "skipped".
        find: "if !self.mentions_block(&t) {",
        replace: "if true {",
        package: "fln-kernel",
        target: &["--test", "k1_judgments"],
        killers: &[
            Killer {
                path: "kr606_negative_occurrences_are_rejected",
                func: "kr606_negative_occurrences_are_rejected",
                file: "crates/fln-kernel/tests/k1_judgments.rs",
                expect: "the rejection must be the KR-606 positivity judgment",
            },
            Killer {
                path: "kr608_positivity_is_enforced_through_the_translation",
                func: "kr608_positivity_is_enforced_through_the_translation",
                file: "crates/fln-kernel/tests/k1_judgments.rs",
                expect: "the rejection must be the KR-606 positivity judgment on the \
                         translated block",
            },
        ],
    },
    Plant {
        name: "inverted universe condition",
        file: "crates/fln-kernel/src/admit.rs",
        // KR-604 with the sense of the universe fit reversed: exactly the "inverted
        // condition" §18 names, not a deletion of the check.
        find: "if !(self.result_level.is_geq(level) || self.result_level.is_zero()) {",
        replace: "if self.result_level.is_geq(level) || self.result_level.is_zero() {",
        package: "fln-kernel",
        target: &["--test", "k1_judgments"],
        killers: &[Killer {
            path: "kr604_oversized_constructor_fields_are_rejected",
            func: "kr604_oversized_constructor_fields_are_rejected",
            file: "crates/fln-kernel/tests/k1_judgments.rs",
            expect: "the rejection must be the KR-604 universe judgment",
        }],
    },
    Plant {
        name: "dropped retain",
        file: "crates/fln-unsafe-abi/src/rc.rs",
        // `inc_ref_n` returns before incrementing: the retain is dropped on every path.
        find: "    if !shadow::check_rc_target(o as usize, \"inc_ref_n\") {",
        replace: "    if true {",
        package: "fln-unsafe-abi",
        target: &["--lib"],
        killers: &[Killer {
            path: "tests::rc_balance_property_random_graphs",
            func: "rc_balance_property_random_graphs",
            file: "crates/fln-unsafe-abi/src/tests.rs",
            expect: "del on reserved/poisoned tag",
        }],
    },
];

/// The receipt schema.
///
/// `head_commit` is the commit the campaign ran **against**, recorded because AGENTS.md's
/// standing habit until `vdi4` closes is to record the hash a measurement was re-derived at.
/// It is deliberately not the commit that *lands* the receipt — that hash cannot exist yet
/// when the run happens — and the retention check does not read it. What binds a row to a
/// tree is `site_digest` and `killer_digest`; `head_commit` is provenance, and it is only
/// worth recording because the campaign refuses to run from a throwaway commit that `main`
/// could never reach.
const KILL_RECEIPT_SCHEMA: &str = "fln.mandated-mutant-kill-receipt/1";
const KILL_RECEIPT_BEAD: &str = "fln-mandated-mutant-join-unwatched-uagk";

fn kill_receipt_path(root: &std::path::Path) -> std::path::PathBuf {
    root.join("crates/fln-conformance/evidence/mandated_mutants/kills.jsonl")
}

// ---------------------------------------------------------------------------
// The two digests a receipt is bound to
// ---------------------------------------------------------------------------

fn hex(bytes: &[u8]) -> String {
    fln_hash::domain::hash(fln_hash::domain::Domain::Fixture, bytes).to_hex()
}

/// The mutated site: the file path and the exact text the plant replaces.
///
/// Binding the path as well as the text means moving the anchor to another file invalidates
/// the kill even if the text is byte-identical there.
fn site_digest(plant: &Plant) -> String {
    let mut preimage = Vec::new();
    preimage.extend_from_slice(plant.file.as_bytes());
    preimage.push(0);
    preimage.extend_from_slice(plant.find.as_bytes());
    preimage.push(0);
    preimage.extend_from_slice(plant.replace.as_bytes());
    hex(&preimage)
}

/// The body of a `fn`, from its signature line to the closing brace at the same indent.
///
/// Brace *counting* is wrong here: these bodies contain format strings like `{verdict:?}`,
/// and a lone `{` inside a string literal would desynchronise a counter. Matching the
/// closing brace by indentation needs no lexer and fails loudly rather than silently
/// returning a truncated body — a short body would weaken the digest exactly where it is
/// supposed to be strict.
fn fn_body(source: &str, func: &str) -> Option<String> {
    let needle = format!("fn {func}(");
    let at = source.find(&needle)?;
    let line_start = source[..at].rfind('\n').map(|i| i + 1).unwrap_or(0);
    let indent = &source[line_start..at];
    if !indent.chars().all(|c| c == ' ' || c == '\t') {
        // `pub fn`, `async fn`, a trailing comment — anything but plain indentation means
        // the closing-brace rule below is not the right rule for this item.
        return None;
    }
    let closing = format!("\n{indent}}}\n");
    let end = source[at..].find(&closing)? + at + closing.len();
    Some(source[line_start..end].to_string())
}

/// Every killer body for a plant, concatenated in declaration order.
///
/// This is what makes gutting a marked test fail: the marker survives an edit, the digest
/// does not.
fn killer_digest(root: &std::path::Path, plant: &Plant) -> String {
    let mut preimage = Vec::new();
    for killer in plant.killers {
        let source = std::fs::read_to_string(root.join(killer.file))
            .unwrap_or_else(|error| panic!("{} is readable: {error}", killer.file));
        let body = fn_body(&source, killer.func).unwrap_or_else(|| {
            panic!(
                "`fn {}(` was not found in {} with a closing brace at its own indentation. \
                 The killer this mutant is joined to cannot be located, so no digest can be \
                 computed and the kill cannot be re-bound — find where it moved to and \
                 update PLANTS rather than deleting the entry",
                killer.func, killer.file
            )
        });
        preimage.extend_from_slice(killer.path.as_bytes());
        preimage.push(0);
        preimage.extend_from_slice(body.as_bytes());
        preimage.push(0);
    }
    hex(&preimage)
}

/// One field out of a receipt row.
///
/// A free function with its own test rather than a closure inside the retention check,
/// because the first version was off by one — it skipped the value's opening quote and
/// every row-match failed. That fault was *safe* (the guard refused rather than passed),
/// but the same slip in the other direction would have made the retention check compare
/// `None` against `None` and go green on any receipt at all. A parser this guard's verdict
/// depends on is not allowed to be untested.
fn receipt_field(row: &str, key: &str) -> Option<String> {
    // `"key":` is a quote, the key, then a quote and a colon.
    let at = row.find(&format!("\"{key}\":"))? + key.len() + 3;
    let rest = &row[at..];
    if let Some(stripped) = rest.strip_prefix('"') {
        stripped.find('"').map(|end| stripped[..end].to_string())
    } else {
        rest.find([',', '}']).map(|end| rest[..end].to_string())
    }
}

/// The receipt parser, pinned directly — see [`receipt_field`] for why.
#[test]
fn the_receipt_field_parser_reads_values_and_not_their_delimiters() {
    let row = r#"{"schema":"s/1","name":"dropped retain","killed":1,"survivors":[],"last":"z"}"#;
    assert_eq!(receipt_field(row, "schema").as_deref(), Some("s/1"));
    assert_eq!(
        receipt_field(row, "name").as_deref(),
        Some("dropped retain"),
        "a string value must come back without its quotes and without the following key"
    );
    assert_eq!(receipt_field(row, "killed").as_deref(), Some("1"));
    assert_eq!(receipt_field(row, "survivors").as_deref(), Some("[]"));
    assert_eq!(receipt_field(row, "last").as_deref(), Some("z"));
    assert_eq!(
        receipt_field(row, "absent"),
        None,
        "an absent key must be None, never a default that a comparison would accept"
    );
}

// ---------------------------------------------------------------------------
// The per-commit half: recipes stay joined, and recorded kills stay current
// ---------------------------------------------------------------------------

/// A plant whose anchor no longer exists is a recipe for a codebase that has moved on.
///
/// Checked as **exactly one** occurrence in both directions: zero means the site is gone,
/// and more than one means the plant would mutate several places at once, so a kill could
/// no longer be attributed to the defect §18 names.
#[test]
fn every_plant_still_targets_a_live_production_site() {
    let root = workspace_root();
    let mut failures = Vec::new();
    for plant in PLANTS {
        let path = root.join(plant.file);
        let Ok(source) = std::fs::read_to_string(&path) else {
            failures.push(format!("`{}`: {} is unreadable", plant.name, plant.file));
            continue;
        };
        let occurrences = source.matches(plant.find).count();
        if occurrences != 1 {
            failures.push(format!(
                "`{}`: the anchor occurs {occurrences} times in {} (must be exactly 1). \
                 The production site this mutant is defined against has moved, split or \
                 vanished, so the recipe no longer plants what §18 names. Re-derive the \
                 anchor and re-run the campaign; do not relax this count",
                plant.name, plant.file
            ));
            continue;
        }
        if plant.find == plant.replace || source.contains(plant.replace) {
            failures.push(format!(
                "`{}`: the replacement is already present in {} (or equals the anchor), so \
                 planting it would be a no-op and the campaign would score a mutant that \
                 was never introduced",
                plant.name, plant.file
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n  "));
}

/// Recipes and markers must account for each other, or one side can drift unnoticed.
#[test]
fn plants_and_markers_are_joined_in_both_directions() {
    let root = workspace_root();
    let names = mandated_names(&agents_md());
    let found = markers(&root);
    let mut failures = Vec::new();

    for plant in PLANTS {
        if !names.iter().any(|n| n == plant.name) {
            failures.push(format!(
                "PLANTS names `{}`, which is not one of §18's mandated names {names:?} — a \
                 recipe for an obligation nobody asked for",
                plant.name
            ));
        }
        let marked_in: Vec<&str> = found
            .iter()
            .filter(|(name, _)| name == plant.name)
            .map(|(_, file)| file.as_str())
            .collect();
        if marked_in.is_empty() {
            failures.push(format!(
                "`{}` has a plant but no test carries its marker",
                plant.name
            ));
        }
        for killer in plant.killers {
            if !marked_in.contains(&killer.file) {
                failures.push(format!(
                    "`{}`: killer `{}` lives in {}, which carries no marker for this name \
                     (marked in {marked_in:?}). The marker is what records which obligation \
                     a test discharges, so a killer in an unmarked file is joined to §18 by \
                     nothing again",
                    plant.name, killer.path, killer.file
                ));
            }
        }
    }

    // The other direction: a marked name with no recipe is a kill nobody can reproduce.
    for (name, file) in &found {
        if name == DECOY_SENTINEL {
            continue;
        }
        if !PLANTS.iter().any(|p| p.name == name.as_str()) {
            failures.push(format!(
                "`{name}` is marked in {file} but has no plant, so nothing can re-establish \
                 that the marked test still kills it"
            ));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n  "));
}

/// A name excused by a stub crate must not also carry a recipe.
#[test]
fn no_plant_exists_for_a_name_that_cannot_be_seeded_yet() {
    for (name, krate) in NOT_YET_SEEDED {
        assert!(
            !PLANTS.iter().any(|p| p.name == name),
            "`{name}` is declared not-yet-seeded against `{krate}` and yet has a plant. One \
             of the two is false: either the subsystem landed (drop the declaration) or the \
             recipe mutates something that is not the defect §18 names"
        );
    }
}

/// The extractor, tested directly — otherwise the retention digest could be silently
/// computed over a truncated body and still look stable.
#[test]
fn the_body_extractor_finds_whole_bodies_and_refuses_rather_than_truncating() {
    let top_level = "fn a() {\n    let s = \"}\";\n}\nfn b() {}\n";
    let body = fn_body(top_level, "a").expect("top-level fn is extractable");
    assert!(
        body.contains("let s") && !body.contains("fn b"),
        "the body must stop at its own closing brace: {body:?}"
    );

    // A brace inside a string literal must not end the body — the reason this is
    // indentation-matched rather than brace-counted.
    let indented = "mod t {\n    fn c() {\n        p(\"{x:?}\");\n    }\n    fn d() {}\n}\n";
    let body = fn_body(indented, "c").expect("indented fn is extractable");
    assert!(
        body.contains("{x:?}") && !body.contains("fn d"),
        "an indented body must match its own indent: {body:?}"
    );

    assert!(fn_body(top_level, "nonexistent").is_none());
    // Refusing is the point: a `pub fn` is not covered by the indent rule, and returning a
    // wrong body would be worse than returning none.
    assert!(fn_body("pub fn e() {\n}\n", "e").is_none());
}

/// **The retention check.** A recorded kill must still describe the code it was measured on.
///
/// This is what makes the campaign worth running: without it, one hand-run measurement ages
/// into a claim about a tree it no longer describes — which is `vdi4`'s shape, an evidence
/// anchor that stays green while the thing underneath it moves.
#[test]
fn the_recorded_kills_still_describe_this_tree() {
    let root = workspace_root();
    let path = kill_receipt_path(&root);
    let text = std::fs::read_to_string(&path).unwrap_or_else(|error| {
        panic!(
            "no mandated-mutant kill receipt at {} ({error}). Every marked test claims to \
             kill a §18 mutant and nothing has measured that on this tree.\n\
             Run the campaign and commit the rows it appends:\n\
             \x20   cargo test -p fln-conformance --test mandated_mutants \\\n\
             \x20     the_mandated_mutants_are_planted_and_their_killers_die \\\n\
             \x20     -- --ignored --exact --nocapture\n\
             Measured cost 9,393 ms — cheap because the dependency universe is closed \
             (D1), so the campaign's own build directory is 56 MB from cold. \
             Deleting this test is not the alternative: it is the \
             only thing joining the markers to a measured kill (bead {KILL_RECEIPT_BEAD}).",
            path.display()
        )
    });
    let rows: Vec<&str> = text.lines().filter(|l| !l.trim().is_empty()).collect();
    assert!(
        !rows.is_empty(),
        "{} exists but holds no rows. An empty receipt is not a weaker claim than a missing \
         one; it is the same claim with the evidence taken out",
        path.display()
    );

    let field = receipt_field;
    let mut failures = Vec::new();
    for plant in PLANTS {
        let site = site_digest(plant);
        let killers = killer_digest(&root, plant);
        let matching = rows.iter().find(|row| {
            field(row, "name").as_deref() == Some(plant.name)
                && field(row, "site_digest").as_deref() == Some(site.as_str())
                && field(row, "killer_digest").as_deref() == Some(killers.as_str())
        });
        let Some(row) = matching else {
            failures.push(format!(
                "`{}`: no receipt row matches this tree (site_digest {site}, killer_digest \
                 {killers}). Either the mutated site in {} or one of the killer bodies \
                 {:?} has changed since the kill was measured, so the recorded kill \
                 describes code that is no longer here. Re-run the campaign (9,393 ms \
                 measured) and commit the appended row:\n\
                 \x20   cargo test -p fln-conformance --test mandated_mutants \\\n\
                 \x20     the_mandated_mutants_are_planted_and_their_killers_die \\\n\
                 \x20     -- --ignored --exact --nocapture",
                plant.name,
                plant.file,
                plant.killers.iter().map(|k| k.path).collect::<Vec<_>>()
            ));
            continue;
        };
        let expected = plant.killers.len().to_string();
        for (key, why) in [
            (
                "control_passed",
                "the killers did not all pass BEFORE the mutation, so the \
                                run proves nothing about the mutation",
            ),
            ("killed", "not every killer died under the mutant"),
            (
                "reasons_matched",
                "a killer died for a reason other than the one the mutant \
                                 introduces — the kill is coincidental",
            ),
        ] {
            if field(row, key).as_deref() != Some(expected.as_str()) {
                failures.push(format!(
                    "`{}`: receipt records {key}={} against {} killer(s) — {why}",
                    plant.name,
                    field(row, key).unwrap_or_else(|| "<absent>".into()),
                    plant.killers.len()
                ));
            }
        }
        if field(row, "survivors").as_deref() != Some("[]") {
            failures.push(format!(
                "`{}`: receipt records survivors {}. A surviving critical mutant blocks the \
                 gate (§18) and must not sit quietly in an evidence file",
                plant.name,
                field(row, "survivors").unwrap_or_else(|| "<absent>".into())
            ));
        }
        if field(row, "schema").as_deref() != Some(KILL_RECEIPT_SCHEMA) {
            failures.push(format!("`{}`: unknown receipt schema", plant.name));
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {} mandated mutants have no current kill evidence:\n  {}",
        failures.len(),
        PLANTS.len(),
        failures.join("\n  ")
    );
}

// ---------------------------------------------------------------------------
// The cadence join: what dispatches the campaign, and what the receipt claims
// ---------------------------------------------------------------------------
//
// Every receipt row carries a `class` token, and that token is the row's disclosure of what
// its measurement is worth — specifically, of the *cadence* behind it. Until this section
// existed the token was written by the campaign and read by **nothing**, which is the same
// defect one field over that `fln-parity-ledger-freshness-names-the-run-igxr` found in the
// Parity Ledger (`freshness` written once at `ledger.rs:205`, never read again) and that
// `fln-8zsq` found in the corpus censuses (a claim class disclosed, and unwatched).
//
// An unread class token can say anything. Both directions were live:
//
//   * give the campaign a dispatcher and nothing makes the token stop saying nobody runs it;
//   * write a token claiming a cadence, delete the workflow, and nothing notices.
//
// So the token is derived from the dispatch state rather than transcribed, and the derivation
// has exactly one implementation ([`Dispatch::class`]) shared by the writer and this guard.
// Two hand-written copies of "what cadence do we have" would be a join between two rules with
// nothing watching it — this module's own defect class, one floor down.

/// The libtest name the campaign answers to.
///
/// A dispatcher that does not name this exact path is not dispatching this campaign.
const CAMPAIGN_TEST: &str = "the_mandated_mutants_are_planted_and_their_killers_die";

/// How many lines after the campaign's own line still count as its `run:` block.
///
/// The check is deliberately a window rather than the whole file: `--ignored` appearing in
/// some unrelated job must not vouch for a step that dropped it.
const RUN_BLOCK_WINDOW: usize = 8;

/// What, if anything, actually runs the campaign.
///
/// Ordered by strength so the workspace-wide state is the strongest any single workflow
/// provides.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Dispatch {
    /// No workflow runs the campaign. A run is whatever somebody remembered to do by hand.
    Nothing,
    /// A workflow runs it, but only when a human asks.
    OnDemandOnly,
    /// A workflow runs it on a cron.
    Scheduled,
}

impl Dispatch {
    /// The exact `class` token a measurement earns under this dispatch state.
    ///
    /// **Every arm ends in `not_a_per_commit_gate`, and that is the point.** A cron does not
    /// turn a campaign into a per-commit mutation gate; it turns one remembered run into a
    /// dispatched one. §18 asks that a surviving critical mutant block the gate, and what a
    /// cron blocks is the cron's own lane. Widening any of these tokens to imply otherwise
    /// is the overclaim this whole section exists to make impossible.
    fn class(self) -> &'static str {
        match self {
            Dispatch::Nothing => "observed_once_not_a_per_commit_gate",
            Dispatch::OnDemandOnly => "dispatched_on_demand_not_a_per_commit_gate",
            Dispatch::Scheduled => "dispatched_on_a_cron_not_a_per_commit_gate",
        }
    }
}

/// What one workflow file dispatches.
///
/// Three near-misses must NOT count, and each is a real way to build a dispatcher that
/// dispatches nothing:
///
/// * **A run that omits `--ignored`.** The campaign is `#[ignore]`d, so a libtest filter
///   naming it without `--ignored` matches nothing — and *a libtest filter matching nothing
///   exits 0*. That lane is green forever while running no campaign at all. This is the same
///   vacuum [`Killer::path`] documents for the killers themselves.
/// * **A mention inside a YAML comment.** Prose about the campaign is not a dispatch of it,
///   and this file's own workflow cites the campaign in comments.
/// * **`workflow_dispatch:` alone.** Runnable on request is not a cadence, so it earns
///   [`Dispatch::OnDemandOnly`] and a weaker token — never the cron token.
///
/// **Stated limitation:** this is a line-window scan, not a YAML parse (D1 rules out a
/// parser dependency, and hand-rolling one to read three keys would be the larger risk). It
/// binds `--ignored` to the campaign's own `run:` block via [`RUN_BLOCK_WINDOW`], but
/// `schedule:`/`cron:` are matched file-wide, so a workflow carrying a cron for some *other*
/// job would read as scheduled. That is visible in review and fails safe in the direction
/// that matters least; a cron that is deleted still drops the state and fires this guard.
fn dispatch_in_workflow(yaml: &str) -> Dispatch {
    let lines: Vec<&str> = yaml
        .lines()
        .filter(|line| !line.trim_start().starts_with('#'))
        .collect();
    let runs_campaign = lines.iter().enumerate().any(|(at, line)| {
        line.contains(CAMPAIGN_TEST)
            && lines[at..]
                .iter()
                .take(RUN_BLOCK_WINDOW + 1)
                .any(|l| l.contains("--ignored"))
    });
    if !runs_campaign {
        return Dispatch::Nothing;
    }
    let scheduled = lines
        .iter()
        .any(|l| l.trim_start().starts_with("schedule:"))
        && lines.iter().any(|l| l.contains("cron:"));
    if scheduled {
        Dispatch::Scheduled
    } else {
        Dispatch::OnDemandOnly
    }
}

/// Every workflow file, so the scan's scope is *derived* rather than hand-listed.
///
/// A hand-list of workflow filenames is how a scope rots: `scripts/check.sh`'s `INPUT_PATHS`
/// names `ci.yml` and `contract-drift.yml` individually, so a third workflow joins the tree
/// outside it silently. Reading the directory means a dispatcher cannot be added, renamed or
/// deleted behind this guard's back.
fn workflow_files(root: &std::path::Path) -> Vec<(String, String)> {
    let dir = root.join(".github/workflows");
    let mut out = Vec::new();
    let Ok(entries) = std::fs::read_dir(&dir) else {
        return out;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let is_yaml = path
            .extension()
            .and_then(|e| e.to_str())
            .is_some_and(|e| e == "yml" || e == "yaml");
        if !is_yaml {
            continue;
        }
        if let Ok(text) = std::fs::read_to_string(&path) {
            let name = path
                .file_name()
                .and_then(|n| n.to_str())
                .unwrap_or_default()
                .to_string();
            out.push((name, text));
        }
    }
    out.sort();
    out
}

/// The dispatch state of the whole repository: the strongest any one workflow provides.
fn measured_dispatch(root: &std::path::Path) -> (Dispatch, Vec<String>) {
    let files = workflow_files(root);
    assert!(
        !files.is_empty(),
        "no workflow files were read from {}. An empty scan is a broken scan, not a repository \
         with no CI — this guard's whole verdict is derived from that directory, so it refuses \
         rather than reporting the weakest state on no evidence",
        root.join(".github/workflows").display()
    );
    let mut best = Dispatch::Nothing;
    let mut dispatchers = Vec::new();
    for (name, text) in &files {
        let state = dispatch_in_workflow(text);
        if state != Dispatch::Nothing {
            dispatchers.push(format!("{name} ({state:?})"));
        }
        best = best.max(state);
    }
    (best, dispatchers)
}

/// The dispatch reader, pinned on synthetic inputs including every near-miss.
///
/// A guard nobody has seen refuse is a guard nobody has tested, and the negative controls
/// here are the ones that would otherwise pass silently.
#[test]
fn the_dispatch_reader_separates_a_real_lane_from_the_three_near_misses() {
    let scheduled = "on:\n  schedule:\n    - cron: \"23 4 * * 2\"\n  workflow_dispatch:\n\
                     jobs:\n  c:\n    steps:\n      - run: |\n          cargo test \
                     the_mandated_mutants_are_planted_and_their_killers_die \\\n            \
                     -- --ignored --exact\n";
    assert_eq!(dispatch_in_workflow(scheduled), Dispatch::Scheduled);

    let on_demand = "on:\n  workflow_dispatch:\njobs:\n  c:\n    steps:\n      - run: |\n\
                     \x20         cargo test the_mandated_mutants_are_planted_and_their_killers_die \\\n\
                     \x20           -- --ignored --exact\n";
    assert_eq!(
        dispatch_in_workflow(on_demand),
        Dispatch::OnDemandOnly,
        "runnable on request is not a cadence and must never earn the cron token"
    );

    let no_ignored = "on:\n  schedule:\n    - cron: \"23 4 * * 2\"\njobs:\n  c:\n    steps:\n\
                      \x20     - run: cargo test the_mandated_mutants_are_planted_and_their_killers_die\n";
    assert_eq!(
        dispatch_in_workflow(no_ignored),
        Dispatch::Nothing,
        "the campaign is #[ignore]d, so this filter matches nothing and libtest exits 0 — a \
         lane that is green forever while running no campaign at all"
    );

    let commented = "on:\n  schedule:\n    - cron: \"23 4 * * 2\"\njobs:\n  c:\n    steps:\n\
                     \x20     # runs the_mandated_mutants_are_planted_and_their_killers_die \
                     -- --ignored one day\n      - run: cargo build\n";
    assert_eq!(
        dispatch_in_workflow(commented),
        Dispatch::Nothing,
        "prose about the campaign is not a dispatch of it"
    );

    let far_apart = format!(
        "on:\n  workflow_dispatch:\njobs:\n  a:\n    steps:\n      - run: cargo test {CAMPAIGN_TEST}\n{}      - run: cargo test other -- --ignored\n",
        "      - run: echo filler\n".repeat(RUN_BLOCK_WINDOW + 2)
    );
    assert_eq!(
        dispatch_in_workflow(&far_apart),
        Dispatch::Nothing,
        "`--ignored` in an unrelated step must not vouch for a step that dropped it"
    );

    assert_eq!(dispatch_in_workflow(""), Dispatch::Nothing);
}

/// The class token every arm produces is distinct, and none of them claims a per-commit gate.
///
/// Pinned as an exact token in both directions: a token that drifted would silently
/// invalidate every receipt row written before the drift, and a token widened to imply a
/// per-commit gate is the overclaim [`Dispatch::class`] exists to prevent.
#[test]
fn no_dispatch_state_earns_a_per_commit_gate_token() {
    let all = [
        Dispatch::Nothing,
        Dispatch::OnDemandOnly,
        Dispatch::Scheduled,
    ];
    let tokens: Vec<&str> = all.iter().map(|d| d.class()).collect();
    for token in &tokens {
        assert!(
            token.ends_with("not_a_per_commit_gate"),
            "`{token}` stops disclosing that the campaign is not a per-commit gate. A cron \
             dispatches a lane; it does not make every commit run the campaign"
        );
    }
    let mut distinct = tokens.clone();
    distinct.sort_unstable();
    distinct.dedup();
    assert_eq!(
        distinct.len(),
        all.len(),
        "two dispatch states share a class token, so the receipt cannot distinguish them"
    );
}

/// The receipt's cadence disclosure must equal the cadence that actually exists.
///
/// Checked against the **most recent** row matching each plant's digests. Earlier rows
/// describing the same tree are superseded measurements and legitimately carry the cadence
/// that was true when they were taken — rewriting them would be falsifying history, and this
/// guard is about what the current claim says, not about editing the old ones.
///
/// Both directions fail, and each names its own repair:
///
///   * a dispatcher exists and the rows still disclose a weaker cadence — re-run the campaign,
///     which writes the derived token;
///   * the rows disclose a cadence and the dispatcher is gone — restore it, or re-run and let
///     the token drop.
#[test]
fn the_receipt_class_matches_what_actually_dispatches_the_campaign() {
    let root = workspace_root();
    let (dispatch, dispatchers) = measured_dispatch(&root);
    let expected = dispatch.class();

    let path = kill_receipt_path(&root);
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("no kill receipt at {} ({error})", path.display()));
    let rows: Vec<&str> = text.lines().filter(|l| !l.trim().is_empty()).collect();

    let mut failures = Vec::new();
    let mut checked = 0usize;
    for plant in PLANTS {
        let site = site_digest(plant);
        let killers = killer_digest(&root, plant);
        // `rfind`-by-filter: the operative measurement is the newest one describing this tree.
        let current = rows.iter().rev().find(|row| {
            receipt_field(row, "name").as_deref() == Some(plant.name)
                && receipt_field(row, "site_digest").as_deref() == Some(site.as_str())
                && receipt_field(row, "killer_digest").as_deref() == Some(killers.as_str())
        });
        // A plant with no current row is `the_recorded_kills_still_describe_this_tree`'s
        // finding, not this one. Staying silent here keeps one failure reporting one defect.
        let Some(row) = current else { continue };
        checked += 1;
        let claimed = receipt_field(row, "class");
        if claimed.as_deref() != Some(expected) {
            failures.push(format!(
                "`{}`: receipt discloses class {:?}, but the repository dispatches the campaign \
                 as {dispatch:?}, which earns {expected:?}",
                plant.name,
                claimed.unwrap_or_else(|| "<absent>".into())
            ));
        }
    }

    assert!(
        checked > 0,
        "no receipt row matched any plant, so this guard compared nothing and would pass on an \
         empty file. That is a broken join, not a clean tree"
    );
    assert!(
        failures.is_empty(),
        "the kill receipt's cadence disclosure has come apart from the cadence that exists.\n  \
         {}\n\nMeasured dispatch: {dispatch:?}{}\n\n\
         If a dispatcher was just added, the recorded measurements pre-date it — re-run the \
         campaign so the rows disclose the cadence they were taken under:\n\
         \x20   cargo test -p fln-conformance --test mandated_mutants \\\n\
         \x20     {CAMPAIGN_TEST} \\\n\
         \x20     -- --ignored --exact --nocapture\n\
         If a dispatcher was removed, restore it or re-run and let the token drop. What is not \
         available is keeping the claim without the thing that produces it (bead \
         {KILL_RECEIPT_BEAD}).",
        failures.join("\n  "),
        if dispatchers.is_empty() {
            String::from(" (no workflow runs the campaign)")
        } else {
            format!(" from: {}", dispatchers.join(", "))
        }
    );
}

// ---------------------------------------------------------------------------
// The campaign
// ---------------------------------------------------------------------------

/// A planted mutation that restores itself, including on panic.
///
/// `Drop` rather than a tidy-up at the end of the happy path: this test edits tracked source,
/// and an assertion failure mid-campaign must not leave a kernel with its positivity check
/// disabled sitting in somebody's working tree.
struct Planted {
    path: std::path::PathBuf,
    original: String,
}

impl Drop for Planted {
    fn drop(&mut self) {
        let _ = std::fs::write(&self.path, &self.original);
    }
}

/// Plant every mandated mutant, watch its named killers die for the stated reason, and
/// record the measurement.
///
/// `#[ignore]`d because it **edits tracked source files**. It refuses to start unless the
/// working tree is clean, so it can tell its own mutation from somebody else's edit — and so
/// that it never runs while another pane has work in flight.
#[test]
#[ignore = "edits tracked source; run deliberately (see the_recorded_kills_still_describe_this_tree)"]
fn the_mandated_mutants_are_planted_and_their_killers_die() {
    let root = workspace_root();
    let started = std::time::Instant::now();

    // The cadence this run is taken under, derived once from the same function the guard
    // reads. Transcribing a token here instead would be two copies of one rule with nothing
    // watching the join — which is the defect the receipt exists to close.
    let (dispatch, _) = measured_dispatch(&root);
    let measured_class = dispatch.class();

    let git = |args: &[&str]| -> String {
        let out = std::process::Command::new("git")
            .args(args)
            .current_dir(&root)
            .output()
            .expect("git runs");
        String::from_utf8_lossy(&out.stdout).trim().to_string()
    };
    // Only the files this campaign touches need to be pristine — the ones it mutates, and
    // the ones whose bodies it digests. A whole-tree clean check looks safer and is worse
    // twice over: it is unsatisfiable in a shared checkout where other panes always have
    // work in flight, and forcing the run into a throwaway commit would make every receipt
    // cite an anchor unreachable from `main`, which is precisely the defect
    // `fln-history-rewrite-evidence-anchor-reachability-vdi4` records. The safety property
    // that actually matters is narrower: this must not restore over somebody's edit, and it
    // must not digest somebody's uncommitted work as if it were the committed tree.
    let mut owned: Vec<&str> = PLANTS.iter().map(|p| p.file).collect();
    owned.extend(PLANTS.iter().flat_map(|p| p.killers.iter().map(|k| k.file)));
    owned.sort_unstable();
    owned.dedup();
    let status = git(&["status", "--porcelain"]);
    let collisions: Vec<&str> = status
        .lines()
        .filter(|line| owned.iter().any(|file| line.contains(file)))
        .collect();
    assert!(
        collisions.is_empty(),
        "these files are modified and this campaign both mutates and digests them, so it \
         cannot tell its own mutation from work in progress — and its restore would \
         overwrite that work. Commit or stash them first:\n  {}\n\
         (the rest of the tree may be dirty; only these {} files matter here)",
        collisions.join("\n  "),
        owned.len()
    );
    let commit = git(&["rev-parse", "HEAD"]);
    assert_eq!(
        commit.len(),
        40,
        "HEAD did not resolve to a commit: {commit}"
    );

    // A separate target directory: the outer `cargo test` holds the build lock on the
    // ambient one for the whole invocation, so an inner cargo sharing it would wait for
    // this test to finish and this test would wait for it. Cheap here because the
    // dependency universe is closed (D1) — measured at 4.1 s and 56 MB from cold.
    let inner_target = std::env::var("CARGO_TARGET_DIR")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|_| root.join("target"))
        .join("mandated-mutants");

    let run = |plant: &Plant| -> (bool, String) {
        let mut cmd = std::process::Command::new("cargo");
        cmd.arg("test")
            .arg("--locked")
            .arg("-p")
            .arg(plant.package)
            .args(plant.target)
            .arg("--")
            .args(plant.killers.iter().map(|k| k.path))
            .arg("--exact")
            .arg("--test-threads=1")
            .current_dir(&root)
            .env("CARGO_TARGET_DIR", &inner_target);
        let out = cmd.output().expect("cargo runs");
        let mut text = String::from_utf8_lossy(&out.stdout).into_owned();
        text.push_str(&String::from_utf8_lossy(&out.stderr));
        (out.status.success(), text)
    };

    let mut rows = Vec::new();
    for plant in PLANTS {
        let path = root.join(plant.file);
        let original = std::fs::read_to_string(&path).expect("production file is readable");
        assert_eq!(
            original.matches(plant.find).count(),
            1,
            "`{}`: anchor is not unique in {}",
            plant.name,
            plant.file
        );

        // (a) Control. Every killer must PASS and must be SEEN to run: `--exact` against a
        // name that no longer exists matches nothing and exits 0, which would otherwise be
        // indistinguishable from a clean control.
        let (ok, control) = run(plant);
        assert!(
            ok,
            "`{}`: the killers do not pass on an unmutated tree, so nothing this campaign \
             observes afterwards can be attributed to the mutant:\n{control}",
            plant.name
        );
        let control_passed = plant
            .killers
            .iter()
            .filter(|k| control.contains(&format!("test {} ... ok", k.path)))
            .count();
        assert_eq!(
            control_passed,
            plant.killers.len(),
            "`{}`: only {control_passed} of {} killers were observed to RUN in the control. \
             A libtest filter that matches nothing exits 0, so an unseen test is a vacuum, \
             not a pass:\n{control}",
            plant.name,
            plant.killers.len()
        );

        // (b) Plant, restoring on every exit path including a panic below.
        let planted = Planted {
            path: path.clone(),
            original: original.clone(),
        };
        std::fs::write(&path, original.replacen(plant.find, plant.replace, 1))
            .expect("the mutation is writable");

        // (c) The mutant must be killed, by the NAMED tests, for the STATED reason.
        let (still_ok, mutated) = run(plant);
        let mut survivors = Vec::new();
        let mut killed = 0usize;
        let mut reasons_matched = 0usize;
        for killer in plant.killers {
            if mutated.contains(&format!("test {} ... FAILED", killer.path)) {
                killed += 1;
                if mutated.contains(killer.expect) {
                    reasons_matched += 1;
                }
            } else {
                survivors.push(killer.path);
            }
        }

        // (d) Restore, and prove it.
        drop(planted);
        let restored = std::fs::read_to_string(&path).expect("production file is readable");
        assert_eq!(
            restored, original,
            "`{}`: {} was NOT restored to its original bytes",
            plant.name, plant.file
        );

        assert!(
            !still_ok && survivors.is_empty(),
            "`{}`: SURVIVING MANDATED MUTANT. §18 makes this release-blocking. Survivors: \
             {survivors:?}\n{mutated}",
            plant.name
        );
        assert_eq!(
            reasons_matched,
            plant.killers.len(),
            "`{}`: {reasons_matched} of {} killers died for the stated reason. A test that \
             fails for an unrelated reason has stopped discharging this obligation even \
             though it still fails:\n{mutated}",
            plant.name,
            plant.killers.len()
        );

        rows.push(format!(
            "{{\"schema\":\"{KILL_RECEIPT_SCHEMA}\",\"bead\":\"{KILL_RECEIPT_BEAD}\",\
             \"name\":\"{}\",\"head_commit\":\"{commit}\",\"observed_unix_s\":{},\
             \"site_file\":\"{}\",\"site_digest\":\"{}\",\"killers\":[{}],\
             \"killer_digest\":\"{}\",\"control_passed\":{},\"killed\":{killed},\
             \"reasons_matched\":{reasons_matched},\"survivors\":[],\
             \"class\":\"{measured_class}\"}}",
            plant.name,
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("clock is after the epoch")
                .as_secs(),
            plant.file,
            site_digest(plant),
            plant
                .killers
                .iter()
                .map(|k| format!("\"{}\"", k.path))
                .collect::<Vec<_>>()
                .join(","),
            killer_digest(&root, plant),
            control_passed,
        ));
        println!("mandated_mutants: `{}` KILLED by {:?}", plant.name, {
            plant.killers.iter().map(|k| k.path).collect::<Vec<_>>()
        });
    }

    let out = std::env::var("FLN_MUTANT_CAMPAIGN_RECEIPT")
        .map(std::path::PathBuf::from)
        .unwrap_or_else(|_| kill_receipt_path(&root));
    if let Some(parent) = out.parent() {
        std::fs::create_dir_all(parent).expect("the evidence directory is creatable");
    }
    let mut text = std::fs::read_to_string(&out).unwrap_or_default();
    for row in &rows {
        text.push_str(row);
        text.push('\n');
    }
    std::fs::write(&out, text).expect("the receipt is writable");
    println!(
        "mandated_mutants campaign: {} of {} mandated mutants planted and killed in {} ms; \
         {} row(s) appended to {}. This is ONE measurement at {commit} on this host — class \
         bounded_model, dispatch {dispatch:?}, disclosed as `{measured_class}`. A cron \
         dispatches this lane; it is still not a per-commit mutation gate.",
        rows.len(),
        PLANTS.len(),
        started.elapsed().as_millis(),
        rows.len(),
        out.display()
    );
}
