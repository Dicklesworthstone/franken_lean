//! Every commit anchor cited in a governed tracked file must stay **verifiable from `main`**,
//! and the population that is not is declared here and refused growth per commit (bead
//! `fln-history-rewrite-evidence-anchor-reachability-vdi4`).
//!
//! **The gap this closes, in that bead's own words.** `vdi4` closed its classifier/fixture
//! half: `golden_vellum.rs` proves a *mutable Vellum producer* is main-reachable and that
//! only `merge-base --is-ancestor` separates current evidence from a backup-only twin. What
//! it explicitly did **not** buy is a repository-wide per-commit scan — `scan_evidence_file`
//! runs only against a temporary fixture's `anchors.txt`, no tracked test walks the manifest,
//! `AGENTS.md`, `ci/`, `crates/`, `scripts/` or `tools/`, and no allowance is checked in
//! either direction. AGENTS.md states the consequence plainly: *a hundred more backup-only
//! anchors would still not fail the build*. They do now.
//!
//! **Why an anchor rots without anyone touching it.** The 2026-07-25 `filter-branch` did not
//! make these citations wrong; it made them unverifiable from `main`. `refs/original` and the
//! backup branches keep every pre-rewrite commit alive **in this clone**, so `git cat-file -t`
//! and `git show` both succeed on a dead anchor and a naive existence check passes 12/12 on a
//! population where two thirds denote nothing reachable. Reachability from `main` is the only
//! question worth asking, and it is the only one asked here.
//!
//! **What a recovered twin does and does not prove, kept verbatim because it is this
//! technique's exact limit:** *a twin proves two commits carry the same content, never that
//! the sentence citing it was sound.* This guard therefore classifies **reachability** and
//! makes no claim about whether any citing sentence is true. Recoverability was measured
//! separately (`c291fd91`: 9 of 9 manifest anchors, 128 of 132 repository-wide) and is
//! deliberately **not** re-derived here — it costs a patch-id per anchor, and a guard that
//! runs per commit must not.
//!
//! # The boundary, stated rather than discovered
//!
//! The scope is **derived** from `git grep` over `HEAD`, never listed, so a file added
//! tomorrow is in scope without anyone editing this file. Three exclusions are declared, each
//! with a reason and a disclosed cardinality, because a filter that silently drops what it
//! cannot handle is a **sampler** rather than a scan:
//!
//! * **`vendor/`** — 12,828 of the 13,302 tracked paths. It is the pinned Reference tree, not
//!   project-authored evidence; its content is governed by the pin and by the build gate's M1,
//!   and no claim in it is ours to keep verifiable.
//! * **`.beads/issues.jsonl`** — and this exclusion is **not clean, which is the honest part**.
//!   Measured at `c291fd91`: it carries **106** backup-only anchors, of which **88 sit in
//!   immutable comment records** and cannot be repaired at all, only annotated — but **7 sit
//!   in a mutable field only and 10 in both**, so **17 of the 106 are repairable in principle
//!   and are excused here anyway**. The second reason is why: every pane's ordinary `br`
//!   command rewrites this file wholesale, so a bound count would redden on routine bead work
//!   — the cry-wolf failure this repository has already measured twice. The file is disclosed
//!   with a **floor** rather than an equality: it may churn upward freely and may not silently
//!   vanish, which is a broken scan rather than a clean tree.
//! * **binary files** — `git grep -I`. Three `.olean` fixtures under `tribunal/fixtures/`
//!   match the hex shape and emit `Binary file … matches` instead of a parsable record. Any
//!   hex inside a compiled artifact is data, not a citation. The count is asserted, so a
//!   fourth binary joining the tree is a disclosure change rather than a silent narrowing.
//!
//! # The direction of the binding, which is not the same as its neighbour's
//!
//! `artifact_referent_census.rs` binds its population by **equality in both directions**,
//! because it discloses a *measured population* that does not shrink by itself. This is the
//! other shape: a **declared remainder of permitted violations**, which shrinks exactly as
//! people repair it. So it is **one-way plus a floor** — a count may fall freely and may not
//! rise, and a file carrying an undeclared anchor fails outright. Equality here would be a
//! wall that reddens a correct repair, which this repository has already paid for once.
//!
//! # What this does not earn
//!
//! It reads **`HEAD`**, not the working tree. An anchor added in an uncommitted edit is
//! invisible until it is committed — accepted deliberately, because the alternative is a
//! guard that reddens on five peers' in-flight edits, which is the failure mode live in this
//! very crate right now (`the_rch_tracker_exclusion_row_matches_the_measured_population` is
//! red on an orphan nobody can commit). Failing one commit later still fails the build.
//!
//! An 8-hex token that resolves to a commit is *treated* as an anchor; a hex literal that
//! collides with a commit prefix would be counted. With ~1,100 tracked commit objects and
//! 16^8 prefixes the expected accidental count over this corpus is far below one, but it is a
//! probability rather than a proof. It does not check that a *reachable* anchor's citing
//! sentence is true — that is `pfei` R2's territory and stays unwatched. And the exclusions
//! above mean 106 of the tree's 132 backup-only anchors are outside this guard's reach: what
//! is bound is the **26** that live in files a person can edit.

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

/// Backup-only anchors this repository has not repaired, **per file**.
///
/// Per member, never as one total: a sum over many files is a budget refilled by its own
/// repairs, so a conversion in one file silently opens slots for new rot in another. That is
/// measured, not theoretical — `k60n` watched four new unprotected rigs land in four commits
/// under a green aggregate guard.
const BACKUP_ONLY_ALLOWANCE: &[(&str, usize)] = &[
    ("AGENTS.md", 2),
    ("ci/VERIFICATION_MANIFEST.jsonl", 17),
    ("ci/WORKSPACE_GRAPH.txt", 1),
    ("crates/fln-conformance/src/witness.rs", 3),
    (
        "crates/fln-conformance/tests/artifact_referent_census.rs",
        1,
    ),
    (
        "crates/fln-conformance/tests/digest_preimage_encoding.rs",
        3,
    ),
    ("crates/fln-conformance/tests/parity_ledger.rs", 1),
    ("crates/fln-conformance/tests/witness_claim_matrix.rs", 2),
    ("crates/fln-env/src/extensions.rs", 1),
    ("crates/fln-env/src/intern.rs", 1),
    ("crates/fln-env/src/modules.rs", 2),
    (
        "crates/fln-syntax/tests/corpus/VELLUM_GOLDENS_PROVENANCE.md",
        1,
    ),
    ("crates/fln-syntax/tests/golden_vellum.rs", 1),
    (
        "crates/fln-verdict/tests/corpus/CERTIFICATE_GOLDENS_PROVENANCE.md",
        1,
    ),
    ("crates/fln-verdict/tests/corpus/certificate_goldens.hex", 1),
    ("crates/fln-verdict/tests/golden_certificates.rs", 1),
    ("tools/structure-guard/src/ledger.rs", 1),
];

/// Pathspecs excluded from the derived scope. See the module header for each reason.
const EXCLUDED: &[&str] = &[":!vendor", ":!.beads/issues.jsonl"];

/// `.beads/issues.jsonl`'s backup-only population: a floor, never an equality, because every
/// pane's `br` rewrites the file. Falling below it means the scan broke.
const BEADS_BACKUP_ONLY_FLOOR: usize = 90;

/// Binary files the harvest cannot parse, asserted so a fourth is a disclosure change rather
/// than a silent narrowing of the denominator.
const BINARY_FILES_SKIPPED: usize = 3;

/// Anti-vacuity floors on the *denominator*. A repaired population can legitimately drive the
/// finding count to zero; nothing can legitimately drive these to zero except a broken scan.
const MIN_DISTINCT_TOKENS: usize = 400;
const MIN_REACHABLE_ANCHORS: usize = 80;

fn git(root: &Path, args: &[&str]) -> String {
    let out = Command::new("git")
        .current_dir(root)
        .args(args)
        .output()
        .unwrap_or_else(|error| {
            panic!(
                "git must run: this guard is DERIVED from the repository, so without git the \
                 population is unknown and no disclosure can be made ({error})"
            )
        });
    // `git grep` exits 1 on "no matches", which is a legitimate exit and an illegitimate
    // *answer* — the floors below refuse it rather than this call pretending it succeeded.
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn is_anchor_token(token: &str) -> bool {
    (8..=40).contains(&token.len())
        && token
            .chars()
            .all(|c| c.is_ascii_digit() || ('a'..='f').contains(&c))
}

/// One harvest of `HEAD`, in a single `git grep`, attributed by file.
///
/// Returns `(token -> files, binary_files_skipped)`. Parsing is asserted total: a line the
/// reader cannot parse is a **refusal**, never a record quietly dropped, because a scan that
/// skips what it cannot read silently redefines its own denominator.
fn harvest(root: &Path, extra_pathspec: &[&str]) -> (BTreeMap<String, BTreeSet<String>>, usize) {
    let mut args = vec![
        "grep",
        "-I",
        "-o",
        "-E",
        r"\b[0-9a-f]{8,40}\b",
        "HEAD",
        "--",
    ];
    args.extend_from_slice(extra_pathspec);
    let text = git(root, &args);

    // The same command WITHOUT -I, only to count what -I removed. Declared, not dropped.
    let mut bin_args = args.clone();
    bin_args.remove(1);
    let binary = git(root, &bin_args)
        .lines()
        .filter(|line| line.starts_with("Binary file "))
        .count();

    (parse_harvest(&text), binary)
}

/// The harvest parser, split out so its **refusal is reachable from a test**.
///
/// This existed inline first and a planted mutant that turned each refusal into a `continue`
/// survived the entire campaign: a healthy tree emits no unparsable line, so the check could
/// never fire and was decorative. That is the same disease as an unreachable anti-vacuity
/// floor, and the same cure — inject the input rather than wait for it. A scan that skips what
/// it cannot read silently redefines its own denominator, which is the failure mode that let a
/// sibling scan in this repository report 786 of 1880 as a total.
fn parse_harvest(text: &str) -> BTreeMap<String, BTreeSet<String>> {
    let mut found: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for line in text.lines() {
        let rest = line.strip_prefix("HEAD:").unwrap_or_else(|| {
            panic!(
                "harvest line {line:?} does not carry the HEAD: prefix this reader requires; \
                 an unparsable line is a REFUSAL, never a record dropped from the denominator"
            )
        });
        let (path, token) = rest
            .rsplit_once(':')
            .unwrap_or_else(|| panic!("harvest line {line:?} carries no path/token separator"));
        assert!(
            is_anchor_token(token),
            "harvest produced token {token:?} for {path}, which is not 8-40 lowercase hex — \
             the parse is wrong and every count derived from it would be fiction"
        );
        found
            .entry(token.to_owned())
            .or_default()
            .insert(path.to_owned());
    }
    found
}

/// Which of `tokens` name a commit, and whether it is reachable from `refs/heads/main`.
///
/// One `git cat-file --batch-check` for the whole set. **The join is positional**: batch-check
/// prints the RESOLVED FULL OID, never the token it was asked about, so keying its output by
/// the echoed oid invents entries that never appeared in any file. That is not hypothetical —
/// it was done while building this guard, and a `defaultdict`-shaped lookup that cannot fail
/// reported 119 tokens outside `.beads` while listing five. The length assertion below is what
/// makes the join able to fail.
fn classify(root: &Path, tokens: &[String]) -> BTreeMap<String, bool> {
    let main: BTreeSet<String> = git(root, &["rev-list", "refs/heads/main"])
        .lines()
        .map(str::to_owned)
        .collect();
    assert!(
        main.len() > 200,
        "rev-list refs/heads/main returned {} commits — a history this short is a broken scan, \
         and it would classify every anchor as backup-only",
        main.len()
    );

    let mut child = Command::new("git")
        .current_dir(root)
        .args(["cat-file", "--batch-check"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .expect("git cat-file --batch-check must spawn");
    child
        .stdin
        .take()
        .expect("stdin was piped")
        .write_all(tokens.join("\n").as_bytes())
        .expect("the token list must be writable to batch-check");
    let out = child.wait_with_output().expect("batch-check must complete");
    let lines: Vec<&str> = String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(str::to_owned)
        .collect::<Vec<String>>()
        .leak()
        .iter()
        .map(String::as_str)
        .collect();

    assert_eq!(
        lines.len(),
        tokens.len(),
        "batch-check returned {} lines for {} inputs — the positional join is invalid and \
         every count below would be fiction",
        lines.len(),
        tokens.len()
    );

    let mut verdict = BTreeMap::new();
    for (token, line) in tokens.iter().zip(lines) {
        let mut fields = line.split_whitespace();
        let (Some(oid), Some(kind)) = (fields.next(), fields.next()) else {
            continue; // "<token> missing" — not an object at all
        };
        if kind == "commit" {
            verdict.insert(token.clone(), main.contains(oid));
        }
    }
    verdict
}

struct Census {
    backup_by_file: BTreeMap<String, usize>,
    distinct_tokens: usize,
    reachable: usize,
    binary_skipped: usize,
}

fn measure(root: &Path) -> Census {
    let (found, binary_skipped) = harvest(root, EXCLUDED);
    let tokens: Vec<String> = found.keys().cloned().collect();
    let verdict = classify(root, &tokens);

    let mut backup_by_file: BTreeMap<String, usize> = BTreeMap::new();
    let mut reachable = 0usize;
    for (token, is_reachable) in &verdict {
        if *is_reachable {
            reachable += 1;
        } else {
            for file in &found[token] {
                *backup_by_file.entry(file.clone()).or_default() += 1;
            }
        }
    }
    Census {
        backup_by_file,
        distinct_tokens: found.len(),
        reachable,
        binary_skipped,
    }
}

fn root() -> PathBuf {
    fln_conformance::checked_workspace_root!()
}

/// The allowance judgement, in **one** place.
///
/// The live assertion and every planted mutant call this, deliberately: a planted test that
/// re-implements the predicate in its own closure proves that *the copy* fires and leaves the
/// production path free to be gutted while the campaign still reports a kill. That is the
/// second-copy drift this repository names as its most-repeated defect, and the first version
/// of this file had it.
fn allowance_violations(measured: &BTreeMap<String, usize>) -> Vec<String> {
    let declared: BTreeMap<&str, usize> = BACKUP_ONLY_ALLOWANCE.iter().copied().collect();
    let mut faults = Vec::new();
    for (file, count) in measured {
        match declared.get(file.as_str()) {
            None => faults.push(format!("{file}: {count} backup-only, declared nowhere")),
            Some(allowed) if count > allowed => faults.push(format!(
                "{file}: declared {allowed}, measured {count} ({:+})",
                *count as isize - *allowed as isize
            )),
            Some(_) => {}
        }
    }
    faults
}

/// The anti-vacuity judgement, likewise in one place so the floors are **reachable from a
/// test**. A floor exists for the day the scan breaks, which is precisely the day a healthy
/// tree cannot reproduce — so the inputs are injected rather than waited for.
fn vacuity_faults(census: &Census) -> Vec<String> {
    let mut faults = Vec::new();
    if census.distinct_tokens < MIN_DISTINCT_TOKENS {
        faults.push(format!(
            "harvested {} distinct hex tokens, floor {MIN_DISTINCT_TOKENS}: the grep, the \
             pathspec or the parse broke. A scan that returns nothing and a tree with nothing \
             to find are the same green, and only this floor separates them",
            census.distinct_tokens
        ));
    }
    if census.reachable < MIN_REACHABLE_ANCHORS {
        faults.push(format!(
            "only {} anchors classify as reachable, floor {MIN_REACHABLE_ANCHORS}: rev-list or \
             the positional join broke, and a broken classifier calls every anchor backup-only",
            census.reachable
        ));
    }
    if census.binary_skipped != BINARY_FILES_SKIPPED {
        faults.push(format!(
            "the harvest skipped {} binary file(s), disclosed {BINARY_FILES_SKIPPED}: a filter \
             that silently drops what it cannot parse is a sampler, not a scan",
            census.binary_skipped
        ));
    }
    faults
}

/// **The property AGENTS.md says the `vdi4` close did not buy: a hundred more backup-only
/// anchors fail the build.** One-way per file, plus refusal of any undeclared file.
#[test]
fn the_backup_only_anchor_population_may_shrink_and_may_not_grow() {
    let census = measure(&root());
    let faults = allowance_violations(&census.backup_by_file);
    assert!(
        faults.is_empty(),
        "the backup-only commit-anchor population is no longer what this file declares:\n  {}\n\n\
         An anchor like this RESOLVES — `git show` and `git cat-file -t` both succeed, because \
         refs/original keeps every pre-rewrite commit alive in this clone — while denoting \
         nothing a reader can verify from main.\n\n\
         Repair it to the content-identical twin on main if one exists: identical patch-id, \
         byte-identical diff text, identical touched-path list and identical resulting blobs. \
         Subject and author date agreeing prove NOTHING on their own. If no twin exists, \
         declare the count here and say why.\n\n\
         This allowance is ONE-WAY: it may fall freely as anchors are repaired and may not \
         rise, and a file declared nowhere may carry none at all. Do not raise a number to go \
         green — silent growth is the whole defect this guard exists to refuse.",
        faults.join("\n  ")
    );
}

/// The derivation is reconciled against a cheap independent signal, and a derived zero is
/// refused as a broken scan rather than reported as a clean tree.
///
/// The floors sit on the **denominator**, which is the only place they can be honest: a
/// repaired tree may legitimately show zero backup-only anchors, so flooring the *finding*
/// count would forbid the very outcome this guard wants. Nothing legitimately drives the token
/// or reachable counts to zero.
#[test]
fn a_derived_zero_is_refused_as_a_broken_scan() {
    let census = measure(&root());
    let faults = vacuity_faults(&census);
    assert!(
        faults.is_empty(),
        "the scan cannot be trusted to have run:\n  {}",
        faults.join("\n  ")
    );

    // The floors are exercised against INJECTED inputs, because a healthy tree cannot produce
    // the state they defend against and an unreachable floor is decorative.
    let broken = Census {
        backup_by_file: BTreeMap::new(),
        distinct_tokens: 0,
        reachable: 0,
        binary_skipped: BINARY_FILES_SKIPPED,
    };
    assert_eq!(
        vacuity_faults(&broken).len(),
        2,
        "an empty scan must raise BOTH denominator floors; it raised {:?}. A scan returning \
         nothing would otherwise report a clean tree",
        vacuity_faults(&broken)
    );
    let sampler = Census {
        backup_by_file: census.backup_by_file.clone(),
        distinct_tokens: census.distinct_tokens,
        reachable: census.reachable,
        binary_skipped: BINARY_FILES_SKIPPED + 1,
    };
    assert_eq!(
        vacuity_faults(&sampler).len(),
        1,
        "a fourth binary file joining the tree must move the disclosure rather than the \
         denominator silently"
    );

    // The independent signal: the excluded beads population, harvested by a DIFFERENT
    // pathspec through the same code path. If the classifier were broken this would collapse
    // too, so agreement between two disjoint scopes is worth more than either alone.
    let (beads, _) = harvest(&root(), &[".beads/issues.jsonl"]);
    let tokens: Vec<String> = beads.keys().cloned().collect();
    let verdict = classify(&root(), &tokens);
    let beads_backup = verdict.values().filter(|reachable| !**reachable).count();
    assert!(
        beads_backup >= BEADS_BACKUP_ONLY_FLOOR,
        ".beads/issues.jsonl shows {beads_backup} backup-only anchors, below the disclosed \
         floor of {BEADS_BACKUP_ONLY_FLOOR}. This population is excluded from the allowance \
         because every pane's br rewrites the file, but it is floored rather than ignored: it \
         may churn upward freely and cannot silently vanish"
    );
}

/// **The synthetic control, which is the only thing that still works when the population
/// reaches zero.** A guard whose live population has been fully repaired becomes decorative —
/// every assertion passes against an empty set, including a broken classifier's. So the
/// discrimination is proved against planted inputs rather than against the tree's own state.
#[test]
fn the_classifier_separates_a_reachable_anchor_from_a_backup_only_one() {
    let root = root();

    // A commit that is on main by construction: main's own tip.
    let head = git(&root, &["rev-parse", "refs/heads/main"]);
    let head = head.trim();
    // A commit that exists in this clone and is NOT on main, DERIVED rather than written down.
    //
    // Naming one here would defeat the guard's own rule: this file is inside the scope it
    // scans, so a hard-coded pre-rewrite sha would make the file cite a backup-only anchor and
    // need an allowance row it cannot have before it is tracked — a bootstrap the HEAD-reading
    // harvest makes unsatisfiable in both directions. Deriving it also survives the sha the
    // literal would have named being garbage-collected.
    let backup_only = git(&root, &["rev-list", "--all", "--not", "refs/heads/main"]);
    let backup_only = backup_only
        .lines()
        .next()
        .unwrap_or_else(|| {
            panic!(
                "no commit is reachable from any ref while absent from main, so the NEGATIVE \
                 control cannot be constructed and a green here would prove only that the \
                 positive control fired. If the backup refs have genuinely been pruned, every \
                 rotted anchor in the allowance has become an unresolvable object rather than \
                 a backup-only commit, and the allowance rows will say so"
            )
        })
        .to_owned();

    let verdict = classify(&root, &[head.to_owned(), backup_only.clone()]);
    let backup_only = backup_only.as_str();
    const BACKUP_ONLY_PLACEHOLDER: &str = "the derived backup-only commit";

    assert_eq!(
        verdict.get(head),
        Some(&true),
        "main's own tip did not classify as reachable — the positive control failed, so a \
         green from this guard would mean nothing"
    );
    assert_eq!(
        verdict.get(backup_only),
        Some(&false),
        "{BACKUP_ONLY_PLACEHOLDER} {backup_only} classified as reachable or as a non-commit. It \
         must resolve AND be absent from main. Without this cell a green here would prove only \
         that the positive control fired, which is the shape of every guard that passes because \
         it can no longer fail"
    );
}

/// A hundred more backup-only anchors must fail, and one more must fail, and a *repair* must
/// not. All three planted against the real measured population rather than a fixture, because
/// a fixture proves the comparison fires and says nothing about the production path.
#[test]
fn planted_growth_is_refused_and_a_planted_repair_is_not() {
    let census = measure(&root());
    assert!(
        allowance_violations(&census.backup_by_file).is_empty(),
        "the live tree must be clean before a plant against it means anything"
    );

    // +100 in a file that already carries an allowance.
    let mut hundred = census.backup_by_file.clone();
    *hundred
        .entry("ci/VERIFICATION_MANIFEST.jsonl".to_owned())
        .or_default() += 100;
    assert_eq!(
        allowance_violations(&hundred).len(),
        1,
        "a hundred new backup-only anchors in an already-declared file did not fail — this is \
         the exact property AGENTS.md records the vdi4 close as NOT having bought"
    );

    // +1 is enough. A guard that only notices a hundred is a guard that notices nothing until
    // it is far too late.
    let mut one_more = census.backup_by_file.clone();
    *one_more
        .entry("ci/VERIFICATION_MANIFEST.jsonl".to_owned())
        .or_default() += 1;
    assert_eq!(
        allowance_violations(&one_more).len(),
        1,
        "one more must fail too"
    );

    // A file with no allowance at all, which is how a NEW file joins silently.
    let mut newcomer = census.backup_by_file.clone();
    newcomer.insert("crates/fln-kernel/src/lib.rs".to_owned(), 1);
    let faults = allowance_violations(&newcomer);
    assert_eq!(faults.len(), 1, "an undeclared file must fail");
    assert!(
        faults[0].contains("declared nowhere"),
        "the undeclared case must be reported as such rather than as growth — they have \
         different repairs: {faults:?}"
    );

    // A repair must NOT redden. Equality here would be a wall against the good event, which
    // this repository has already paid for once.
    let mut repaired = census.backup_by_file.clone();
    repaired.remove("ci/VERIFICATION_MANIFEST.jsonl");
    assert!(
        allowance_violations(&repaired).is_empty(),
        "repairing every anchor in a declared file reddened the guard — one-way means a count \
         may fall freely"
    );
}

/// The parser accepts a well-formed harvest, so the refusals below are not a blanket refusal.
#[test]
fn the_harvest_parser_accepts_a_well_formed_record() {
    let parsed = parse_harvest("HEAD:ci/a.txt:deadbeef\nHEAD:ci/b.txt:deadbeef\n");
    assert_eq!(parsed.len(), 1, "one distinct token");
    assert_eq!(
        parsed["deadbeef"].len(),
        2,
        "attributed to both files that cite it"
    );
}

/// **The mutant that survived the first campaign.** Turning this refusal into a `continue`
/// makes the scan a sampler, and a healthy tree never produces the line that would reveal it.
#[test]
#[should_panic(expected = "an unparsable line is a REFUSAL")]
fn an_unparsable_harvest_line_is_refused_rather_than_skipped() {
    parse_harvest("HEAD:ci/a.txt:deadbeef\nBinary file HEAD:tribunal/x.olean matches\n");
}

/// The token-shape half of the same refusal, gutted independently.
#[test]
#[should_panic(expected = "which is not 8-40 lowercase hex")]
fn a_harvest_token_of_the_wrong_shape_is_refused() {
    parse_harvest("HEAD:ci/a.txt:NOTHEXAT\n");
}

/// The declared allowance may not name a file that does not exist, or carry a zero: both are
/// slots a future regression could occupy silently, and `k60n` had to delete rather than zero
/// its residue rows for exactly this reason.
#[test]
fn the_allowance_carries_no_dead_or_zero_rows() {
    let root = root();
    let tracked: BTreeSet<String> = git(&root, &["ls-files"])
        .lines()
        .map(str::to_owned)
        .collect();
    assert!(tracked.len() > 500, "git ls-files returned a broken scan");

    let census = measure(&root);
    for (file, allowed) in BACKUP_ONLY_ALLOWANCE {
        assert!(
            tracked.contains(*file),
            "{file} is declared in the allowance and is not tracked — a dead row keeps a slot \
             that a future file at that path could occupy without review"
        );
        assert!(
            *allowed > 0,
            "{file} is declared with an allowance of 0; delete the row instead, because a \
             zero row is an open slot that regrows silently up to its old count"
        );
        assert!(
            census.backup_by_file.contains_key(*file),
            "{file} is declared with an allowance of {allowed} but now carries NO backup-only \
             anchor. That is a completed repair: delete the row rather than leaving it, or the \
             path can regrow to {allowed} without the guard noticing"
        );
    }
}
