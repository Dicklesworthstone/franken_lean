//! `mutation_kill_ledger_model` — the named suite for td9's first campaign framework:
//! the mutation kill ledger (`fln_conformance::campaign`).
//!
//! # What is proven here
//!
//! The kill law (only a stated-reason failure kills; the five non-kill kinds are named
//! and never promote either way), the denominator law (equivalent and unbuildable are
//! evidenced exclusions that stay counted and cannot shrink the denominator silently),
//! the binding law (all seven binds, each refusal naming its field), the conservation
//! and completion laws over a mixed campaign, the NDJSON artifact laws
//! (schema-versioned, canonical, round-tripping, tamper-refusing), and the framework's
//! own self-mutants td9 names: **false kill** and **denominator drop**.
//!
//! # The real controlled target
//!
//! td9 requires each framework to be proven on a real controlled fln-conformance
//! target rather than a toy. The controlled target is uagk's mandated-mutant campaign:
//! its committed receipts (`evidence/mandated_mutants/kills.jsonl`) are classified
//! through the model — two recorded campaigns, three mutants each, every killer
//! checked for the stated reason — and the model's conservation law must reconcile
//! them exactly. The receipts' production paths are also resolved, so a receipt
//! pointing at dead code is caught here rather than believed.

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use fln_conformance::campaign::{
    CampaignError, Disposition, KILL_LEDGER_SCHEMA, KillLedger, KillVerdict, MutantBinding,
    MutationKiller, MutationSite, NotAKill, Observation, mutation_killer_recipe_digest,
    mutation_site_digest,
};

fn root() -> PathBuf {
    fln_conformance::checked_workspace_root!()
}

/// A binding that passes every law; cells break one thing at a time from here.
fn good_binding(mutant_id: &str) -> MutantBinding {
    MutantBinding::new(
        mutant_id,
        "25170f8c3a3bea3e4839cf041896ea600dab27c3",
        "943b55bcb8dec7e47db9276b59db36e694a6804263619e663f3b5c1e155e014e",
        "nightly-2026-07-13+test-profile",
        "crates/fln-kernel/src/admit.rs",
        "kr606_negative_occurrences_are_rejected fails with the KR-606 positivity judgment",
        "test-target-only",
    )
    .expect("the fixture binding is well-formed")
}

// ---------------------------------------------------------------------------
// The binding law: seven binds, each refusal naming its field
// ---------------------------------------------------------------------------

#[test]
fn a_binding_refuses_each_missing_field_naming_it() {
    let cases: [(&str, [&str; 7]); 7] = [
        (
            "mutant_id",
            [
                "", "a1b2c3d4", "a1b2c3d4", "build", "target", "disc", "proof",
            ],
        ),
        (
            "source_root_digest",
            ["id", "", "a1b2c3d4", "build", "target", "disc", "proof"],
        ),
        (
            "patch_digest",
            ["id", "a1b2c3d4", "", "build", "target", "disc", "proof"],
        ),
        (
            "build_identity",
            ["id", "a1b2c3d4", "a1b2c3d4", "", "target", "disc", "proof"],
        ),
        (
            "target_path",
            ["id", "a1b2c3d4", "a1b2c3d4", "build", "", "disc", "proof"],
        ),
        (
            "expected_discriminator",
            ["id", "a1b2c3d4", "a1b2c3d4", "build", "target", "", "proof"],
        ),
        (
            "release_exclusion_proof",
            ["id", "a1b2c3d4", "a1b2c3d4", "build", "target", "disc", ""],
        ),
    ];
    for (field, args) in cases {
        let err = MutantBinding::new(
            args[0], args[1], args[2], args[3], args[4], args[5], args[6],
        )
        .expect_err(&format!("an empty {field} must be refused"));
        assert_eq!(
            err,
            CampaignError::BindingFieldInvalid { field },
            "the refusal must name {field}"
        );
    }
}

#[test]
fn a_digest_field_refuses_a_non_hex_token() {
    // A digest binds bytes; a label is not a bind. Only the two digest fields are
    // hex-checked — the others are legitimately prose.
    let err = MutantBinding::new(
        "id",
        "not-a-digest-at-all",
        "a1b2c3d4",
        "build",
        "target",
        "disc",
        "proof",
    )
    .expect_err("a non-hex source root must be refused");
    assert_eq!(
        err,
        CampaignError::BindingFieldInvalid {
            field: "source_root_digest"
        }
    );
}

// ---------------------------------------------------------------------------
// The kill law: one observation kills; five kinds do not, and none survives
// ---------------------------------------------------------------------------

#[test]
fn only_a_stated_reason_failure_is_a_kill() {
    let cases: [(Observation, KillVerdict); 7] = [
        (Observation::FailedForStatedReason, KillVerdict::Killed),
        (Observation::Passed, KillVerdict::Survived),
        (
            Observation::WrongFailureReason,
            KillVerdict::NotKilled(NotAKill::AnotherMutant),
        ),
        (
            Observation::CompileFailure,
            KillVerdict::NotKilled(NotAKill::CompileFailure),
        ),
        (
            Observation::UnrelatedGateFailure,
            KillVerdict::NotKilled(NotAKill::UnrelatedGateFailure),
        ),
        (
            Observation::Timeout,
            KillVerdict::NotKilled(NotAKill::Timeout),
        ),
        (
            Observation::HarnessFault,
            KillVerdict::NotKilled(NotAKill::HarnessFault),
        ),
    ];
    for (observation, expected) in cases {
        assert_eq!(
            observation.verdict(),
            expected,
            "{observation:?} misclassified"
        );
    }
}

#[test]
fn a_compile_failure_recorded_as_a_kill_is_refused_by_the_model() {
    // The false-kill self-mutant, planted at the API: a campaign that observed a
    // compile failure must come out NotKilled, and the summary must not count it as
    // killed or survived. FL-INV-07: inconclusive is not promoted either way.
    let mut ledger = KillLedger::new();
    ledger
        .register(good_binding("m1"), Disposition::Active)
        .expect("register");
    let verdict = ledger
        .record("m1", Observation::CompileFailure)
        .expect("recording a compile failure is legal; it is just not a kill");
    assert_eq!(verdict, KillVerdict::NotKilled(NotAKill::CompileFailure));
    let summary = ledger.summary();
    assert_eq!(summary.killed, 0, "a compile failure is never a kill");
    assert_eq!(
        summary.survived, 0,
        "a compile failure says nothing about survival"
    );
    assert_eq!(summary.not_killed, 1);
}

// ---------------------------------------------------------------------------
// The denominator law: exclusions are evidenced, counted, and never silent
// ---------------------------------------------------------------------------

#[test]
fn an_exclusion_needs_evidence_to_leave_the_denominator() {
    // The denominator-drop self-mutant, planted: without evidence an exclusion is a
    // typed refusal, and the error says which kind and which mutant.
    for (disposition, kind) in [
        (
            Disposition::Equivalent {
                evidence: String::new(),
            },
            "equivalent",
        ),
        (
            Disposition::Unbuildable {
                evidence: "   ".to_string(),
            },
            "unbuildable",
        ),
    ] {
        let mut ledger = KillLedger::new();
        let err = ledger
            .register(good_binding("m1"), disposition)
            .expect_err("an evidence-less exclusion must be refused");
        assert_eq!(
            err,
            CampaignError::ExclusionWithoutEvidence {
                mutant_id: "m1".to_string(),
                kind,
            }
        );
    }
}

#[test]
fn an_excluded_mutant_stays_counted_and_cannot_be_run() {
    let mut ledger = KillLedger::new();
    ledger
        .register(
            good_binding("equiv"),
            Disposition::Equivalent {
                evidence: "reviewed: the mutation rewrites x+x to 2*x under this typing"
                    .to_string(),
            },
        )
        .expect("evidenced exclusion registers");
    let summary = ledger.summary();
    assert_eq!(summary.registered, 1);
    assert_eq!(summary.active, 0, "the exclusion leaves the denominator");
    assert_eq!(summary.equivalent, 1, "but stays counted");
    let err = ledger
        .record("equiv", Observation::Passed)
        .expect_err("a run on an excluded mutant is a contradiction");
    assert_eq!(
        err,
        CampaignError::RunOnExcludedMutant {
            mutant_id: "equiv".to_string()
        }
    );
}

// ---------------------------------------------------------------------------
// Conservation, completion, and duplicate laws over a mixed campaign
// ---------------------------------------------------------------------------

#[test]
fn the_denominator_is_conserved_under_a_mixed_campaign() {
    let mut ledger = KillLedger::new();
    for (id, disposition) in [
        ("k1", Disposition::Active),
        ("k2", Disposition::Active),
        ("s1", Disposition::Active),
        ("n1", Disposition::Active),
        (
            "e1",
            Disposition::Equivalent {
                evidence: "alpha-equivalent under the translation".to_string(),
            },
        ),
        (
            "u1",
            Disposition::Unbuildable {
                evidence: "type error in the mutated tree, build log retained".to_string(),
            },
        ),
    ] {
        ledger
            .register(good_binding(id), disposition)
            .expect("register");
    }
    ledger
        .record("k1", Observation::FailedForStatedReason)
        .expect("run");
    ledger
        .record("k2", Observation::FailedForStatedReason)
        .expect("run");
    ledger.record("s1", Observation::Passed).expect("run");
    ledger.record("n1", Observation::Timeout).expect("run");
    let summary = ledger.summary();
    assert_eq!(summary.registered, 6);
    assert_eq!(summary.active, 4);
    assert_eq!(summary.equivalent, 1);
    assert_eq!(summary.unbuildable, 1);
    assert_eq!(summary.killed, 2);
    assert_eq!(summary.survived, 1);
    assert_eq!(summary.not_killed, 1);
    assert_eq!(
        summary.runs(),
        summary.killed + summary.survived + summary.not_killed,
        "conservation: every run is accounted for"
    );
    assert_eq!(summary.runs(), 4, "exactly the active mutants ran");
    assert!(
        ledger.unrun_mutants().is_empty(),
        "the campaign is complete"
    );
}

#[test]
fn a_campaign_names_its_unrun_mutants_instead_of_averaging_them_away() {
    let mut ledger = KillLedger::new();
    ledger
        .register(good_binding("ran"), Disposition::Active)
        .expect("register");
    ledger
        .register(good_binding("unrun"), Disposition::Active)
        .expect("register");
    ledger
        .register(
            good_binding("excluded"),
            Disposition::Unbuildable {
                evidence: "does not typecheck; build log retained".to_string(),
            },
        )
        .expect("register");
    ledger
        .record("ran", Observation::FailedForStatedReason)
        .expect("run");
    assert_eq!(
        ledger.unrun_mutants(),
        vec!["unrun".to_string()],
        "the unrun active mutant is named; the excluded one is not a campaign gap"
    );
}

#[test]
fn a_second_verdict_for_one_mutant_is_refused() {
    // The overwrite vector: a first Survived quietly becoming a kill on re-record.
    let mut ledger = KillLedger::new();
    ledger
        .register(good_binding("m1"), Disposition::Active)
        .expect("register");
    ledger.record("m1", Observation::Passed).expect("first run");
    let err = ledger
        .record("m1", Observation::FailedForStatedReason)
        .expect_err("a second verdict must be refused");
    assert_eq!(
        err,
        CampaignError::DuplicateRun {
            mutant_id: "m1".to_string()
        }
    );
    assert_eq!(
        ledger.summary().survived,
        1,
        "the first verdict stands; nothing was overwritten"
    );
}

#[test]
fn a_run_on_an_unknown_mutant_is_refused() {
    let mut ledger = KillLedger::new();
    let err = ledger
        .record("ghost", Observation::FailedForStatedReason)
        .expect_err("an unregistered mutant cannot accrue a kill");
    assert_eq!(
        err,
        CampaignError::UnknownMutant {
            mutant_id: "ghost".to_string()
        }
    );
}

#[test]
fn a_duplicate_registration_is_refused() {
    let mut ledger = KillLedger::new();
    ledger
        .register(good_binding("m1"), Disposition::Active)
        .expect("first");
    let err = ledger
        .register(good_binding("m1"), Disposition::Active)
        .expect_err("second registration of the same id must be refused");
    assert_eq!(
        err,
        CampaignError::DuplicateRegistration {
            mutant_id: "m1".to_string()
        }
    );
}

// ---------------------------------------------------------------------------
// The NDJSON artifact laws: schema-versioned, canonical, round-tripping
// ---------------------------------------------------------------------------

#[test]
fn the_ledger_rows_are_schema_versioned_canonical_and_round_trip() {
    let mut ledger = KillLedger::new();
    ledger
        .register(good_binding("m1"), Disposition::Active)
        .expect("register");
    ledger
        .record("m1", Observation::FailedForStatedReason)
        .expect("run");
    ledger
        .register(
            good_binding("m2"),
            Disposition::Equivalent {
                evidence: "equivalence argument retained".to_string(),
            },
        )
        .expect("register");
    let ndjson = ledger.to_ndjson();
    let lines: Vec<&str> = ndjson.lines().collect();
    assert_eq!(lines.len(), 2, "one row per mutant");
    for line in &lines {
        assert!(
            line.starts_with(&format!("{{\"schema\":\"{KILL_LEDGER_SCHEMA}\",")),
            "every row leads with the schema token: {line}"
        );
    }
    // Round-trip: every field survives the parse, including the verdict and the
    // exclusion evidence.
    let (binding, disposition, verdict) =
        KillLedger::row_from_ndjson(lines[0]).expect("row 0 parses");
    assert_eq!(binding, good_binding("m1"));
    assert_eq!(disposition, Disposition::Active);
    assert_eq!(verdict, Some(KillVerdict::Killed));
    let (_, disposition, verdict) = KillLedger::row_from_ndjson(lines[1]).expect("row 1 parses");
    assert_eq!(
        disposition,
        Disposition::Equivalent {
            evidence: "equivalence argument retained".to_string()
        }
    );
    assert_eq!(verdict, None, "an unrun excluded mutant stays unrun");
}

#[test]
fn the_emitted_row_is_byte_exact_canonical() {
    // The golden row: field order, quoting, and spacing are the canonical form a
    // retention check can bind to. Any emitter drift breaks this byte comparison.
    let mut ledger = KillLedger::new();
    ledger
        .register(good_binding("m1"), Disposition::Active)
        .expect("register");
    ledger.record("m1", Observation::Timeout).expect("run");
    let expected = concat!(
        "{\"schema\":\"fln.mutation-kill-ledger/1\",",
        "\"mutant_id\":\"m1\",",
        "\"source_root_digest\":\"25170f8c3a3bea3e4839cf041896ea600dab27c3\",",
        "\"patch_digest\":\"943b55bcb8dec7e47db9276b59db36e694a6804263619e663f3b5c1e155e014e\",",
        "\"build_identity\":\"nightly-2026-07-13+test-profile\",",
        "\"target_path\":\"crates/fln-kernel/src/admit.rs\",",
        "\"expected_discriminator\":\"kr606_negative_occurrences_are_rejected fails with the KR-606 positivity judgment\",",
        "\"release_exclusion_proof\":\"test-target-only\",",
        "\"disposition\":\"active\",",
        "\"exclusion_evidence\":\"\",",
        "\"verdict\":\"not_killed\",",
        "\"not_a_kill\":\"timeout\"}\n"
    );
    assert_eq!(ledger.to_ndjson(), expected);
}

#[test]
fn a_tampered_row_is_refused_at_parse() {
    let mut ledger = KillLedger::new();
    ledger
        .register(good_binding("m1"), Disposition::Active)
        .expect("register");
    ledger
        .record("m1", Observation::FailedForStatedReason)
        .expect("run");
    let line = ledger
        .to_ndjson()
        .lines()
        .next()
        .expect("one row")
        .to_string();

    let wrong_schema = line.replacen(KILL_LEDGER_SCHEMA, "fln.mutation-kill-ledger/0", 1);
    assert!(
        matches!(
            KillLedger::row_from_ndjson(&wrong_schema),
            Err(CampaignError::NdjsonInvalid { .. })
        ),
        "a drifted schema token is refused"
    );

    let promoted = line.replacen("\"killed\"", "\"survived\"", 1);
    let (_, _, verdict) = KillLedger::row_from_ndjson(&promoted).expect("a legal edit parses");
    assert_eq!(
        verdict,
        Some(KillVerdict::Survived),
        "the parser reports what the row says, not what we wish — which is why the \
         artifact's authority comes from the campaign, and the parse only enforces shape"
    );

    let unknown_verdict = line.replacen("\"killed\"", "\"vaporized\"", 1);
    assert!(
        matches!(
            KillLedger::row_from_ndjson(&unknown_verdict),
            Err(CampaignError::NdjsonInvalid { .. })
        ),
        "an unknown verdict token is refused"
    );

    let gutted = line.replacen("25170f8c3a3bea3e4839cf041896ea600dab27c3", "", 1);
    assert_eq!(
        KillLedger::row_from_ndjson(&gutted),
        Err(CampaignError::BindingFieldInvalid {
            field: "source_root_digest"
        }),
        "a tampered bind fails the same law a hand-written one does"
    );
}

// ---------------------------------------------------------------------------
// The real controlled target: uagk's mandated-mutant campaign receipts
// ---------------------------------------------------------------------------

/// One receipt row's fields, extracted with the same delimiter-blind parser uagk pins
/// (`receipt_field`): values are read, never their delimiters.
fn receipt_field(row: &str, key: &str) -> Option<String> {
    let at = row.find(&format!("\"{key}\":"))? + key.len() + 3;
    let rest = &row[at..];
    if let Some(stripped) = rest.strip_prefix('"') {
        stripped.find('"').map(|end| stripped[..end].to_string())
    } else {
        rest.find([',', '}']).map(|end| rest[..end].to_string())
    }
}

#[test]
fn the_real_mandated_campaign_classifies_through_the_model() {
    let path = root().join("crates/fln-conformance/evidence/mandated_mutants/kills.jsonl");
    let text = fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "the committed kill receipts must exist at {}: {e}",
            path.display()
        )
    });
    let rows: Vec<&str> = text.lines().filter(|l| !l.trim().is_empty()).collect();
    assert!(
        rows.len() >= 3,
        "the real campaign recorded fewer than its three plantable mutants: {}",
        rows.len()
    );

    // Group by source root: each campaign run is its own ledger (the model's
    // duplicate-run law forbids folding two campaigns into one).
    let mut campaigns: Vec<(String, Vec<&str>)> = Vec::new();
    for row in &rows {
        let head = receipt_field(row, "head_commit").expect("receipt carries head_commit");
        match campaigns.iter_mut().find(|(h, _)| *h == head) {
            Some((_, group)) => group.push(row),
            None => campaigns.push((head, vec![row])),
        }
    }
    assert!(
        !campaigns.is_empty(),
        "at least one real campaign is on record"
    );

    for (head, group) in campaigns {
        let mut ledger = KillLedger::new();
        for row in &group {
            let name = receipt_field(row, "name").expect("receipt carries name");
            let site_file = receipt_field(row, "site_file").expect("receipt carries site_file");
            let site_digest =
                receipt_field(row, "site_digest").expect("receipt carries site_digest");
            let killers = receipt_field(row, "killers").expect("receipt carries killers");

            // Production-path reachability: the receipt's target must exist as real
            // code, or the kill was scored against nothing (the empty-referent shape).
            let target = root().join(&site_file);
            assert!(
                target.is_file(),
                "receipt for `{name}` targets {site_file}, which does not exist"
            );

            let killed: usize = receipt_field(row, "killed")
                .and_then(|v| v.parse().ok())
                .expect("receipt carries a numeric killed count");
            let reasons: usize = receipt_field(row, "reasons_matched")
                .and_then(|v| v.parse().ok())
                .expect("receipt carries a numeric reasons_matched count");
            let survivors = receipt_field(row, "survivors").expect("receipt carries survivors");

            let binding = MutantBinding::new(
                &name,
                &head,
                &site_digest,
                "pinned-nightly (see rust-toolchain.toml)",
                &site_file,
                &format!("killers {killers} failing for the stated reasons"),
                "test-target-only",
            )
            .expect("the real receipt's binds satisfy the model");

            // The classification the campaign's own evidence supports: every killer
            // died for the stated reason with no survivors — or the row is not a kill.
            let observation = if survivors == "[]" && reasons == killed && killed > 0 {
                Observation::FailedForStatedReason
            } else if survivors != "[]" {
                Observation::Passed
            } else {
                Observation::WrongFailureReason
            };
            ledger
                .register(binding, Disposition::Active)
                .expect("register");
            ledger.record(&name, observation).expect("record");
        }
        let summary = ledger.summary();
        assert_eq!(
            summary.killed, summary.active,
            "campaign {head}: every plantable mandated mutant died for its stated reason"
        );
        assert_eq!(summary.survived, 0, "campaign {head}: no survivor");
        assert_eq!(
            summary.runs(),
            summary.killed + summary.survived + summary.not_killed,
            "campaign {head}: conservation"
        );
        assert!(
            ledger.unrun_mutants().is_empty(),
            "campaign {head} is complete"
        );
    }
}

#[test]
fn the_real_campaigns_release_exclusion_is_checked_not_prose() {
    // The binding's seventh field names the mechanism keeping mutation controls out
    // of release artifacts. For the real campaign that mechanism is `test-target-only`:
    // the campaign compiles into #[test] targets, which no release artifact contains.
    // Checked, not asserted: the campaign file lives under tests/, and no production
    // source carries the campaign's own identifiers.
    let campaign_file = root().join("crates/fln-conformance/tests/mandated_mutants.rs");
    assert!(
        campaign_file.is_file(),
        "the campaign lives in a test target: {}",
        campaign_file.display()
    );
    let identifiers = ["kill_receipt_path", "KILL_RECEIPT_SCHEMA", "const PLANTS"];
    for crate_dir in [
        "crates/fln-kernel/src",
        "crates/fln-unsafe-abi/src",
        "crates/fln-conformance/src",
    ] {
        let dir = root().join(crate_dir);
        for entry in walk_rs(&dir) {
            let text = fs::read_to_string(&entry)
                .unwrap_or_else(|e| panic!("read {}: {e}", entry.display()));
            for needle in identifiers {
                assert!(
                    !text.contains(needle),
                    "mutation-control identifier `{needle}` leaked into production source {}",
                    entry.display()
                );
            }
        }
    }
}

fn walk_rs(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    if let Ok(entries) = fs::read_dir(dir) {
        let mut entries: Vec<_> = entries.flatten().collect();
        entries.sort_by_key(std::fs::DirEntry::file_name);
        for entry in entries {
            let path = entry.path();
            if path.is_dir() {
                out.extend(walk_rs(&path));
            } else if path.extension().is_some_and(|e| e == "rs") {
                out.push(path);
            }
        }
    }
    out
}

// ---------------------------------------------------------------------------
// as7's concrete module-apply mutation campaign and retained receipts
// ---------------------------------------------------------------------------

const MODULE_APPLY_RECEIPT_SCHEMA: &str = "fln.module-apply-mutant-kill-receipt/1";
const MODULE_APPLY_RECEIPT_BEAD: &str = "franken_lean-module-provenance-atomic-apply-as7";
const MODULE_APPLY_RECEIPT_CLASS: &str = "bounded_model";
const MODULE_APPLY_TREE_CLASS: &str = "committed_main_ancestor";

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum ModuleApplyMutantCategory {
    DropDeclaration,
    DropExtraDeclaration,
    DropExtensionRow,
    DropReverseRow,
    PayloadBinding,
    RootPrecondition,
    PreflightCheck,
}

impl ModuleApplyMutantCategory {
    const ALL: [Self; 7] = [
        Self::DropDeclaration,
        Self::DropExtraDeclaration,
        Self::DropExtensionRow,
        Self::DropReverseRow,
        Self::PayloadBinding,
        Self::RootPrecondition,
        Self::PreflightCheck,
    ];

    const fn token(self) -> &'static str {
        match self {
            Self::DropDeclaration => "drop_declaration",
            Self::DropExtraDeclaration => "drop_extra_declaration",
            Self::DropExtensionRow => "drop_extension_row",
            Self::DropReverseRow => "drop_reverse_row",
            Self::PayloadBinding => "payload_binding",
            Self::RootPrecondition => "root_precondition",
            Self::PreflightCheck => "preflight_check",
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct ModuleApplyKiller {
    libtest_path: &'static str,
    function: &'static str,
    file: &'static str,
    expected_failure: &'static [&'static str],
}

impl ModuleApplyKiller {
    const fn as_digest_killer(self) -> MutationKiller<'static> {
        MutationKiller {
            libtest_path: self.libtest_path,
            function: self.function,
            file: self.file,
            expected_failure: self.expected_failure,
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct ModuleApplyPlant {
    id: &'static str,
    categories: &'static [ModuleApplyMutantCategory],
    file: &'static str,
    find: &'static str,
    replace: &'static str,
    killer: ModuleApplyKiller,
}

impl ModuleApplyPlant {
    const fn site(self) -> MutationSite<'static> {
        MutationSite {
            file: self.file,
            find: self.find,
            replace: self.replace,
        }
    }
}

const MODULE_APPLY_TEST_FILE: &str = "crates/fln-env/src/module_apply.rs";
const MODULE_APPLY_PROVENANCE_FILE: &str = "crates/fln-env/src/provenance.rs";

const MODULE_APPLY_PLANTS: &[ModuleApplyPlant] = &[
    ModuleApplyPlant {
        id: "root-precondition/stale-base",
        categories: &[ModuleApplyMutantCategory::RootPrecondition],
        file: MODULE_APPLY_TEST_FILE,
        find: concat!(
            "        if self.schema != MODULE_APPLY_SCHEMA_VERSION || !self.is_valid_for(base) {\n",
            "            return Outcome::complete(Err(ModuleApplyCommitError::StaleBase));\n",
            "        }\n",
        ),
        replace: "",
        killer: ModuleApplyKiller {
            libtest_path: "module_apply::tests::concurrent_module_apply_resolves_by_stale_base_and_converges_either_way",
            function: "concurrent_module_apply_resolves_by_stale_base_and_converges_either_way",
            file: MODULE_APPLY_TEST_FILE,
            expected_failure: &[
                "expected StaleBase for the losing plan",
                "got Receipt(BaseRoot",
            ],
        },
    },
    ModuleApplyPlant {
        id: "root-precondition/receipt-verify",
        categories: &[ModuleApplyMutantCategory::RootPrecondition],
        file: MODULE_APPLY_TEST_FILE,
        find: concat!(
            "        if let Err(error) = self.receipt.verify_for(base, &self.candidate) {\n",
            "            return Outcome::complete(Err(ModuleApplyCommitError::Receipt(error)));\n",
            "        }\n",
        ),
        replace: "",
        killer: ModuleApplyKiller {
            libtest_path: "module_apply::tests::prepare_candidate_joins_every_component_only_after_target_binding",
            function: "prepare_candidate_joins_every_component_only_after_target_binding",
            file: MODULE_APPLY_TEST_FILE,
            expected_failure: &["ModuleApplyReceiptError::ResultRoot"],
        },
    },
    ModuleApplyPlant {
        id: "index/drop-declaration",
        categories: &[ModuleApplyMutantCategory::DropDeclaration],
        file: MODULE_APPLY_PROVENANCE_FILE,
        find: "                (DeclarationClass::Declaration, record.declarations()),\n",
        replace: "",
        killer: ModuleApplyKiller {
            libtest_path: "module_apply::tests::committed_state_derives_and_keeps_both_provenance_directions",
            function: "committed_state_derives_and_keeps_both_provenance_directions",
            file: MODULE_APPLY_TEST_FILE,
            expected_failure: &["forward index does not cover exactly the manifest's declarations"],
        },
    },
    ModuleApplyPlant {
        id: "index/drop-extra-declaration",
        categories: &[ModuleApplyMutantCategory::DropExtraDeclaration],
        file: MODULE_APPLY_PROVENANCE_FILE,
        find: concat!(
            "                (\n",
            "                    DeclarationClass::ExtraDeclaration,\n",
            "                    record.extra_declarations(),\n",
            "                ),\n",
        ),
        replace: "",
        killer: ModuleApplyKiller {
            libtest_path: "module_apply::tests::committed_state_derives_and_keeps_both_provenance_directions",
            function: "committed_state_derives_and_keeps_both_provenance_directions",
            file: MODULE_APPLY_TEST_FILE,
            expected_failure: &["forward index does not cover exactly the manifest's declarations"],
        },
    },
    ModuleApplyPlant {
        id: "index/drop-reverse-row",
        categories: &[ModuleApplyMutantCategory::DropReverseRow],
        file: MODULE_APPLY_PROVENANCE_FILE,
        find: "                    owners.insert(name.clone(), (module.clone(), class));\n",
        replace: "",
        killer: ModuleApplyKiller {
            libtest_path: "module_apply::tests::committed_state_derives_and_keeps_both_provenance_directions",
            function: "committed_state_derives_and_keeps_both_provenance_directions",
            file: MODULE_APPLY_TEST_FILE,
            expected_failure: &["reverse index does not cover exactly the manifest's declarations"],
        },
    },
    ModuleApplyPlant {
        id: "index/drop-extension-row",
        categories: &[ModuleApplyMutantCategory::DropExtensionRow],
        file: MODULE_APPLY_PROVENANCE_FILE,
        find: concat!(
            "                for (offset, entry) in contribution.entries().iter().enumerate() {\n",
            "                    // In range by construction",
        ),
        replace: concat!(
            "                for (offset, entry) in contribution.entries().iter().enumerate().skip(1) {\n",
            "                    // In range by construction",
        ),
        killer: ModuleApplyKiller {
            libtest_path: "module_apply::tests::committed_state_derives_and_keeps_both_provenance_directions",
            function: "committed_state_derives_and_keeps_both_provenance_directions",
            file: MODULE_APPLY_TEST_FILE,
            expected_failure: &[
                "entry-occurrence index does not cover exactly the manifest's entries",
            ],
        },
    },
    ModuleApplyPlant {
        id: "payload-binding/declarations",
        categories: &[
            ModuleApplyMutantCategory::PayloadBinding,
            ModuleApplyMutantCategory::PreflightCheck,
        ],
        file: MODULE_APPLY_TEST_FILE,
        find: concat!(
            "    verify_declaration_payloads(\n",
            "        DeclarationClass::Declaration,\n",
            "        transaction.contribution.declarations(),\n",
            "        &transaction.declarations,\n",
            "    )?;\n",
        ),
        replace: "",
        killer: ModuleApplyKiller {
            libtest_path: "module_apply::tests::declaration_order_is_a_typed_payload_binding_refusal",
            function: "declaration_order_is_a_typed_payload_binding_refusal",
            file: MODULE_APPLY_TEST_FILE,
            expected_failure: &["DeclarationClass::Declaration"],
        },
    },
    ModuleApplyPlant {
        id: "payload-binding/extra-declarations",
        categories: &[
            ModuleApplyMutantCategory::PayloadBinding,
            ModuleApplyMutantCategory::PreflightCheck,
        ],
        file: MODULE_APPLY_TEST_FILE,
        find: concat!(
            "    verify_declaration_payloads(\n",
            "        DeclarationClass::ExtraDeclaration,\n",
            "        transaction.contribution.extra_declarations(),\n",
            "        &transaction.extra_declarations,\n",
            "    )?;\n",
        ),
        replace: "",
        killer: ModuleApplyKiller {
            libtest_path: "module_apply::tests::extra_declaration_payloads_are_bound_independently_of_the_primary_class",
            function: "extra_declaration_payloads_are_bound_independently_of_the_primary_class",
            file: MODULE_APPLY_TEST_FILE,
            expected_failure: &["DeclarationClass::ExtraDeclaration"],
        },
    },
    ModuleApplyPlant {
        id: "payload-binding/extension-count",
        categories: &[
            ModuleApplyMutantCategory::PayloadBinding,
            ModuleApplyMutantCategory::PreflightCheck,
        ],
        file: MODULE_APPLY_TEST_FILE,
        find: concat!(
            "    if transaction.extension_payloads.len() != expected_payloads {\n",
            "        return Err(ModuleApplyPreflightError::ExtensionPayloadCount {\n",
            "            expected: expected_payloads,\n",
            "            actual: transaction.extension_payloads.len(),\n",
            "        });\n",
            "    }\n",
        ),
        replace: "",
        killer: ModuleApplyKiller {
            libtest_path: "module_apply::tests::an_extension_payload_shortfall_is_a_typed_count_refusal",
            function: "an_extension_payload_shortfall_is_a_typed_count_refusal",
            file: MODULE_APPLY_TEST_FILE,
            expected_failure: &["ModuleApplyPreflightError::ExtensionPayloadCount"],
        },
    },
];

fn module_apply_receipt_path(workspace: &Path) -> PathBuf {
    workspace.join("crates/fln-conformance/evidence/module_apply_mutants/kills.jsonl")
}

fn module_apply_site_digest(plant: ModuleApplyPlant) -> String {
    mutation_site_digest(plant.site())
}

fn module_apply_killer_digest(workspace: &Path, plant: ModuleApplyPlant) -> String {
    mutation_killer_recipe_digest(workspace, &[plant.killer.as_digest_killer()])
        .unwrap_or_else(|error| panic!("{}: killer recipe cannot be bound: {error}", plant.id))
}

fn json_string_array(values: impl IntoIterator<Item = &'static str>) -> String {
    values
        .into_iter()
        .map(|value| format!("\"{value}\""))
        .collect::<Vec<_>>()
        .join(",")
}

fn module_apply_receipt_row(
    plant: ModuleApplyPlant,
    head_commit: &str,
    observed_unix_s: u64,
    site_digest: &str,
    killer_digest: &str,
) -> String {
    let categories = json_string_array(plant.categories.iter().map(|category| category.token()));
    format!(
        "{{\"schema\":\"{MODULE_APPLY_RECEIPT_SCHEMA}\",\"bead\":\"{MODULE_APPLY_RECEIPT_BEAD}\",\
         \"mutant_id\":\"{}\",\"categories\":[{categories}],\"head_commit\":\"{head_commit}\",\
         \"observed_unix_s\":{observed_unix_s},\"site_file\":\"{}\",\
         \"site_digest\":\"{site_digest}\",\"killers\":[\"{}\"],\
         \"killer_digest\":\"{killer_digest}\",\"control_passed\":1,\"killed\":1,\
         \"reasons_matched\":1,\"recovery_passed\":1,\"survivors\":[],\
         \"class\":\"{MODULE_APPLY_RECEIPT_CLASS}\",\"tree_class\":\"{MODULE_APPLY_TREE_CLASS}\"}}",
        plant.id, plant.file, plant.killer.libtest_path,
    )
}

#[test]
fn module_apply_registry_covers_every_named_category_with_a_live_unique_recipe() {
    let workspace = root();
    let required: BTreeSet<_> = ModuleApplyMutantCategory::ALL.into_iter().collect();
    let mut covered: BTreeMap<ModuleApplyMutantCategory, Vec<&str>> = BTreeMap::new();
    let mut ids = BTreeSet::new();

    for plant in MODULE_APPLY_PLANTS {
        assert!(ids.insert(plant.id), "duplicate mutant id `{}`", plant.id);
        assert!(
            !plant.categories.is_empty(),
            "{} has no acceptance category",
            plant.id
        );
        for category in plant.categories {
            covered.entry(*category).or_default().push(plant.id);
        }

        let path = workspace.join(plant.file);
        let source = fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("{} is unreadable: {error}", path.display()));
        assert_eq!(
            source.matches(plant.find).count(),
            1,
            "{} does not name exactly one live production edit in {}",
            plant.id,
            plant.file
        );
        assert_ne!(
            plant.find, plant.replace,
            "{} is a no-op mutation recipe",
            plant.id
        );
        if !plant.replace.is_empty() {
            assert!(
                !source.contains(plant.replace),
                "{} replacement is already present in {}",
                plant.id,
                plant.file
            );
        }
        assert!(
            !plant.killer.expected_failure.is_empty(),
            "{} has no stated failure discriminator",
            plant.id
        );
        let _ = module_apply_killer_digest(&workspace, *plant);
    }

    assert_eq!(
        covered.keys().copied().collect::<BTreeSet<_>>(),
        required,
        "the concrete registry and the exhaustive category enum drifted: {covered:?}"
    );
    for category in ModuleApplyMutantCategory::ALL {
        assert!(
            covered
                .get(&category)
                .is_some_and(|plants| !plants.is_empty()),
            "{} has no active plant",
            category.token()
        );
    }
}

#[test]
fn module_apply_receipts_are_canonical_current_complete_and_classify_as_kills() {
    let workspace = root();
    let path = module_apply_receipt_path(&workspace);
    let text = fs::read_to_string(&path).unwrap_or_else(|error| {
        panic!(
            "the module-apply mutation receipt is absent at {}: {error}. Run the ignored \
             campaign deliberately in a clean linked worktree; a bead comment is not \
             per-commit retention evidence",
            path.display()
        )
    });
    let rows: Vec<&str> = text
        .lines()
        .filter(|line| !line.trim().is_empty())
        .collect();
    let mut by_id = BTreeMap::new();
    for row in rows {
        let id = receipt_field(row, "mutant_id")
            .unwrap_or_else(|| panic!("receipt row has no mutant_id: {row}"));
        assert!(
            by_id.insert(id.clone(), row).is_none(),
            "duplicate receipt row for `{id}`"
        );
    }

    let expected_ids: BTreeSet<&str> = MODULE_APPLY_PLANTS.iter().map(|plant| plant.id).collect();
    let actual_ids: BTreeSet<&str> = by_id.keys().map(String::as_str).collect();
    assert_eq!(
        actual_ids, expected_ids,
        "receipt rows and live mutant recipes must account for each other exactly"
    );

    let mut ledger = KillLedger::new();
    for plant in MODULE_APPLY_PLANTS {
        let row = by_id[plant.id];
        let head_commit = receipt_field(row, "head_commit").expect("row carries head_commit");
        assert!(
            head_commit.len() == 40 && head_commit.bytes().all(|byte| byte.is_ascii_hexdigit()),
            "{} carries a malformed source commit {head_commit:?}",
            plant.id
        );
        let observed = receipt_field(row, "observed_unix_s")
            .and_then(|value| value.parse::<u64>().ok())
            .filter(|value| *value > 0)
            .unwrap_or_else(|| panic!("{} carries no positive observation time", plant.id));
        let site_digest = module_apply_site_digest(*plant);
        let killer_digest = module_apply_killer_digest(&workspace, *plant);
        let expected =
            module_apply_receipt_row(*plant, &head_commit, observed, &site_digest, &killer_digest);
        assert_eq!(
            row, expected,
            "{} receipt is stale, noncanonical, incomplete, or contains an unrecognised field",
            plant.id
        );

        let binding = MutantBinding::new(
            plant.id,
            &head_commit,
            &site_digest,
            "pinned-nightly (see rust-toolchain.toml)",
            plant.file,
            &format!(
                "{} fails for every recipe-bound stated reason",
                plant.killer.libtest_path
            ),
            "test-target-only",
        )
        .expect("the concrete receipt supplies every mutation-ledger bind");
        ledger
            .register(binding, Disposition::Active)
            .expect("every module-apply mutant registers exactly once");
        ledger
            .record(plant.id, Observation::FailedForStatedReason)
            .expect("the canonical receipt is a stated-reason kill");
    }

    let summary = ledger.summary();
    assert_eq!(summary.killed, summary.active);
    assert_eq!(summary.survived, 0);
    assert_eq!(summary.not_killed, 0);
    assert!(ledger.unrun_mutants().is_empty());
}

struct PlantedModuleApplyMutant {
    path: PathBuf,
    original: String,
    restored: bool,
}

impl PlantedModuleApplyMutant {
    fn plant(path: PathBuf, original: String, find: &str, replace: &str) -> Self {
        fs::write(&path, original.replacen(find, replace, 1))
            .unwrap_or_else(|error| panic!("plant {}: {error}", path.display()));
        Self {
            path,
            original,
            restored: false,
        }
    }

    fn restore(mut self) {
        fs::write(&self.path, &self.original)
            .unwrap_or_else(|error| panic!("restore {}: {error}", self.path.display()));
        let restored = fs::read_to_string(&self.path)
            .unwrap_or_else(|error| panic!("re-read {}: {error}", self.path.display()));
        assert_eq!(
            restored,
            self.original,
            "{} was not restored byte-for-byte",
            self.path.display()
        );
        self.restored = true;
    }
}

impl Drop for PlantedModuleApplyMutant {
    fn drop(&mut self) {
        if !self.restored {
            let _ = fs::write(&self.path, &self.original);
        }
    }
}

fn command_output(mut command: Command, what: &str) -> Output {
    command
        .output()
        .unwrap_or_else(|error| panic!("{what} could not start: {error}"))
}

fn git_output(workspace: &Path, args: &[&str]) -> Output {
    let mut command = Command::new("git");
    command.args(args).current_dir(workspace);
    command_output(command, "git")
}

fn run_module_apply_killer(
    workspace: &Path,
    inner_target: &Path,
    killer: ModuleApplyKiller,
) -> Output {
    let mut command = Command::new("cargo");
    command
        .arg("test")
        .arg("--locked")
        .arg("-p")
        .arg("fln-env")
        .arg("--lib")
        .arg(killer.libtest_path)
        .arg("--")
        .arg("--exact")
        .arg("--test-threads=1")
        .current_dir(workspace)
        .env("CARGO_TARGET_DIR", inner_target);
    command_output(command, killer.libtest_path)
}

fn combined_output(output: &Output) -> String {
    let mut text = String::from_utf8_lossy(&output.stdout).into_owned();
    text.push_str(&String::from_utf8_lossy(&output.stderr));
    text
}

fn assert_killer_control(plant: ModuleApplyPlant, output: &Output, phase: &str) {
    let text = combined_output(output);
    assert!(
        output.status.success(),
        "{}: {phase} control failed before attribution was possible:\n{text}",
        plant.id
    );
    assert!(
        text.contains(&format!("test {} ... ok", plant.killer.libtest_path)),
        "{}: {phase} exited successfully without observing the exact named killer; a libtest \
         filter that matches nothing is not a control:\n{text}",
        plant.id
    );
}

/// Plant every active as7 recipe in a retained linked worktree and replace the bounded receipt.
///
/// This is intentionally ignored and additionally refuses a normal checkout: a panic must never
/// leave a shared pane with a production precondition deleted. Ordinary CI runs the retention test,
/// not this source-mutating measurement.
#[test]
#[ignore = "edits production source; run deliberately in a clean linked worktree"]
fn the_module_apply_mutants_are_killed_for_their_recipe_bound_reasons() {
    let workspace = root();
    let git_pointer = workspace.join(".git");
    assert!(
        git_pointer.is_file(),
        "this source-mutating campaign runs only in a linked worktree; {} is not a gitdir \
         pointer file, so this appears to be the shared checkout",
        git_pointer.display()
    );
    let pointer = fs::read_to_string(&git_pointer).expect("linked-worktree gitdir is readable");
    assert!(
        pointer.starts_with("gitdir: "),
        "{} is a file but not a linked-worktree gitdir pointer",
        git_pointer.display()
    );

    let mut protected: Vec<&str> = MODULE_APPLY_PLANTS
        .iter()
        .flat_map(|plant| [plant.file, plant.killer.file])
        .collect();
    protected.sort_unstable();
    protected.dedup();
    let mut status_command = Command::new("git");
    status_command
        .arg("status")
        .arg("--porcelain")
        .arg("--")
        .args(&protected)
        .current_dir(&workspace);
    let status = command_output(status_command, "git status");
    assert!(status.status.success(), "git status failed");
    let collisions = String::from_utf8_lossy(&status.stdout);
    assert!(
        collisions.trim().is_empty(),
        "the campaign would overwrite or digest in-flight work in protected files:\n{collisions}"
    );

    let head_output = git_output(&workspace, &["rev-parse", "HEAD"]);
    assert!(head_output.status.success(), "HEAD does not resolve");
    let head_commit = String::from_utf8_lossy(&head_output.stdout)
        .trim()
        .to_string();
    assert_eq!(head_commit.len(), 40, "HEAD is not a full commit id");
    let reachable = git_output(
        &workspace,
        &["merge-base", "--is-ancestor", &head_commit, "main"],
    );
    assert!(
        reachable.status.success(),
        "{head_commit} is not reachable from main; a throwaway-commit receipt is not durable evidence"
    );

    let inner_target = std::env::var("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|_| workspace.join("target"))
        .join("module-apply-mutants");
    let observed_unix_s = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("clock is after the epoch")
        .as_secs();
    let mut rows = Vec::new();

    for plant in MODULE_APPLY_PLANTS {
        let path = workspace.join(plant.file);
        let original =
            fs::read_to_string(&path).unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        assert_eq!(
            original.matches(plant.find).count(),
            1,
            "{} anchor is absent or ambiguous",
            plant.id
        );

        let control = run_module_apply_killer(&workspace, &inner_target, plant.killer);
        assert_killer_control(*plant, &control, "pre-mutation");

        let planted = PlantedModuleApplyMutant::plant(
            path.clone(),
            original.clone(),
            plant.find,
            plant.replace,
        );
        let mutated = run_module_apply_killer(&workspace, &inner_target, plant.killer);
        let mutated_text = combined_output(&mutated);
        assert!(
            !mutated.status.success(),
            "{} SURVIVED: the named killer still passed under the mutation:\n{mutated_text}",
            plant.id
        );
        assert!(
            mutated_text.contains(&format!("test {} ... FAILED", plant.killer.libtest_path)),
            "{} did not kill the exact named test; compilation or another failure is not a kill:\n{}",
            plant.id,
            mutated_text
        );
        for expected in plant.killer.expected_failure {
            assert!(
                mutated_text.contains(expected),
                "{} killed its test for an unstated reason; missing {expected:?}:\n{mutated_text}",
                plant.id
            );
        }

        planted.restore();
        let recovery = run_module_apply_killer(&workspace, &inner_target, plant.killer);
        assert_killer_control(*plant, &recovery, "post-restore recovery");

        rows.push(module_apply_receipt_row(
            *plant,
            &head_commit,
            observed_unix_s,
            &module_apply_site_digest(*plant),
            &module_apply_killer_digest(&workspace, *plant),
        ));
        println!(
            "module_apply_mutants: {} KILLED by {}",
            plant.id, plant.killer.libtest_path
        );
    }

    let output = std::env::var("FLN_MODULE_APPLY_MUTANT_RECEIPT")
        .map(PathBuf::from)
        .unwrap_or_else(|_| module_apply_receipt_path(&workspace));
    let parent = output.parent().expect("receipt has a parent directory");
    fs::create_dir_all(parent).expect("receipt directory is creatable");
    let mut text = rows.join("\n");
    text.push('\n');
    fs::write(&output, text).expect("receipt is writable");
    println!(
        "module_apply_mutants: {} recipe-bound kills recorded at {} against main-reachable \
         {head_commit}; class {MODULE_APPLY_RECEIPT_CLASS}, one host and one instant",
        rows.len(),
        output.display()
    );
}
