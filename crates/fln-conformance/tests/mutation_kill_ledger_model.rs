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

use std::fs;
use std::path::{Path, PathBuf};

use fln_conformance::campaign::{
    CampaignError, Disposition, KILL_LEDGER_SCHEMA, KillLedger, KillVerdict, MutantBinding,
    NotAKill, Observation,
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
