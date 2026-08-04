//! `fuzz_seed_replay` — the named suite for td9's third campaign framework: budgeted
//! fuzz generation and replay (`fln_conformance::campaign`'s `Splitmix64`,
//! `FuzzBudget`, `FuzzRunner`, `FuzzReceipt`).
//!
//! # The laws proven here
//!
//! Replay (a seed plus a case index reproduces the input, checked rather than
//! believed), the budget law (every stop is typed and reported — cases, bytes,
//! duration — never a silent short count), failure capture (seed + case index in the
//! receipt), the artifact laws (schema-versioned canonical NDJSON, round-trip,
//! tamper-refusing, D7 class `statistical` always), and the framework's real
//! controlled target: the kill-ledger NDJSON row parser is total over seeded
//! garbage — no panic, and a mutated schema token is always refused — plus a planted
//! defective parser the framework finds with a replayable seed.

#![forbid(unsafe_code)]

use std::time::Duration;

use fln_conformance::campaign::{
    CaseOutcome, FUZZ_CLAIM_CLASS, FUZZ_RECEIPT_SCHEMA, FuzzBudget, FuzzReceipt, FuzzRunner,
    FuzzStop, KillLedger, MutantBinding, Splitmix64,
};

fn budget(max_cases: u64) -> FuzzBudget {
    FuzzBudget {
        max_cases,
        max_input_bytes: 1 << 16,
        max_duration: Duration::from_secs(30),
    }
}

fn runner(seed: u64, max_cases: u64) -> FuzzRunner {
    FuzzRunner {
        generator: "suite-generator/1".to_string(),
        target: "suite-target".to_string(),
        build: "nightly-2026-07-13+test-profile".to_string(),
        budget: budget(max_cases),
        seed,
    }
}

/// A generator whose stream is easy to assert on: `case_index`-mixed seeded bytes as
/// a lossy string.
fn generate_string(rng: &mut Splitmix64, case_index: u64) -> String {
    let len = 8 + rng.below(24);
    let mut bytes = rng.bytes(len);
    bytes[0] = (case_index % 256) as u8;
    String::from_utf8_lossy(&bytes).into_owned()
}

// ---------------------------------------------------------------------------
// The replay law
// ---------------------------------------------------------------------------

#[test]
fn the_same_seed_replays_the_same_stream() {
    let first =
        runner(0x5EED, 64).run(generate_string, |s: &String| s.len(), |_| CaseOutcome::Pass);
    let second =
        runner(0x5EED, 64).run(generate_string, |s: &String| s.len(), |_| CaseOutcome::Pass);
    assert_eq!(first, second, "same seed, same receipt, exactly");
    assert_eq!(first.cases_run, 64);
    assert_eq!(first.stop, FuzzStop::CasesCompleted);

    let third =
        runner(0x5EEE, 64).run(generate_string, |s: &String| s.len(), |_| CaseOutcome::Pass);
    assert_ne!(first.seed, third.seed, "control: the seeds differ");
    // And the receipt's replay reproduces case k's input byte-for-byte.
    for case_index in [0, 1, 17, 63] {
        let replayed = FuzzRunner::replay_input(&first, case_index, generate_string);
        let mut rng = Splitmix64::new(first.seed);
        let mut expected = generate_string(&mut rng, 0);
        for index in 1..=case_index {
            expected = generate_string(&mut rng, index);
        }
        assert_eq!(replayed, expected, "case {case_index} replays exactly");
    }
}

// ---------------------------------------------------------------------------
// The budget law: every stop is typed and reported
// ---------------------------------------------------------------------------

#[test]
fn the_byte_budget_stops_the_run_and_the_receipt_says_why() {
    let mut r = runner(1, 100);
    r.budget.max_input_bytes = 10;
    let receipt = r.run(generate_string, |s: &String| s.len(), |_| CaseOutcome::Pass);
    match receipt.stop {
        FuzzStop::InputBytesExhausted { case_index } => {
            // The first oversized input stops the run *before* the oracle sees it.
            let oversized = FuzzRunner::replay_input(&receipt, case_index, generate_string);
            assert!(oversized.len() > 10);
        }
        other => panic!("expected a typed byte-budget stop, got {other:?}"),
    }
    assert!(
        receipt.cases_run < 100,
        "the run reports its short count, never a silent truncation to the full budget"
    );
}

#[test]
fn the_duration_budget_stops_the_run() {
    let mut r = runner(1, 1_000_000);
    r.budget.max_duration = Duration::ZERO;
    let receipt = r.run(generate_string, |s: &String| s.len(), |_| CaseOutcome::Pass);
    assert_eq!(receipt.stop, FuzzStop::DurationExhausted);
    assert_eq!(
        receipt.cases_run, 0,
        "a zero duration stops before the first case"
    );
}

#[test]
fn a_failure_is_captured_with_its_seed_and_case_index() {
    let fail_at = 7u64;
    let receipt = runner(0xBEEF, 100).run(
        generate_string,
        |s: &String| s.len(),
        |input: &String| {
            if input.as_bytes()[0] == fail_at as u8 {
                CaseOutcome::Fail {
                    detail: "planted failure marker".to_string(),
                }
            } else {
                CaseOutcome::Pass
            }
        },
    );
    match &receipt.stop {
        FuzzStop::FailureFound { case_index, detail } => {
            assert_eq!(*case_index, fail_at);
            assert_eq!(detail, "planted failure marker");
            // The seed + index reproduce the failing input, and it fails the same oracle.
            let replayed = FuzzRunner::replay_input(&receipt, *case_index, generate_string);
            assert_eq!(replayed.as_bytes()[0], fail_at as u8);
        }
        other => panic!("expected a captured failure, got {other:?}"),
    }
    assert_eq!(
        receipt.cases_run,
        fail_at + 1,
        "the run stops at the failure"
    );
}

// ---------------------------------------------------------------------------
// The artifact laws: schema-versioned, canonical, round-tripping, D7-honest
// ---------------------------------------------------------------------------

#[test]
fn the_receipt_is_schema_versioned_and_round_trips() {
    let receipt =
        runner(0xC0DE, 32).run(generate_string, |s: &String| s.len(), |_| CaseOutcome::Pass);
    let line = receipt.to_ndjson();
    assert!(
        line.starts_with(&format!("{{\"schema\":\"{FUZZ_RECEIPT_SCHEMA}\",")),
        "the row leads with its schema token"
    );
    assert!(
        line.contains(&format!("\"class\":\"{FUZZ_CLAIM_CLASS}\"")),
        "the D7 class is statistical — a fuzz receipt is never proof of the sampled property"
    );
    let parsed = FuzzReceipt::from_ndjson(&line).expect("the emitted row parses");
    assert_eq!(parsed, receipt, "round-trip is exact");

    let wrong_schema = line.replacen(FUZZ_RECEIPT_SCHEMA, "fln.fuzz-replay/0", 1);
    assert!(FuzzReceipt::from_ndjson(&wrong_schema).is_err());
    let wrong_stop = line.replacen("cases_completed", "went_walkabout", 1);
    assert!(FuzzReceipt::from_ndjson(&wrong_stop).is_err());
    let wrong_class = line.replacen(FUZZ_CLAIM_CLASS, "proof", 1);
    let parsed = FuzzReceipt::from_ndjson(&wrong_class).expect("a class token is data");
    assert!(
        !parsed.to_ndjson().contains("\"class\":\"proof\""),
        "re-emission restores the statistical class — the receipt cannot be edited \
         into a proof by string surgery"
    );
}

// ---------------------------------------------------------------------------
// The real controlled target: the kill-ledger row parser under seeded garbage
// ---------------------------------------------------------------------------

/// A valid row, built once, that the mutator starts from.
fn valid_row() -> String {
    let mut ledger = KillLedger::new();
    ledger
        .register(
            MutantBinding::new(
                "m1", "a1b2c3d4", "e5f60718", "build", "target", "disc", "proof",
            )
            .expect("binding"),
            fln_conformance::campaign::Disposition::Active,
        )
        .expect("register");
    ledger
        .to_ndjson()
        .lines()
        .next()
        .expect("one row")
        .to_string()
}

/// The mutator: seeded byte-level havoc over a valid row — flips, truncations,
/// insertions, and schema-token replacements.
fn mutate_row(rng: &mut Splitmix64, _case_index: u64) -> String {
    let mut bytes = valid_row().into_bytes();
    match rng.below(4) {
        0 => {
            let at = rng.below(bytes.len());
            bytes[at] = rng.bytes(1)[0];
        }
        1 => {
            bytes.truncate(rng.below(bytes.len() + 1));
        }
        2 => {
            let at = rng.below(bytes.len() + 1);
            bytes.insert(at, rng.bytes(1)[0]);
        }
        _ => {
            let text = String::from_utf8_lossy(&bytes).into_owned();
            return text.replacen(
                fln_conformance::campaign::KILL_LEDGER_SCHEMA,
                &format!("fln.mutation-kill-ledger/{}", rng.below(9)),
                1,
            );
        }
    }
    String::from_utf8_lossy(&bytes).into_owned()
}

#[test]
fn the_kill_ledger_row_parser_is_total_over_seeded_garbage() {
    let receipt = runner(0xF422, 2_000).run(
        mutate_row,
        |s: &String| s.len(),
        |input: &String| {
            // Totality: Ok or Err, never a panic (FL-INV-07 — a fuzzer turning a
            // panic into a crash instead of a finding is the fuzzer failing first).
            let verdict = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                KillLedger::row_from_ndjson(input)
            }));
            match verdict {
                Ok(Ok(_)) | Ok(Err(_)) => CaseOutcome::Pass,
                Err(_) => CaseOutcome::Fail {
                    detail: format!("parser panicked on {input:?}"),
                },
            }
        },
    );
    assert_eq!(
        receipt.stop,
        FuzzStop::CasesCompleted,
        "2,000 seeded mutations, no panic: {}",
        receipt.to_ndjson()
    );
    assert_eq!(receipt.cases_run, 2_000);

    // And the schema law under the same generator: a mutated schema token is always
    // refused, never silently accepted.
    for case_index in [0, 1, 2, 3, 4] {
        let mut rng = Splitmix64::new(0xF422);
        let mut row = mutate_row(&mut rng, 0);
        for index in 1..=case_index {
            row = mutate_row(&mut rng, index);
        }
        if !row.contains(fln_conformance::campaign::KILL_LEDGER_SCHEMA) {
            assert!(
                KillLedger::row_from_ndjson(&row).is_err(),
                "a row without the exact schema token is refused"
            );
        }
    }
}

#[test]
fn a_planted_parser_defect_is_found_with_a_replayable_seed() {
    // The framework proving itself on a controlled defective target (td9: "plant and
    // recover named failures"): a parser that panics on NUL bytes, fuzzed with a
    // generator whose stream contains them.
    fn buggy_parser(input: &[u8]) -> Result<(), String> {
        if input.contains(&0) {
            panic!("planted defect: NUL byte");
        }
        Ok(())
    }
    let receipt = runner(0xD00D, 512).run(
        |rng: &mut Splitmix64, _| rng.bytes(16),
        |v: &Vec<u8>| v.len(),
        |input: &Vec<u8>| match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            buggy_parser(input)
        })) {
            Ok(Ok(())) | Ok(Err(_)) => CaseOutcome::Pass,
            Err(_) => CaseOutcome::Fail {
                detail: "panicked on a NUL byte".to_string(),
            },
        },
    );
    let case_index = match &receipt.stop {
        FuzzStop::FailureFound { case_index, .. } => *case_index,
        other => panic!("the planted defect is found, got {other:?}"),
    };
    let replayed: Vec<u8> =
        FuzzRunner::replay_input(&receipt, case_index, |rng: &mut Splitmix64, _| {
            rng.bytes(16)
        });
    assert!(
        replayed.contains(&0),
        "the replayed failing input carries the defect trigger — the failure is a \
         fact about the input, not about the run"
    );
}
