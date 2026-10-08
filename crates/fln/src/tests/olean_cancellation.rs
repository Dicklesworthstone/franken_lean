//! Cancellation of real serial module councils must expose no admitted prefix.

use super::*;
use crate::{CancellationProbe, CheckedOleanSet, Inconclusive};
use std::cell::Cell;

struct CancelAt {
    sample: usize,
    calls: Cell<usize>,
}

impl CancelAt {
    fn new(sample: usize) -> Self {
        Self {
            sample,
            calls: Cell::new(0),
        }
    }
}

impl CancellationProbe for CancelAt {
    fn is_cancelled(&self) -> bool {
        let call = self.calls.get() + 1;
        self.calls.set(call);
        call >= self.sample
    }
}

fn chain(reject_child: bool) -> Vec<(Name, Vec<u8>)> {
    let mut constants = standalone_declarations();
    if reject_child {
        let ConstantInfo::Thm(theorem) = &mut constants[0] else {
            unreachable!("the real checking fixture starts with its theorem")
        };
        theorem.value = Expr::sort(Level::zero());
    }
    vec![
        (
            fixture_name("Cancellation.Base"),
            standalone_olean(&constants[1..]),
        ),
        (
            fixture_name("Cancellation.Child"),
            olean_with_imports(&constants[..1], &fixture_imports(&["Cancellation.Base"])),
        ),
    ]
}

fn limits(set: &[(Name, Vec<u8>)]) -> OleanCheckLimits {
    OleanCheckLimits::new(
        set.iter().map(|(_, bytes)| bytes.len()).sum(),
        test_budget(),
    )
}

fn assert_cancelled(answer: &Result<Outcome<CheckedOleanSet>, OleanCheckError>, checkpoint: &str) {
    assert!(
        matches!(answer, Ok(Outcome::Inconclusive(reason))
            if *reason == Inconclusive::cancelled(checkpoint)),
        "{answer:?}"
    );
}

#[test]
fn serial_import_cancellation_precedes_artifact_decoding() {
    let engine = Engine::from_environment(Environment::new());
    let original = engine.clone();
    let set = vec![(fixture_name("Cancellation.Malformed"), vec![0_u8; 8])];
    let inputs = fixture_inputs(&set);
    let options = KVMap::new();
    assert!(matches!(
        engine.check_olean_modules(&inputs, &options, limits(&set)),
        Err(OleanCheckError::ModuleDecode { .. })
    ));

    let probe = CancelAt::new(1);
    let answer = engine.check_olean_modules_scheduled(
        &inputs,
        &options,
        limits(&set),
        fixture_jobs(1),
        Some(&probe),
    );
    assert_cancelled(&answer, "olean-modules/before-decode");
    assert_eq!(probe.calls.get(), 1);
    crate::assert_engines_identical(&original, &engine, "cancel before decoding");
}

#[test]
fn serial_import_cancellation_stops_before_the_next_council() {
    let set = chain(true);
    let inputs = fixture_inputs(&set);
    let options = KVMap::new();
    for (engine, threads) in [
        (Engine::from_environment(Environment::new()), 1),
        (seeded_engine(), 3),
    ] {
        let original = engine.clone();
        let root = engine.logical_root(&options);
        // The first module really admits both declarations through the council;
        // the second really rejects when cancellation does not stop its check.
        let prefix = engine
            .check_olean_modules(&fixture_inputs(&set[..1]), &options, limits(&set))
            .unwrap()
            .into_complete()
            .unwrap();
        assert!(
            prefix
                .engine
                .environment()
                .contains(&fixture_name("Fixture.P"))
        );
        assert!(
            prefix
                .engine
                .environment()
                .contains(&fixture_name("Fixture.p"))
        );
        assert_eq!(prefix.modules[0].declarations.len(), 2);
        match engine.check_olean_modules(&inputs, &options, limits(&set)) {
            Err(OleanCheckError::Admission(EngineAdmissionError::BatchDeclaration {
                error,
                ..
            })) => assert!(matches!(
                *error,
                EngineAdmissionError::KernelRejected { .. }
            )),
            answer => panic!("the uncancelled child must reach its bad proof: {answer:?}"),
        }

        // Polls: before decoding, before the valid base, before the bad child.
        // Three requested workers still use this path on the nonempty base.
        let probe = CancelAt::new(3);
        let answer = engine.check_olean_modules_scheduled(
            &inputs,
            &options,
            limits(&set),
            fixture_jobs(threads),
            Some(&probe),
        );
        assert_cancelled(&answer, "olean-modules/before-module");
        assert_eq!(probe.calls.get(), 3);
        assert_eq!(engine.logical_root(&options), root);
        assert!(!engine.environment().contains(&fixture_name("Fixture.P")));
        assert!(!engine.imported_modules().contains(&set[0].0));
        crate::assert_engines_identical(&original, &engine, "cancel between module councils");
    }
}

#[test]
fn serial_import_cancellation_before_publication_returns_no_successor() {
    let set = chain(false);
    let inputs = fixture_inputs(&set);
    let options = KVMap::new();
    for (engine, threads) in [
        (Engine::from_environment(Environment::new()), 1),
        (seeded_engine(), 3),
    ] {
        let original = engine.clone();
        let root = engine.logical_root(&options);
        let probe = CancelAt::new(4);
        let answer = engine.check_olean_modules_scheduled(
            &inputs,
            &options,
            limits(&set),
            fixture_jobs(threads),
            Some(&probe),
        );
        assert_cancelled(&answer, "olean-modules/before-publication");
        assert_eq!(probe.calls.get(), 4);
        assert_eq!(engine.logical_root(&options), root);
        assert!(!engine.environment().contains(&fixture_name("Fixture.t")));
        assert!(!engine.imported_modules().contains(&set[1].0));
        crate::assert_engines_identical(&original, &engine, "cancel before set publication");

        let recovered = engine
            .check_olean_modules(&inputs, &options, limits(&set))
            .unwrap()
            .into_complete()
            .unwrap();
        assert!(
            recovered
                .engine
                .environment()
                .contains(&fixture_name("Fixture.t"))
        );
        assert_eq!(recovered.modules.len(), 2);
        assert_eq!(
            recovered.modules[1].declarations[0].checker.ground,
            CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        assert_eq!(engine.logical_root(&options), root);
    }
}

#[test]
fn uncancelled_serial_fallbacks_preserve_the_complete_admission_result() {
    let set = chain(false);
    let inputs = fixture_inputs(&set);
    let options = KVMap::new();
    for (engine, threads) in [
        (Engine::from_environment(Environment::new()), 1),
        (seeded_engine(), 3),
    ] {
        let original = engine.clone();
        let expected = engine.check_olean_modules(&inputs, &options, limits(&set));
        assert!(
            matches!(&expected, Ok(Outcome::Complete(_))),
            "{expected:?}"
        );
        let probe = CancelAt::new(usize::MAX);
        let observed = engine.check_olean_modules_scheduled(
            &inputs,
            &options,
            limits(&set),
            fixture_jobs(threads),
            Some(&probe),
        );
        assert_eq!(probe.calls.get(), set.len() + 2);
        assert_same_set_answer(&expected, &observed, "uncancelled serial fallback");
        let without_probe = engine.check_olean_modules_scheduled(
            &inputs,
            &options,
            limits(&set),
            fixture_jobs(threads),
            None,
        );
        assert_same_set_answer(&expected, &without_probe, "serial fallback without a probe");
        crate::assert_engines_identical(&original, &engine, "completed serial fallback receiver");
    }
}
