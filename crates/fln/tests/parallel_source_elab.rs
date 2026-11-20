//! Production FL-INV-01 determinism tests for `fln::parallel_elab` backed by
//! `fln_elab::DeterministicScheduler`.
#![forbid(unsafe_code)]

use fln::parallel_elab::{ParallelSourceStrategy, check_source_definitions_parallel};
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome};

fn seeded_engine() -> Engine {
    let kernel = Budget::for_stack_bytes(2 * 1024 * 1024);
    match Engine::with_source_seed(EngineAdmissionLimits::new(kernel)).expect("seed") {
        Outcome::Complete(engine) => engine,
        other => panic!("expected Complete seed, got {other:?}"),
    }
}

#[test]
fn parallel_source_elab_is_bit_identical_across_1_8_32_threads_and_ordinary_admission() {
    let engine = seeded_engine();
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let mut options = KVMap::new();
    options.insert(
        Name::from_components(["backward", "eqns", "nonrecursive"]),
        fln_core::options::DataValue::OfBool(false),
    );
    let sources: [&[u8]; 10] = [
        b"def a1 : Nat := 2 + 3",
        b"def a2 : Nat := 4 * 5",
        b"def a3 : Nat := 10 - 3",
        b"def a4 : String := \"hello\" ++ \" world\"",
        b"def a5 : Bool := true",
        b"def b1 : Nat := a1 + a2",
        b"def b2 : Nat := a2 * a3",
        b"def b3 : Bool := b1 == 25",
        b"def c1 : Nat := b1 + b2",
        b"def c2 : Nat := c1 + a3",
    ];

    let r1 = match check_source_definitions_parallel(&engine, &sources, &options, 1, limits)
        .expect("1 thread")
    {
        Outcome::Complete(r) => r,
        other => panic!("expected Complete at 1 thread, got {other:?}"),
    };
    let r32 = match check_source_definitions_parallel(&engine, &sources, &options, 32, limits)
        .expect("32 threads")
    {
        Outcome::Complete(r) => r,
        other => panic!("expected Complete at 32 threads, got {other:?}"),
    };
    let r8 = match check_source_definitions_parallel(&engine, &sources, &options, 8, limits)
        .expect("8 threads")
    {
        Outcome::Complete(r) => r,
        other => panic!("expected Complete at 8 threads, got {other:?}"),
    };

    assert_eq!(r1.base_logical_root, r32.base_logical_root);
    assert_eq!(r1.base_logical_root, r8.base_logical_root);
    assert_eq!(r1.result_logical_root, r32.result_logical_root);
    assert_eq!(r1.result_logical_root, r8.result_logical_root);
    assert_eq!(r1.committed_order, r32.committed_order);
    assert_eq!(r1.committed_order, r8.committed_order);
    assert_eq!(r1.committed_order.len(), 10);
    for result in [&r1, &r8, &r32] {
        assert_eq!(result.strategy, ParallelSourceStrategy::Dataflow);
    }
    let mut ordinary = engine.clone();
    for source in sources {
        ordinary = ordinary
            .admit_source_declaration(source, &options, limits)
            .expect("ordinary source admission")
            .into_complete()
            .expect("ordinary source admission completes")
            .engine;
    }
    assert_eq!(r1.result_logical_root, ordinary.logical_root(&options));
    assert!(
        r1.engine
            .environment()
            .extension(&fln_elab::source::scope::simp::equations::journal_name())
            .is_some()
    );

    for name in ["a1", "a2", "a3", "a4", "a5", "b1", "b2", "b3", "c1", "c2"] {
        let key = Name::from_components([name]);
        assert!(r8.engine.environment().contains(&key), "missing {name}");
        assert_eq!(
            r1.engine.environment().find(&key),
            r8.engine.environment().find(&key)
        );
    }
}

#[test]
fn parallel_source_elab_rejects_ill_typed_definition_atomically() {
    let engine = seeded_engine();
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let options = KVMap::new();
    let sources: [&[u8]; 3] = [
        b"def good1 : Nat := 1 + 2",
        b"def bad : Nat := \"not a nat\"",
        b"def good2 : Nat := good1 + 3",
    ];
    let before = engine.logical_root(&options);
    for threads in [1, 8, 32] {
        let result =
            check_source_definitions_parallel(&engine, &sources, &options, threads, limits);
        assert!(result.is_err(), "ill-typed batch must fail, got {result:?}");
        assert_eq!(engine.logical_root(&options), before);
    }
    assert!(
        !engine
            .environment()
            .contains(&Name::from_components(["good1"]))
    );
}

#[test]
fn exhausted_elaboration_is_a_nonanswer_at_every_worker_width_and_can_recover() {
    let engine = seeded_engine();
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let sources: [&[u8]; 2] = [
        b"def first : Nat := 0",
        b"def needsConversion : Nat := first + 2",
    ];
    for steps in [0, 1] {
        let mut kernel = Budget::for_stack_bytes(2 * 1024 * 1024);
        kernel.steps = steps;
        for threads in [1, 8, 32] {
            let stopped = check_source_definitions_parallel(
                &engine,
                &sources,
                &options,
                threads,
                EngineAdmissionLimits::new(kernel),
            )
            .expect("a resource stop is not a semantic error");
            assert!(matches!(stopped, Outcome::Inconclusive(_)), "{stopped:?}");
            assert_eq!(engine.logical_root(&options), before);
            assert!(
                !engine
                    .environment()
                    .contains(&Name::from_components(["first"]))
            );
        }
    }
    let recovered = check_source_definitions_parallel(
        &engine,
        &sources,
        &options,
        8,
        EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
    )
    .unwrap()
    .into_complete()
    .expect("adequate budget completes the same source");
    assert_eq!(recovered.strategy, ParallelSourceStrategy::Dataflow);
    assert!(
        recovered
            .engine
            .environment()
            .contains(&Name::from_components(["needsConversion"]))
    );
}

#[test]
fn source_effects_and_helpers_match_ordinary_admission_across_worker_widths() {
    let engine = seeded_engine();
    let options = KVMap::new();
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let sources: [&[u8]; 5] = [
        b"abbrev two : Nat := 2",
        b"@[irreducible] def hidden : Nat := two",
        b"def helperOwner : Nat := helper + 1\nwhere helper : Nat := 5",
        b"def down : Nat -> Nat | 0 => 0 | n + 1 => down n",
        b"theorem usesAbbrev : two + 3 = 5 := by simp only []",
    ];
    let before = engine.logical_root(&options);
    let mut ordinary = engine.clone();
    for source in sources {
        ordinary = ordinary
            .admit_source_declaration(source, &options, limits)
            .unwrap_or_else(|error| panic!("{}: {error:?}", String::from_utf8_lossy(source)))
            .into_complete()
            .expect("ordinary admission completes")
            .engine;
    }
    for threads in [1, 8, 32] {
        let result =
            check_source_definitions_parallel(&engine, &sources, &options, threads, limits)
                .unwrap()
                .into_complete()
                .expect("source effects complete");
        assert_eq!(result.strategy, ParallelSourceStrategy::SourceOrder);
        assert_eq!(result.result_logical_root, ordinary.logical_root(&options));
        assert_eq!(result.committed_order.len(), sources.len());
        assert_eq!(result.retry_count, 0);
        let environment = result.engine.environment();
        assert_eq!(
            fln_elab::reducibility::known_status(environment, &Name::from_components(["two"]))
                .unwrap(),
            Some(fln_elab::reducibility::Reducibility::Reducible)
        );
        assert_eq!(
            fln_elab::reducibility::known_status(environment, &Name::from_components(["hidden"]))
                .unwrap(),
            Some(fln_elab::reducibility::Reducibility::Irreducible)
        );
        assert!(environment.contains(&Name::from_components(["helperOwner", "helper"])));
        assert!(
            fln_elab::source::equation_theorems::journal::read(environment)
                .unwrap()
                .iter()
                .any(|record| record.declaration == Name::from_components(["down"]))
        );
        assert_eq!(engine.logical_root(&options), before);
    }
}

#[test]
fn source_effect_failure_does_not_publish_earlier_declarations_or_journals() {
    let engine = seeded_engine();
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let sources: [&[u8]; 2] = [b"abbrev two : Nat := 2", b"def bad : Nat := \"wrong\""];
    for threads in [1, 8, 32] {
        assert!(
            check_source_definitions_parallel(&engine, &sources, &options, threads, limits)
                .is_err()
        );
        assert_eq!(engine.logical_root(&options), before);
        assert!(
            !engine
                .environment()
                .contains(&Name::from_components(["two"]))
        );
        assert_eq!(
            fln_elab::reducibility::known_status(
                engine.environment(),
                &Name::from_components(["two"])
            )
            .unwrap(),
            None
        );
    }
}
