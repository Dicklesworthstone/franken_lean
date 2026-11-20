//! Production FL-INV-01 determinism tests for `fln::parallel_elab` backed by
//! `fln_elab::DeterministicScheduler`.
#![forbid(unsafe_code)]

use fln::parallel_elab::check_source_definitions_parallel;
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome};

fn seeded_engine() -> Engine {
    let kernel = Budget::for_stack_bytes(2 * 1024 * 1024);
    match Engine::with_source_seed(EngineAdmissionLimits::new(kernel)).expect("seed") {
        Outcome::Complete(engine) => engine,
        other => panic!("expected Complete seed, got {other:?}"),
    }
}

#[test]
fn parallel_source_elab_is_bit_identical_across_1_4_8_threads() {
    let engine = seeded_engine();
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let options = KVMap::new();
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
    let r4 = match check_source_definitions_parallel(&engine, &sources, &options, 4, limits)
        .expect("4 threads")
    {
        Outcome::Complete(r) => r,
        other => panic!("expected Complete at 4 threads, got {other:?}"),
    };
    let r8 = match check_source_definitions_parallel(&engine, &sources, &options, 8, limits)
        .expect("8 threads")
    {
        Outcome::Complete(r) => r,
        other => panic!("expected Complete at 8 threads, got {other:?}"),
    };

    assert_eq!(r1.base_logical_root, r4.base_logical_root);
    assert_eq!(r1.base_logical_root, r8.base_logical_root);
    assert_eq!(r1.result_logical_root, r4.result_logical_root);
    assert_eq!(r1.result_logical_root, r8.result_logical_root);
    assert_eq!(r1.committed_order, r4.committed_order);
    assert_eq!(r1.committed_order, r8.committed_order);
    assert_eq!(r1.committed_order.len(), 10);

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
    let result = check_source_definitions_parallel(&engine, &sources, &options, 4, limits);
    assert!(result.is_err(), "ill-typed batch must fail, got {result:?}");
    assert!(
        !engine
            .environment()
            .contains(&Name::from_components(["good1"]))
    );
}
