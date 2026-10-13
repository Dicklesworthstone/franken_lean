//! Source-inferred inductive universes must pass both native checkers.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn check(source: &str) {
    let engine = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    engine
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .expect("source and both judges complete");
}

#[test]
fn inferred_polymorphic_sum_eliminates_and_retains_independent_carrier_universes() {
    check(include_str!(
        "../../fln-parse/tests/fixtures/polymorphic_sum.lean"
    ));
}

#[test]
fn inferred_polymorphic_product_and_exception_families_keep_their_fields() {
    check(
        "structure Prod (α : Type u) (β : Type v) where\n  fst : α\n  snd : β\n\
           def pair : Prod Nat Bool := Prod.mk 4 true\n\
           theorem first : pair.fst = 4 := by rfl\n\
           theorem second : pair.snd = true := by rfl",
    );
    check(
        "inductive Except (ε : Type u) (α : Type v) where | error (value : ε) | ok (value : α)\n\
           def result (e : Except Bool Nat) : Nat := match e with | Except.error b => if b then 1 else 2 | Except.ok n => n\n\
           theorem success : result (Except.ok 4) = 4 := by rfl\n\
           theorem failure : result (Except.error true) = 1 := by rfl",
    );
}

#[test]
fn explicit_reordered_maxima_and_redundant_result_bounds_are_convertible() {
    for level in ["max v u", "max 0 (max u v)", "max (max u v) u"] {
        check(&format!(
            "inductive Sum (α : Type u) (β : Type v) : Type ({level}) where | inl (a : α) | inr (b : β)\n\
          def take (x : Sum Nat Bool) : Nat := match x with | Sum.inl n => n | Sum.inr b => if b then 1 else 0\n\
          theorem value : take (Sum.inl 4) = 4 := by rfl"
        ));
    }
}

#[test]
fn reconstructed_coproducts_execute_through_the_native_vm() {
    use fln::{EngineExecutionLimits, VmExit};
    let seed = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let engine = seed
        .check_source_files(
            &[include_bytes!(
                "../../fln-parse/tests/fixtures/polymorphic_sum.lean"
            )],
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let source = "#eval observe (Sum.inl 4)\n#eval observe (Sum.inr false)\n#eval observe (mapSum (fun n => n + 2) (fun b => b) (Sum.inl 4))";
    let run = engine
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(run.executions.len(), 3);
    for (execution, expected) in run.executions.iter().zip(["5", "3", "7"]) {
        let VmExit::Returned(value) = &execution.exit else {
            panic!("{:?}", execution.exit)
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}

#[test]
fn universe_equality_cannot_hide_wrong_carriers_false_proofs_or_small_results() {
    let seed = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let engine = seed
        .check_source_files(
            &[include_bytes!(
                "../../fln-parse/tests/fixtures/polymorphic_sum.lean"
            )],
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let options = KVMap::new();
    let before = engine.logical_root(&options);
    for source in [
        "def bad : Sum Nat Bool := Sum.inl true",
        "def bad : Sum Nat Bool := Sum.inr 1",
        "theorem bad : observe (Sum.inl 4) = 6 := by rfl",
        "def bad : Sum Nat Bool := higherLeft Nat",
        "inductive TooSmall (α : Type (u+1)) : Type u where | mk (a : α)",
    ] {
        let result = engine.check_source_files(&[source.as_bytes()], &options, limits());
        assert!(result.is_err(), "invalid source admitted: {source}");
        assert_eq!(engine.logical_root(&options), before);
    }
    engine
        .check_source_files(
            &[b"theorem recovered : observe (Sum.inr false) = 3 := by rfl"],
            &options,
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap();
}
