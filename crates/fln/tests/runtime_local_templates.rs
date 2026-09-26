//! Local generic/staged helpers specialize at uses, after ordinary admission.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, FlbcExecutionLimits, KVMap,
    Outcome, VmExit, execute_flbc_artifact,
};

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}
fn returned(exit: &VmExit, expected: &str) -> u64 {
    let VmExit::Returned(value) = exit else {
        panic!("expected native returned value");
    };
    assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some(expected));
    value.usage.steps
}
fn execute(source: &str, expected: &str) -> u64 {
    let run = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let execution = run.executions.last().unwrap();
    let steps = returned(&execution.exit, expected);
    let replay = execute_flbc_artifact(
        &execution.flbc_artifact,
        &KVMap::new(),
        FlbcExecutionLimits::default(),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    returned(&replay, expected);
    steps
}

#[test]
fn local_generic_helpers_have_distinct_concrete_uses_and_no_runtime_type_slot() {
    execute(
        "def answer : Nat := let identity (A : Type) (x : A) : A := x; identity Nat 40 + String.length (identity String \"ab\")\n#eval answer",
        "42",
    );
    execute(
        "def answer : Nat := let identity {A : Type} (x : A) : A := x; identity 40 + String.length (identity \"ab\")\n#eval answer",
        "42",
    );
}

#[test]
fn local_type_arguments_can_follow_runtime_parameters() {
    execute(
        "def answer : Nat := let keep (ignored : Nat) (A : Type) (x : A) : A := x; keep 9 Nat 42\n#eval answer",
        "42",
    );
}

#[test]
fn type_constructor_parameters_use_the_ordinary_static_application_path() {
    execute(
        "def Id (A : Type) : Type := A\ndef answer : Nat := let pass (F : Type -> Type) (A : Type) (x : F A) : F A := x; pass Id Nat 42\n#eval answer",
        "42",
    );
}

#[test]
fn generic_local_helpers_capture_runtime_values_and_owned_strings() {
    execute(
        "def run (offset : Nat) : Nat := let add (A : Type) (ignored : A) (n : Nat) : Nat := offset + n; add String \"unused\" 36\n#eval run 6",
        "42",
    );
    execute(
        "def run (suffix : String) : Nat := let wrap (A : Type) (ignored : A) : String := suffix ++ suffix; String.length (wrap Nat 0 ++ wrap Bool true)\n#eval run \"abc\"",
        "12",
    );
}

#[test]
fn consuming_string_arguments_preserve_the_original_and_its_aliases() {
    execute(
        "def run (suffix : String) : Nat := let doubled : String := suffix ++ suffix; String.length (suffix ++ doubled)\n#eval run \"abc\"",
        "9",
    );
    execute(
        "def run (suffix : String) : Nat := let alias : String := suffix; let appended : String := suffix ++ \"d\"; String.length alias + String.length appended\n#eval run \"abc\"",
        "7",
    );
    execute(
        "#eval let suffix : String := \"abc\"; String.length ((suffix ++ suffix) ++ (suffix ++ suffix))",
        "12",
    );
}

const APPLY: &str = "def applyBoth (f : Nat -> Nat -> Nat) (a b : Nat) : Nat := f a b\n";
const SPEND: &str =
    "def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => spend k + 1\n";

#[test]
fn named_staged_helpers_and_aliases_reach_known_callback_specialization() {
    execute(
        &format!(
            "{APPLY}def run (delta : Nat) : Nat := let stage (x : Nat) : Nat -> Nat := let saved : Nat := delta + x; fun (y : Nat) => saved + y; let alias : Nat -> Nat -> Nat := stage; applyBoth alias 20 16\n#eval run 6"
        ),
        "42",
    );
    execute(
        include_str!("../../../examples/native_local_templates.lean"),
        "42",
    );
}

#[test]
fn unused_callback_results_still_run_their_required_first_stage() {
    let definitions = format!(
        "{SPEND}def ignorePartial (f : Nat -> Nat -> Nat) (n : Nat) : Nat := let unused : Nat -> Nat := f n; 42\n"
    );
    let program = |cost| {
        format!(
            "{definitions}#eval let stage (n : Nat) : Nat -> Nat := let paid : Nat := spend n; fun (y : Nat) => y; ignorePartial stage {cost}"
        )
    };
    let idle = execute(&program(0), "42");
    let busy = execute(&program(30), "42");
    assert!(
        busy > idle + 30,
        "required stage disappeared: {idle} vs {busy}"
    );
}

#[test]
fn computed_initializers_and_unused_ordinary_arguments_keep_their_strict_work() {
    let programs = [
        "def run (cost : Nat) : Nat := let helper : Nat -> Nat := let paid : Nat := spend cost; fun (x : Nat) => x; 42\n",
        "def run (cost : Nat) : Nat := let keep (ignored : Nat) (A : Type) (x : A) : A := x; keep (spend cost) Nat 42\n",
    ];
    for definitions in programs {
        let program = |cost| format!("{SPEND}{definitions}#eval run {cost}");
        let idle = execute(&program(0), "42");
        let busy = execute(&program(30), "42");
        assert!(
            busy > idle + 30,
            "initializer disappeared: {idle} vs {busy}"
        );
        let base = engine();
        let options = KVMap::new();
        let root = base.logical_root(&options);
        let mut bounded = limits();
        bounded.vm.max_steps = idle;
        assert!(matches!(
            base.execute_source_definitions(&[program(30).as_bytes()], &options, bounded)
                .unwrap(),
            Outcome::Inconclusive(_)
        ));
        assert_eq!(base.logical_root(&options), root);
    }
}

#[test]
fn invalid_local_templates_and_budget_stops_leave_a_clean_deterministic_retry() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for invalid in [
        "#eval let bad (A : Type) (x : A) : A := 7; 42",
        "#eval let keep (A : Type) (x : A) : A := x; keep Bool 7",
    ] {
        assert!(
            base.execute_source_definitions(&[invalid.as_bytes()], &options, limits())
                .is_err(),
            "{invalid}"
        );
        assert_eq!(base.logical_root(&options), root);
    }
    let source = include_str!("../../../examples/native_local_templates.lean");
    let mut tiny = limits();
    tiny.ingress.max_nodes = 1;
    assert!(
        base.execute_source_definitions(&[source.as_bytes()], &options, tiny)
            .is_err()
    );
    assert_eq!(base.logical_root(&options), root);
    let run = || {
        base.execute_source_definitions(&[source.as_bytes()], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let first = run();
    let second = run();
    assert_eq!(
        first.executions.last().unwrap().flbc_artifact,
        second.executions.last().unwrap().flbc_artifact
    );
    returned(&first.executions.last().unwrap().exit, "42");
    assert_eq!(base.logical_root(&options), root);
}
