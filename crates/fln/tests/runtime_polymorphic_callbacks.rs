//! Literal polymorphic callbacks specialize at their admitted consumer's uses.
//! Generic values have no invented flat runtime ABI; ordinary operands stay strict.
#![forbid(unsafe_code)]

use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionError, EngineExecutionLimits,
    FlbcExecutionLimits, IngressError, KVMap, Name, Outcome, SourceCheckLimits, VmExit,
    execute_flbc_artifact,
};
use fln_comp::ingress::IngressResource;

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
        panic!("expected a native returned value");
    };
    assert_eq!(fln::nat_decimal(&value.value).as_deref(), Some(expected));
    value.usage.steps
}

fn execute(source: &str, expected: &str) -> u64 {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let report = base
        .execute_source_commands_with_checks(source.as_bytes(), &options, limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let execution = report.batch.executions.last().unwrap();
    let steps = returned(&execution.exit, expected);
    let replay = execute_flbc_artifact(
        &execution.flbc_artifact,
        &options,
        FlbcExecutionLimits::default(),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    assert_eq!(returned(&replay, expected), steps);
    assert_eq!(base.logical_root(&options), root);
    steps
}

fn unwrap_command(mut error: EngineExecutionError) -> EngineExecutionError {
    while let EngineExecutionError::BatchCommand { error: inner, .. } = error {
        error = *inner;
    }
    error
}

const IDENTITY_CONSUMER: &str = "def usePoly (id : (A : Type) -> A -> A) : Nat := id Nat 42\n";
const SPEND: &str =
    "def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => spend k + 1\n";

#[test]
fn literal_generic_identity_reaches_native_execution_and_canonical_replay() {
    execute(
        &format!("{IDENTITY_CONSUMER}#eval usePoly (fun A x => x)"),
        "42",
    );
    execute(
        r#"
def atTwoTypes (id : (A : Type) -> A -> A) : Nat :=
  id Nat 36 + String.length (id String "answer")
#eval atTwoTypes (fun A x => x)
"#,
        "42",
    );
}

#[test]
fn canonical_consumers_keep_interleaved_static_parameters_and_runtime_captures() {
    execute(
        r#"
def useCanonical (first : Nat) (A : Type) (ignored : A)
    (id : (B : Type) -> B -> B) (last : Nat) : Nat :=
  id Nat (first - last)
#eval useCanonical 62 String "kept" (fun B x => x) 20
"#,
        "42",
    );
    execute(
        r#"
def useCaptured (first : Nat) (f : (A : Type) -> A -> Nat) (last : Nat) : Nat :=
  first - f String "kept" + last
def answer (captured : Nat) : Nat :=
  useCaptured 50 (fun A x => captured) 8
#eval answer 16
"#,
        "42",
    );
}

#[test]
fn generic_literal_partial_consumers_return_a_concrete_closure() {
    execute(
        r#"
def useSuffix (id : (A : Type) -> A -> A) (first last : Nat) : Nat :=
  id Nat (first + last)
#eval let saved : Nat -> Nat := useSuffix (fun A x => x) 20; saved 22
"#,
        "42",
    );
}

#[test]
fn ordinary_flat_and_genuinely_staged_callbacks_keep_their_existing_behavior() {
    execute(
        "def apply (f : Nat -> Nat) (n : Nat) : Nat := f n\n#eval apply (fun n => n + 1) 41",
        "42",
    );
    execute(
        "def both (f : Nat -> Nat -> Nat) (a b : Nat) : Nat := f a b\n#eval both (fun x => let paid := x + 1; fun y => paid + y) 20 21",
        "42",
    );
}

#[test]
fn nonliteral_operands_are_strict_and_shared_across_generic_callback_uses() {
    let once =
        format!("{SPEND}def use (ignored : Nat) (id : (A : Type) -> A -> A) : Nat := id Nat 42\n");
    let twice = format!(
        "{SPEND}def use (ignored : Nat) (id : (A : Type) -> A -> A) : Nat := id Nat 20 + id Nat 22\n"
    );
    let program =
        |definitions: &str, cost| format!("{definitions}#eval use (spend {cost}) (fun A x => x)");
    let idle = execute(&program(&once, 0), "42");
    let busy = execute(&program(&once, 30), "42");
    let once_cost = busy - idle;
    assert!(once_cost > 30, "an unused ordinary operand was dropped");
    let twice_cost = execute(&program(&twice, 30), "42") - execute(&program(&twice, 0), "42");
    assert_eq!(
        twice_cost, once_cost,
        "ordinary operand evaluation was duplicated"
    );

    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let mut bounded = limits();
    bounded.vm.max_steps = idle;
    assert!(matches!(
        base.execute_source_commands_with_checks(program(&once, 30).as_bytes(), &options, bounded)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn a_generic_consumer_cannot_bypass_its_selected_foreign_extern() {
    let options = KVMap::new();
    let clean = engine()
        .check_source_files(
            &[IDENTITY_CONSUMER.as_bytes()],
            &options,
            SourceCheckLimits::new(limits().admission()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let decorated = Engine::from_environment(
        fln_elab::externs::register(
            clean.environment(),
            &Name::from_components(["usePoly"]),
            vec![fln_elab::externs::ExternEntry::Standard {
                backend: Name::from_components(["all"]),
                symbol: "foreign_generic_consumer".to_owned(),
            }],
        )
        .unwrap(),
    );
    let malformed = Engine::from_environment(
        decorated
            .environment()
            .push_extension_entry(&fln_elab::externs::journal_name(), vec![0])
            .unwrap(),
    );
    let query = b"#eval usePoly (fun A x => x)";
    let ordinary = clean
        .execute_source_definitions(&[query], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    returned(&ordinary.executions.last().unwrap().exit, "42");
    for (subject, invalid_journal) in [(&decorated, false), (&malformed, true)] {
        let root = subject.logical_root(&options);
        let error = unwrap_command(
            subject
                .execute_source_definitions(&[query], &options, limits())
                .unwrap_err(),
        );
        assert!(
            matches!(
                (&error, invalid_journal),
                (
                    EngineExecutionError::Ingress(IngressError::UnsupportedNode {
                        kind: "native extern attribute does not match the supported ABI",
                    }),
                    false,
                ) | (
                    EngineExecutionError::Frontend(fln::DefinitionFrontendError::Elaborate(
                        fln_elab::NatDefinitionElabError::Inference(
                            fln_elab::source::SourceInferenceError::ExternJournal(
                                fln_elab::externs::ExternError::Malformed,
                            ),
                        ),
                    )),
                    true,
                )
            ),
            "the consumer's selected extern was bypassed: {error:?}"
        );
        assert_eq!(subject.logical_root(&options), root);
    }
}

#[test]
fn a_computed_generic_callback_is_not_relabelled_as_a_flat_runtime_closure() {
    let definitions = format!(
        "{IDENTITY_CONSUMER}def choosePoly (flag : Bool) : (A : Type) -> A -> A := if flag then (fun A x => x) else (fun A x => x)\n"
    );
    let options = KVMap::new();
    let base = engine()
        .check_source_files(
            &[definitions.as_bytes()],
            &options,
            SourceCheckLimits::new(limits().admission()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let root = base.logical_root(&options);
    let error = unwrap_command(
        base.execute_source_definitions(&[b"#eval usePoly (choosePoly true)"], &options, limits())
            .unwrap_err(),
    );
    assert!(
        matches!(
            &error,
            EngineExecutionError::Ingress(IngressError::UnknownConstant { name, .. })
                if name == &Name::from_components(["usePoly"])
        ),
        "an unsupported dynamic generic value must refuse without rewrite exhaustion: {error:?}"
    );
    assert_eq!(base.logical_root(&options), root);
}

#[test]
fn invalid_generic_values_and_budget_stops_leave_clean_deterministic_retries() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let invalid = format!("{IDENTITY_CONSUMER}def invalid : Nat := usePoly (fun A x => true)");
    assert!(
        base.check_source_files(
            &[invalid.as_bytes()],
            &options,
            SourceCheckLimits::new(limits().admission()),
        )
        .is_err()
    );
    let source = format!("{IDENTITY_CONSUMER}#eval usePoly (fun A x => x)");
    let mut bounded = limits();
    bounded.ingress.max_nodes = 1;
    let error = unwrap_command(
        base.execute_source_commands_with_checks(source.as_bytes(), &options, bounded)
            .unwrap_err(),
    );
    assert!(
        matches!(
            error,
            EngineExecutionError::Ingress(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                limit: 1,
                observed: 2,
            })
        ),
        "{error:?}"
    );
    let run = || {
        base.execute_source_commands_with_checks(source.as_bytes(), &options, limits())
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let first = run();
    let second = run();
    let first = first.batch.executions.last().unwrap();
    let second = second.batch.executions.last().unwrap();
    returned(&first.exit, "42");
    assert_eq!(first.flbc_artifact, second.flbc_artifact);
    assert_eq!(base.logical_root(&options), root);
}
