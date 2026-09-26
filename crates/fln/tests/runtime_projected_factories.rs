//! Projected instance dictionaries remain ordinary checked source programs.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, VmExit};

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}
fn execute(source: &str, expected: &str) -> u64 {
    let run = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &run.executions.last().unwrap().exit else {
        panic!("execution did not return");
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected)
    );
    value.usage.steps
}

const EXAMPLE: &str = include_str!("../../../examples/native_instance_factories.lean");

#[test]
fn packaged_polymorphic_dictionaries_pass_both_checkers_and_execute() {
    execute(EXAMPLE, "42");
    execute(
        &format!("{EXAMPLE}\nstructure Outer (K : Type) where\n  bundle : DictionaryBundle K\ndef makeOuter (K : Type) : Outer K := {{ bundle := makeBundle K }}\n#eval invokeEcho (K := Nat) (chosen := (makeOuter Nat).bundle.dictionary) 42"),
        "42",
    );
}

#[test]
fn explicit_class_parent_fields_and_projected_factory_callbacks_execute() {
    execute(
        r#"
class Echo (K : Type) where
  echo : {A : Type} -> A -> A
class Composite (K : Type) where
  parent : Echo K
  marker : Nat
def makeComposite (K : Type) : Composite K :=
  { parent := { echo := fun a => a }, marker := 0 }
def useEcho {K : Type} [chosen : Echo K] (n : Nat) : Nat := Echo.echo (K := K) n
#eval useEcho (K := Nat) (chosen := (makeComposite Nat).parent) 42
"#,
        "42",
    );
    execute(
        r#"
class Echo (K : Type) where
  echo : {A : Type} -> A -> A
structure Factory (K : Type) where
  build : Nat -> Echo K
def makeFactory (K : Type) : Factory K :=
  { build := fun n => { echo := fun a => a } }
def useEcho {K : Type} [chosen : Echo K] (n : Nat) : Nat := Echo.echo (K := K) n
#eval useEcho (K := Nat) (chosen := (makeFactory Nat).build 7) 42
"#,
        "42",
    );
}

#[test]
fn a_projected_runtime_dictionary_keeps_its_unselected_sibling_computation() {
    let source = |cost| {
        format!(
            r#"
class Probe (A : Type) where
  call : A -> A
structure Envelope (K : Type) where
  chosen : Probe Nat
  unused : Nat
def count (n : Nat) : Nat := match n with | .zero => 0 | .succ k => count k + 1
def makeEnvelope (K : Type) (n : Nat) : Envelope K :=
  {{ chosen := {{ call := fun x => x }}, unused := count n }}
def useProbe [chosen : Probe Nat] (n : Nat) : Nat := Probe.call n
#eval useProbe (chosen := (makeEnvelope Nat {cost}).chosen) 42
"#
        )
    };
    let idle = execute(&source(0), "42");
    let busy = execute(&source(30), "42");
    assert!(
        busy > idle + 30,
        "unselected initializer vanished: {idle} vs {busy}"
    );
}

#[test]
fn failed_projected_calls_do_not_advance_the_caller_or_change_retries() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let invalid = format!("{EXAMPLE}\n#eval invokeEcho (K := Nat) (chosen := true) 42");
    assert!(
        base.execute_source_definitions(&[invalid.as_bytes()], &options, limits())
            .is_err()
    );
    assert_eq!(base.logical_root(&options), root);
    let run = || {
        base.execute_source_definitions(&[EXAMPLE.as_bytes()], &options, limits())
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
    assert_eq!(first.result_logical_root, second.result_logical_root);
    assert_eq!(base.logical_root(&options), root);
}
