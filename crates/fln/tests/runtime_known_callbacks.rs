//! Known higher-order bodies execute through admission, native FIR and FLBC.
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
fn expect(exit: &VmExit, expected: &str) -> u64 {
    let VmExit::Returned(value) = exit else {
        panic!("expected a returned value");
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
    let steps = expect(&execution.exit, expected);
    let replay = execute_flbc_artifact(
        &execution.flbc_artifact,
        &KVMap::new(),
        FlbcExecutionLimits::default(),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    expect(&replay, expected);
    steps
}

const APPLY: &str = "def applyBoth (f : Nat -> Nat -> Nat) (a b : Nat) : Nat := f a b\n";
const SPEND: &str = "def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => spend k + 1\n";

#[test]
fn known_staged_callbacks_execute_through_the_ordinary_higher_order_consumer() {
    execute(
        &format!("{APPLY}#eval applyBoth (fun (x : Nat) => let saved : Nat := x + 1; fun (y : Nat) => saved + y) 20 21"),
        "42",
    );
}

#[test]
fn specialization_carries_open_runtime_captures_and_owned_string_values() {
    execute(
        "def size (f : Nat -> String -> String) (n : Nat) (s : String) : Nat := String.length (f n s)\ndef run (suffix : String) : Nat := size (fun (n : Nat) => let saved : String := suffix ++ suffix; fun (s : String) => saved ++ s) 7 \"xx\"\n#eval run \"abc\"",
        "8",
    );
    execute(
        &format!("{APPLY}def run (delta : Nat) : Nat := applyBoth (fun (x : Nat) => let saved : Nat := delta + x; fun (y : Nat) => saved + y) 20 16\n#eval run 6"),
        "42",
    );
}

#[test]
fn partially_applied_consumers_and_interleaved_templates_keep_concrete_types() {
    execute(
        &format!("{APPLY}#eval let saved : Nat -> Nat := applyBoth (fun (x : Nat) => let n : Nat := x + 1; fun (y : Nat) => n + y) 20; saved 21"),
        "42",
    );
    execute(
        "def use (ignored : Nat) {A : Type} (f : Nat -> A -> A) (n : Nat) (x : A) : A := f n x\n#eval use 9 (fun (n : Nat) => let base : Nat := n + 1; fun (x : Nat) => base + x) 20 21",
        "42",
    );
}

#[test]
fn an_unused_partial_result_still_performs_the_callback_first_stage() {
    let definitions = format!("{SPEND}def ignorePartial (f : Nat -> Nat -> Nat) (n : Nat) : Nat := let unused : Nat -> Nat := f n; 42\n");
    let program = |cost| format!("{definitions}#eval ignorePartial (fun (n : Nat) => let paid : Nat := spend n; fun (y : Nat) => y) {cost}");
    let idle = execute(&program(0), "42");
    let busy = execute(&program(30), "42");
    assert!(busy > idle + 30, "required stage was dropped: {idle} vs {busy}");
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

#[test]
fn unused_ordinary_operands_are_strict_even_when_callback_code_is_specialized() {
    let definitions = format!("{SPEND}def use (ignored : Nat) (f : Nat -> Nat -> Nat) : Nat := f 20 21\n");
    let program = |cost| format!("{definitions}#eval use (spend {cost}) (fun (x : Nat) => let n : Nat := x + 1; fun (y : Nat) => n + y)");
    let idle = execute(&program(0), "42");
    let busy = execute(&program(30), "42");
    assert!(
        busy > idle + 30,
        "ordinary argument disappeared: {idle} vs {busy}"
    );
}

#[test]
fn reader_bind_can_execute_a_known_closure_returning_continuation() {
    execute(
        r#"
class Pure (f : Type -> Type) where
  pure : {A : Type} -> A -> f A
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B
def Reader (A : Type) : Type := Nat -> A
instance readerPure : Pure Reader := { pure := fun a r => a }
instance readerBind : Bind Reader := { bind := fun action k r => k (action r) r }
def ask : Reader Nat := fun r => r
def work : Reader Nat := do
  let n ← ask
  return (n + 2)
#eval work 40
"#,
        "42",
    );
}

#[test]
fn budget_stops_and_invalid_callbacks_do_not_publish_or_poison_a_retry() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let source = format!("{APPLY}#eval applyBoth (fun (x : Nat) => let n : Nat := x + 1; fun (y : Nat) => n + y) 20 21");
    let mut tiny = limits();
    tiny.ingress.max_nodes = 1;
    assert!(
        base.execute_source_definitions(&[source.as_bytes()], &options, tiny)
            .is_err()
    );
    assert_eq!(base.logical_root(&options), root);
    let bad = format!("{source}\n#eval applyBoth (fun (b : Bool) (n : Nat) => n) 20 22");
    assert!(
        base.execute_source_definitions(&[bad.as_bytes()], &options, limits())
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
    expect(&first.executions.last().unwrap().exit, "42");
    assert_eq!(base.logical_root(&options), root);
}
