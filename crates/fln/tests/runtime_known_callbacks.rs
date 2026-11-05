//! Known higher-order bodies execute through admission, native FIR and FLBC.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionError, EngineExecutionLimits,
    FlbcExecutionLimits, IngressError, KVMap, Name, Outcome, SourceCheckLimits, VmExit,
    execute_flbc_artifact,
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
const SPEND: &str =
    "def spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => spend k + 1\n";

#[test]
fn ordinary_higher_order_arguments_do_not_repeat_callback_annotation() {
    execute(
        "def use (f : (Nat -> Nat) -> Nat) : Nat := f (fun n => n)\n#eval use (fun g => g 42)",
        "42",
    );
    execute(
        "def use (f : (Nat -> Nat) -> Nat) : Nat := f (fun n => n)\n#eval let callback : (Nat -> Nat) -> Nat := fun g => g 42; use callback",
        "42",
    );
    execute(
        "#eval let callback : (Nat -> Nat) -> Nat := fun g => g 21; let forward : ((Nat -> Nat) -> Nat) -> Nat := fun f => f (fun n => n); callback (fun n => n) + forward callback",
        "42",
    );
}

#[test]
fn known_staged_callbacks_execute_through_the_ordinary_higher_order_consumer() {
    execute(
        &format!(
            "{APPLY}#eval applyBoth (fun (x : Nat) => let saved : Nat := x + 1; fun (y : Nat) => saved + y) 20 21"
        ),
        "42",
    );
}

const NESTED_PARTIAL: &str = r#"
partial def nestedConsumer (f : Nat -> Nat -> Nat -> Nat -> Nat) (n : Nat) : Nat :=
  if n == 0 then f n 2 3 1 else
    Nat.add (f n 2 3 1) (nestedConsumer f (Nat.pred n))
"#;

#[test]
fn recursive_consumers_preserve_nested_callback_result_stages() {
    // Both arithmetic lets are used. The callback has a two-argument prefix,
    // then a one-argument prefix, then its final state closure.
    execute(
        &format!(
            "{NESTED_PARTIAL}\
#eval nestedConsumer
  (fun a b =>
    let outer := Nat.add a b
    fun acc =>
      let saved := Nat.add outer acc
      fun state => Nat.add saved state) 3"
        ),
        "30",
    );
    // Equal interfaces share the recursive variant while captures stay
    // dynamic; an ordinary flat callback still uses its distinct interface.
    execute(
        &format!(
            "{NESTED_PARTIAL}\
def nestedRun (offset : Nat) : Nat :=
  nestedConsumer
    (fun a b =>
      let outer := Nat.add (Nat.add a b) offset
      fun acc =>
        let saved := Nat.add outer acc
        fun state => Nat.add saved state) 3
#eval Nat.add (nestedRun 0)
  (Nat.add (nestedRun 10)
    (nestedConsumer (fun a b acc state => Nat.add (Nat.add (Nat.add a b) acc) state) 3))"
        ),
        "130",
    );
}

#[test]
fn recursive_consumers_keep_known_stages_before_computed_callback_tails() {
    for (source, expected) in [
        (
            r#"
#eval nestedConsumer
  (fun a b =>
    let outer := Nat.add a b
    fun acc =>
      let saved := Nat.add outer acc
      Nat.add saved) 3
"#,
            "30",
        ),
        (
            r#"
#eval nestedConsumer
  (fun a b =>
    let outer := Nat.add a b
    fun acc =>
      let saved := Nat.add outer acc
      let action : Nat -> Nat := fun state => Nat.add saved state
      action) 3
"#,
            "30",
        ),
        (
            r#"
def stateSuffix (saved : Nat) : Nat -> Nat :=
  let captured := Nat.add saved 1
  fun state => Nat.add captured state

#eval nestedConsumer
  (fun a b =>
    let outer := Nat.add a b
    fun acc => stateSuffix (Nat.add outer acc)) 3
"#,
            "34",
        ),
    ] {
        execute(&format!("{NESTED_PARTIAL}{source}"), expected);
    }
}

#[test]
fn recursive_consumers_match_late_closed_callback_forwarding() {
    // Child preparation exposes a closed suffix. Ordinary local registration
    // then forwards it as one flat residual stage; the recursive consumer must
    // select that exact interface after preparation, not predict two stages.
    execute(
        r#"
def closedSuffix : Nat -> Nat :=
  (fun (_ : Nat) => fun state => Nat.add state 1) 0

partial def closedTailConsumer
    (f : Nat -> Nat -> Nat -> Nat -> Nat) (n : Nat) : Nat :=
  if n == 0 then f n 2 3 1 else
    Nat.add (f n 2 3 1) (closedTailConsumer f (Nat.pred n))

#eval closedTailConsumer
  (fun a b =>
    let paid := Nat.add a b
    fun acc => closedSuffix) 3
"#,
        "8",
    );
}

#[test]
fn recursive_middle_callbacks_keep_captures_when_the_consumer_is_under_applied() {
    // The callback's final let scope includes the preceding bias operand.
    // Both supplied bindings must remain outside the missing n lambda, and
    // offset must keep its original outer slot after the one-time lift.
    for (offset, expected) in [(10, "77"), (0, "37")] {
        execute(
            &format!(
                "\
partial def middle (bias : Nat) (f : Nat -> Nat -> Nat -> Nat -> Nat) (n : Nat) : Nat :=
  if n == 0 then Nat.add (f n 2 3 1) bias else
    Nat.add (f n 2 3 1) (middle bias f (Nat.pred n))
def middleRun (offset : Nat) : Nat :=
  let loop := middle 7
    (fun a b =>
      let outer := Nat.add (Nat.add a b) offset
      fun acc =>
        let saved := Nat.add outer acc
        Nat.add saved)
  loop 3
#eval middleRun {offset}"
            ),
            expected,
        );
    }
}

#[test]
fn discarded_nested_callback_results_still_execute_the_second_prefix() {
    let source = |cost| {
        format!(
            "{SPEND}\
partial def ignoreNested (f : Nat -> Nat -> Nat -> Nat) (n second : Nat) : Nat :=
  let first := f n
  let unused := first second
  if n == 0 then 42 else ignoreNested f (Nat.pred n) second
#eval ignoreNested
  (fun n =>
    let outer := Nat.add n 1
    fun acc =>
      let paid := spend acc
      fun state => Nat.add (Nat.add outer paid) state) 3 {cost}"
        )
    };
    let idle = execute(&source(0), "42");
    let busy = execute(&source(30), "42");
    assert!(
        busy > idle + 30,
        "the second strict prefix disappeared: {idle} vs {busy}"
    );
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let mut bounded = limits();
    bounded.vm.max_steps = idle;
    assert!(matches!(
        base.execute_source_definitions(&[source(30).as_bytes()], &options, bounded)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
}

fn assert_foreign_extern_is_not_inlined(definition: &str, target: &str, query: &str) {
    let options = KVMap::new();
    let clean = engine()
        .check_source_files(
            &[definition.as_bytes()],
            &options,
            SourceCheckLimits::new(limits().admission()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let clean_root = clean.logical_root(&options);
    let decorated = Engine::from_environment(
        fln_elab::externs::register(
            clean.environment(),
            &Name::from_components([target]),
            vec![fln_elab::externs::ExternEntry::Standard {
                backend: Name::from_components(["all"]),
                symbol: "foreign_staged_function".to_owned(),
            }],
        )
        .unwrap(),
    );
    let decorated_root = decorated.logical_root(&options);
    // The source is checked and executes normally; only the selected extern
    // policy makes the otherwise identical decorated definition unsupported.
    let ordinary = clean
        .execute_source_definitions(&[query.as_bytes()], &options, limits())
        .unwrap()
        .into_complete()
        .unwrap();
    expect(&ordinary.executions.last().unwrap().exit, "42");
    let mut error = decorated
        .execute_source_definitions(&[query.as_bytes()], &options, limits())
        .unwrap_err();
    while let EngineExecutionError::BatchCommand { error: inner, .. } = error {
        error = *inner;
    }
    assert!(
        matches!(
            error,
            EngineExecutionError::Ingress(IngressError::UnsupportedNode {
                kind: "native extern attribute does not match the supported ABI"
            })
        ),
        "selected {target} metadata was bypassed: {error:?}"
    );
    assert_eq!(decorated.logical_root(&options), decorated_root);
    assert_eq!(clean.logical_root(&options), clean_root);
}

#[test]
fn selected_staged_callback_consumer_cannot_bypass_foreign_extern_metadata() {
    assert_foreign_extern_is_not_inlined(
        APPLY,
        "applyBoth",
        "#eval applyBoth (fun (x : Nat) => let saved : Nat := x + 1; fun (y : Nat) => saved + y) 20 21",
    );
    assert_foreign_extern_is_not_inlined(
        APPLY,
        "applyBoth",
        "#eval let callback : Nat -> Nat -> Nat := fun (x : Nat) => let saved : Nat := x + 1; fun (y : Nat) => saved + y; let alias : Nat -> Nat -> Nat := callback; applyBoth alias 20 21",
    );
}

#[test]
fn selected_staged_producer_cannot_bypass_foreign_extern_metadata() {
    assert_foreign_extern_is_not_inlined(
        "def producer (x : Nat) : Nat -> Nat := let saved : Nat := x + 1; fun (y : Nat) => saved + y\n",
        "producer",
        "#eval producer 20 21",
    );
}

#[test]
fn specialization_carries_open_runtime_captures_and_owned_string_values() {
    execute(
        "def size (f : Nat -> String -> String) (n : Nat) (s : String) : Nat := String.length (f n s)\ndef run (suffix : String) : Nat := size (fun (n : Nat) => let saved : String := suffix ++ suffix; fun (s : String) => saved ++ s) 7 \"xx\"\n#eval run \"abc\"",
        "8",
    );
    execute(
        &format!(
            "{APPLY}def run (delta : Nat) : Nat := applyBoth (fun (x : Nat) => let saved : Nat := delta + x; fun (y : Nat) => saved + y) 20 16\n#eval run 6"
        ),
        "42",
    );
}

#[test]
fn partially_applied_consumers_and_interleaved_templates_keep_concrete_types() {
    execute(
        &format!(
            "{APPLY}#eval let saved : Nat -> Nat := applyBoth (fun (x : Nat) => let n : Nat := x + 1; fun (y : Nat) => n + y) 20; saved 21"
        ),
        "42",
    );
    execute(
        "def use (ignored : Nat) {A : Type} (f : Nat -> A -> A) (n : Nat) (x : A) : A := f n x\n#eval use 9 (fun (n : Nat) => let base : Nat := n + 1; fun (x : Nat) => base + x) 20 21",
        "42",
    );
}

#[test]
fn an_unused_partial_result_still_performs_the_callback_first_stage() {
    let definitions = format!(
        "{SPEND}def ignorePartial (f : Nat -> Nat -> Nat) (n : Nat) : Nat := let unused : Nat -> Nat := f n; 42\n"
    );
    let program = |cost| {
        format!(
            "{definitions}#eval ignorePartial (fun (n : Nat) => let paid : Nat := spend n; fun (y : Nat) => y) {cost}"
        )
    };
    let idle = execute(&program(0), "42");
    let busy = execute(&program(30), "42");
    assert!(
        busy > idle + 30,
        "required stage was dropped: {idle} vs {busy}"
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

#[test]
fn unused_ordinary_operands_are_strict_even_when_callback_code_is_specialized() {
    let definitions =
        format!("{SPEND}def use (ignored : Nat) (f : Nat -> Nat -> Nat) : Nat := f 20 21\n");
    let program = |cost| {
        format!(
            "{definitions}#eval use (spend {cost}) (fun (x : Nat) => let n : Nat := x + 1; fun (y : Nat) => n + y)"
        )
    };
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
    let source = format!(
        "{APPLY}#eval applyBoth (fun (x : Nat) => let n : Nat := x + 1; fun (y : Nat) => n + y) 20 21"
    );
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
