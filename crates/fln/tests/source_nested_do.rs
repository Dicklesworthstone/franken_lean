//! Bare do elements share return scope; parenthesized term-do starts a scope.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Outcome, VmExit};

const ID: &str = r#"
class Pure (f : Type -> Type) where
  pure : {A : Type} -> A -> f A
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B
def Id (A : Type) : Type := A
instance idPure : Pure Id := { pure := fun a => a }
instance idBind : Bind Id := { bind := fun a k => k a }
"#;

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}
fn execute(source: &str, expected: &str) {
    let source = format!("{ID}{source}");
    let batch = engine()
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &batch.executions.last().unwrap().exit else {
        panic!("not returned")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some(expected),
        "{source}"
    );
}

#[test]
fn bare_and_parenthesized_do_have_distinct_return_scopes() {
    execute(
        "def nested (seed : Nat) : Id Nat := do\n  let n ← do\n    let n ← (seed : Id Nat)\n    return (n + 1)\n  let n ← (n + 1 : Id Nat)\n  return n\n#eval nested 40",
        "41",
    );
    execute(
        "def nested (seed : Nat) : Id Nat := do\n  let n ← (do\n    let n ← (seed : Id Nat)\n    return (n + 1))\n  let n ← (n + 1 : Id Nat)\n  return n\n#eval nested 40",
        "42",
    );
    // This is the original runtime_specialization reproducer. Its non-Unit
    // action is syntactically dead, so the pin warns and returns 41.
    execute(
        "def nested (seed : Nat) : Id Nat := do\n  let n ← do\n    let n ← (seed : Id Nat)\n    return (n + 1)\n  (10 : Id Nat)\n  let n ← (n + 1 : Id Nat)\n  return n\n#eval nested 40",
        "41",
    );
}

#[test]
fn final_actions_resume_the_value_continuation_in_the_outer_lexical_scope() {
    execute(
        "def nested (seed : Nat) : Id Nat := do\n  let n ← do\n    let n ← (seed : Id Nat)\n    (n + 1 : Id Nat)\n  return (n + 1)\n#eval nested 40",
        "42",
    );
    execute(
        "def scopeValue (n : Nat) : Id Nat := do\n  let x ← do\n    let n := true\n    (n : Id Bool)\n  return (if x then n else 0)\n#eval scopeValue 42",
        "42",
    );
    execute(
        "def terminal : Id Nat := do\n  do\n    return 42\n#eval terminal",
        "42",
    );
}

#[test]
fn early_returns_use_the_outer_result_even_when_normal_values_are_boolean() {
    for (flag, expected) in [("true", "41"), ("false", "42")] {
        execute(
            &format!(
                "def choose (flag : Bool) : Id Nat := do\n  let b : Bool ← do\n    if flag then return 41\n    (false : Id Bool)\n  return (if b then 0 else 42)\n#eval choose {flag}"
            ),
            expected,
        );
    }
    execute(
        "def abstracted {M : Type -> Type} [Pure M] [Bind M] {A B : Type} (flag : Bool) (normal : M A) (early : B) (finish : A -> M B) : M B := do\n  let a ← do\n    if flag then return early\n    normal\n  finish a\n#eval (abstracted (M := Id) false (false : Id Bool) 41 (fun b => if b then (0 : Nat) else (42 : Nat)) : Id Nat)",
        "42",
    );
}

#[test]
fn ordinary_polymorphic_calls_keep_written_result_type_hints() {
    // This call has no do body: retaining the original result equation is a
    // general application inference requirement, including bare numerals.
    execute(
        "def selectResult {M : Type -> Type} {A B : Type} (normal : A) (early : B) (finish : A -> M B) : M B := finish normal\n#eval (selectResult (M := Id) false 41 (fun b => if b then (0 : Nat) else (42 : Nat)) : Id Nat)",
        "42",
    );
}

#[test]
fn written_monadic_operations_preserve_their_result_parameters() {
    execute(
        "def writtenPure : Id Nat := Pure.pure (f := Id) 42\n#eval writtenPure",
        "42",
    );
    execute(
        "def writtenBind : Id Nat := Bind.bind (m := Id) ((7 : Nat) : Id Nat) (fun seed => Pure.pure 42)\n#eval writtenBind",
        "42",
    );
    // Function-valued results may be overapplied. These last arguments belong
    // to the returned function, not to Pure or Bind's original telescope.
    execute(
        "def overPure : Id Nat := (Pure.pure (f := Id) (fun (x : Nat) => Pure.pure (f := Id) (x + 1))) 41\n#eval overPure",
        "42",
    );
    execute(
        "def overBind : Id Nat := Bind.bind (m := Id) ((7 : Nat) : Id Nat) (fun seed => Pure.pure (f := Id) (fun (x : Nat) => seed + x)) 35\n#eval overBind",
        "42",
    );
}

#[test]
fn continuation_domains_come_from_actions_or_explicit_binder_annotations() {
    // Field resolution needs the action's concrete record type before checking
    // the suffix; an unconstrained continuation parameter is insufficient.
    execute(
        "structure Payload where\n  value : Nat\ndef nestedField : Id Nat := do\n  let x ← do\n    (Pure.pure (Payload.mk 42) : Id Payload)\n  return x.value\n#eval nestedField",
        "42",
    );
    // Conversely, an explicit binder annotation must reach an action whose
    // record literal cannot infer its own carrier (including the Id alias).
    execute(
        "structure Payload where\n  value : Nat\ndef nestedField : Id Nat := do\n  let x : Payload ← do\n    Pure.pure { value := 42 }\n  return x.value\n#eval nestedField",
        "42",
    );
    execute(
        "def deadTyped : Id Nat := do\n  let b : Bool ← do\n    return 41\n  return (if b then 0 else 42)\n#eval deadTyped",
        "41",
    );
}

const STATE: &str = r#"
structure StateResult (A : Type) where
  value : A
  state : Nat
def State (A : Type) : Type := Nat -> StateResult A
instance statePure : Pure State := { pure := fun value state => { value := value, state := state } }
def stateNext {A B : Type} (r : StateResult A) (next : A -> State B) : StateResult B := next r.value r.state
instance stateBind : Bind State := { bind := fun action next state => stateNext (action state) next }
def mark (n : Nat) : State PUnit := fun s => { value := PUnit.unit, state := s * 100 + n }
"#;

#[test]
fn nested_prefix_effects_run_once_and_returning_branches_skip_the_suffix() {
    for (flag, expected) in [("true", "102"), ("false", "1020304")] {
        execute(
            &format!(
                "{STATE}\ndef work (flag : Bool) : State Nat := do\n  mark 1\n  let b : Bool ← do\n    mark 2\n    if flag then return 41\n    mark 3\n    Pure.pure (f := State) false\n  mark 4\n  return (if b then 0 else 42)\n#eval (work {flag} 0).state"
            ),
            expected,
        );
    }
}

const LOOP: &str = r#"
inductive ForInStep (A : Type) where | done (value : A) | yield (value : A)
class ForIn (m : Type -> Type) (R : Type) (A : outParam Type) where
  forIn : {B : Type} -> R -> B -> (A -> B -> m (ForInStep B)) -> m B
def stepValue {A : Type} (step : ForInStep A) : A := match step with | .done value => value | .yield value => value
def boolFor {B : Type} (xs : Bool) (b : B) (f : Nat -> B -> Id (ForInStep B)) : Id B := if xs then stepValue (f 42 b) else b
instance idBoolFor : ForIn Id Bool Nat := { forIn := fun xs b f => boolFor xs b f }
"#;

#[test]
fn nested_elements_keep_the_enclosing_loop_return_scope() {
    for (collection, flag, expected) in [
        ("true", "true", "43"),
        ("true", "false", "7"),
        ("false", "true", "7"),
    ] {
        execute(
            &format!(
                "{LOOP}\ndef find (xs flag : Bool) : Id Nat := do\n  for x in xs do\n    let b : Bool ← do\n      if flag then return (x + 1)\n      (false : Id Bool)\n    Pure.pure (f := Id) PUnit.unit\n  return 7\n#eval find {collection} {flag}"
            ),
            expected,
        );
    }
    for jump in ["break", "continue"] {
        for (flag, expected) in [("true", "7"), ("false", "0")] {
            execute(
                &format!(
                    "{LOOP}\ndef find (flag : Bool) : Id Nat := do\n  for x in true do\n    let b : Bool ← do\n      if flag then {jump}\n      (false : Id Bool)\n    return 0\n  return 7\n#eval find {flag}"
                ),
                expected,
            );
        }
    }
}

#[test]
fn reachable_type_errors_are_not_discarded_and_failure_preserves_the_engine() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for body in [
        "def bad : Id Nat := do\n  let n ← do\n    (40 : Id Nat)\n  (10 : Id Nat)\n  return n\n#eval bad",
        "def bad : Id Nat := do\n  let b : Bool ← do\n    if false then return true\n    (false : Id Bool)\n  return 42\n#eval bad",
        "def bad : Id Nat := do\n  let n : MissingType ← do\n    return 41\n  return n\n#eval bad",
        "def bad : Id Nat := do\n  let n : 3 ← do\n    return 41\n  return n\n#eval bad",
    ] {
        let source = format!("{ID}{body}");
        assert!(
            base.execute_source_definitions(&[source.as_bytes()], &options, limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&options), root);
    }
}

#[test]
fn resource_stops_preserve_prefix_evaluation_and_allow_clean_retry() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let program = |cost| {
        format!(
            "{ID}\ndef spend (n : Nat) : Nat := match n with | .zero => 0 | .succ k => spend k + 1\ndef work (cost : Nat) : Id Nat := do\n  let n ← do\n    let paid ← (spend cost : Id Nat)\n    return 41\n  let unreachable ← (spend 100000 : Id Nat)\n  return (n + unreachable)\n#eval work {cost}"
        )
    };
    let mut bounded = limits();
    bounded.vm.max_steps = 2000;
    bounded.vm.max_stack_depth = 256;
    let expensive = program(100000);
    assert!(matches!(
        base.execute_source_definitions(&[expensive.as_bytes()], &options, bounded)
            .unwrap(),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(base.logical_root(&options), root);
    let cheap = program(0);
    let retry = || {
        base.execute_source_definitions(&[cheap.as_bytes()], &options, bounded)
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let first = retry();
    let second = retry();
    let VmExit::Returned(value) = &first.executions.last().unwrap().exit else {
        panic!("retry did not return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("41")
    );
    assert_eq!(
        first.executions.last().unwrap().flbc_artifact,
        second.executions.last().unwrap().flbc_artifact
    );
    assert_eq!(base.logical_root(&options), root);
}
