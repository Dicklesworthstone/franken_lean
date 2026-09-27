//! Source guards exercise multi-statement lowering through real checked classes.
#![forbid(unsafe_code)]
use super::*;

fn state_engine() -> Engine {
    checked(
        &engine(),
        r#"
structure Result (A : Type) where
  value : A
  state : Nat
def State (A : Type) : Type := Nat -> Result A
instance statePure : Pure State := { pure := fun value state => { value := value, state := state } }
def stateNext {A B : Type} (r : Result A) (next : A -> State B) : Result B := next r.value r.state
instance stateBind : Bind State := { bind := fun action next state => stateNext (action state) next }
def mark (n : Nat) : State PUnit := fun s => { value := PUnit.unit, state := s * 10 + n }
def readState : State Nat := fun s => { value := s, state := s }
def natForState {B : Type} (xs : Nat) (b : B) (f : (a : Nat) -> a = xs -> B -> State (ForInStep B)) : State B :=
  Bind.bind (m := State) (f xs (by rfl) b) (fun step => Pure.pure (f := State) (stepValue step))
instance natStateIteration : ForIn' State Nat Nat memberNat := { forIn' := fun xs b f => natForState xs b f }
"#,
    )
}

#[test]
fn guarded_actions_and_monadic_bindings_run_once_only_on_the_false_branch() {
    checked(
        &state_engine(),
        r#"
def run (flag : Bool) : State Nat := do
  unless flag do
    let x := 1
    mark x
    let y <- readState
    mark (y + 1)
  mark 9
  return 42
theorem ran : (run false 0).state = 129 := by rfl
theorem skipped : (run true 0).state = 9 := by rfl
theorem value : (run false 0).value = 42 := by rfl
"#,
    );
}

#[test]
fn proposition_guards_and_generic_monads_use_the_existing_condition_checker() {
    checked(
        &engine(),
        r#"
def genericGuard {M : Type -> Type} [Pure M] [Bind M] (flag : Bool) (action : M PUnit) : M PUnit := do
  unless flag do
    action
    action
def propGuard (n : Nat) : Id Nat := do
  unless n = 7 do
    let x := n
    Pure.pure (f := Id) PUnit.unit
  return n
theorem falseGuard : propGuard 8 = 8 := by rfl
theorem trueGuard : propGuard 7 = 7 := by rfl
"#,
    );
}

#[test]
fn nested_guards_preserve_loop_exits_and_the_outer_continuation() {
    checked(
        &state_engine(),
        r#"
def guardedLoop (flag : Bool) : State Nat := do
  for h : x in 7 do
    mark 1
    unless flag do
      mark 2
      unless false do
        mark 3
        continue
      mark 4
    mark 5
  mark 9
  return 42
theorem continued : (guardedLoop false 0).state = 1239 := by rfl
theorem normal : (guardedLoop true 0).state = 159 := by rfl
def stopGuard : State Nat := do
  for h : x in 7 do
    unless false do
      mark 2
      break
    mark 3
  mark 9
  return 42
theorem stopped : (stopGuard 0).state = 29 := by rfl
"#,
    );
}

#[test]
fn branch_local_variables_and_unchosen_errors_do_not_escape_checking() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad : Id Nat := do { unless false do { let x := 7; Pure.pure (f := Id) PUnit.unit }; return x }",
        "def bad : Id PUnit := do unless true do missing",
        "def bad : Id PUnit := do unless 7 do Pure.pure (f := Id) PUnit.unit",
        "def bad : Id PUnit := do unless false do break",
        "def bad : Id PUnit := do unless false do continue",
        "def bad : Id Nat := do { unless false do { return 7 }; return 9 }",
        "def bad : Id PUnit := do for h : x in 7 do unless false do (do break)",
        "def bad : Id PUnit := do unless true do { let unused : Bool := 7; Pure.pure (f := Id) PUnit.unit }",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    checked(
        &base,
        "def recovery : Id PUnit := do unless false do Pure.pure (f := Id) PUnit.unit",
    );
}

#[test]
fn guarded_multistatement_source_executes_on_golem() {
    let source = r#"
def run : State Nat := do
  unless false do
    let x := 1
    mark x
    mark (x + 1)
  mark 9
  return 42
#eval (run 0).state
"#;
    let result = state_engine()
        .execute_source_definitions(
            &[source.as_bytes()],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().admission.kernel),
        )
        .unwrap_or_else(|e| panic!("{e:?}"))
        .into_complete()
        .unwrap();
    let VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
        panic!("unless did not return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
        Some("129")
    );
}
