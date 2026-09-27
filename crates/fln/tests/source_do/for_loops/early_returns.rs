//! Guarded returns keep the enclosing do result, not a branch's unit result.
use super::*;

#[test]
fn pure_early_returns_need_no_loop_or_unit_library() {
    checked(
        &super::super::engine(),
        r#"
def choose (b : Bool) : Id Nat := do
  if b then
    return 7
  return 9
theorem yes : choose true = 7 := by rfl
theorem no : choose false = 9 := by rfl
def nested (a b : Bool) : Id Nat := do
  if a then
    if b then return 1
    return 2
  return 3
theorem nestedYes : nested true true = 1 := by rfl
theorem nestedNo : nested true false = 2 := by rfl
theorem outerNo : nested false true = 3 := by rfl
"#,
    );
}

#[test]
fn abstract_monads_share_result_types_without_requiring_bind_for_pure_guards() {
    checked(
        &super::super::engine(),
        r#"
def choose {M : Type -> Type} [Pure M] {A : Type} (flag : Bool) (yes no : A) : M A := do
  if flag then return yes
  return no
"#,
    );
}

const PROGRAM: &str = r#"
def run (flag : Bool) : State Nat := do
  mark 1
  if flag then
    let x : Nat <- Pure.pure (f := State) 7
    mark 2
    return x
  mark 3
  return 9
theorem returnedValue : (run true 0).value = 7 := by rfl
theorem returnedEffects : (run true 0).state = 102 := by rfl
theorem normalValue : (run false 0).value = 9 := by rfl
theorem normalEffects : (run false 0).state = 103 := by rfl
"#;

#[test]
fn prefix_effects_run_once_and_the_returning_branch_skips_the_suffix() {
    checked(&state_engine(), PROGRAM);
}

#[test]
fn branch_locals_and_proposition_witnesses_cannot_capture_the_shared_suffix() {
    checked(
        &state_engine(),
        r#"
def scoped (h x : Nat) (flag : Bool) : State Nat := do
  if h : flag = true then
    let x := 1
    mark x
    return 7
  mark x
  return h
theorem earlyScope : (scoped 9 2 true 0).state = 1 := by rfl
theorem normalScope : (scoped 9 2 false 0).state = 2 := by rfl
theorem outerName : (scoped 9 2 false 0).value = 9 := by rfl
"#,
    );
}

#[test]
fn nested_do_returns_and_completed_loops_do_not_exit_the_outer_do() {
    checked(
        &state_engine(),
        r#"
def nested (flag : Bool) : State Nat := do
  let n <- do
    if flag then return 7
    return 8
  for x in items do mark x
  if n == 7 then return 3
  mark 9
  return 4
theorem innerEarly : (nested true 0).value = 3 := by rfl
theorem innerScope : (nested true 0).state = 102 := by rfl
theorem fallthrough : (nested false 0).state = 10209 := by rfl
def guarded (flag : Bool) : State Nat := do
  unless flag do
    mark 1
    return 7
  mark 2
  return 9
theorem unlessEarly : (guarded false 0).state = 1 := by rfl
theorem unlessNormal : (guarded true 0).state = 2 := by rfl
"#,
    );
}

#[test]
fn unchosen_branches_and_unused_continuations_still_require_checking() {
    let base = state_engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad : State Nat := do { if true then { return 7 }; missing; return 9 }",
        "def bad : State Nat := do { if true then { return 7 } else { return 8 }; let x : Bool := 7; return 9 }",
        "def bad : State Nat := do { if false then { return true }; return 9 }",
        "def bad : State Nat := do { if false then { let x := missing; return 7 }; return 9 }",
        "def bad : State Nat := do { if false then { return 7 }; return x }",
        "def bad : State Nat := do { for x in items do { if true then { return 7 } }; return 9 }",
    ] {
        fln_parse::parse_definition(source.as_bytes())
            .unwrap_or_else(|e| panic!("negative must reach elaboration: {source}: {e:?}"));
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    checked(
        &base,
        "def recovery : State Nat := do { if true then { return 7 }; return 9 }",
    );
}

#[test]
fn early_returns_execute_lazily_on_golem() {
    let base = checked(&state_engine(), PROGRAM);
    for (query, expected) in [
        ("#eval (run true 0).state", "102"),
        ("#eval (run false 0).state", "103"),
        ("#eval (run true 0).value", "7"),
        ("#eval (run false 0).value", "9"),
    ] {
        let result = base
            .execute_source_definitions(
                &[query.as_bytes()],
                &KVMap::new(),
                EngineExecutionLimits::new(limits().admission.kernel),
            )
            .unwrap_or_else(|e| panic!("{query}: {e:?}"))
            .into_complete()
            .unwrap();
        let VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
            panic!("early return did not return")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}

#[test]
fn nested_inference_retains_result_constraints_across_completed_loops() {
    let base = state_engine();
    for source in [
        "def f (b : Bool) : State Nat := do\n  let n <- do\n    if b then return 7\n    return 8\n  for x in items do mark x\n  if n == 7 then return 3\n  mark 9\n  return 4",
        "def f (b : Bool) : State Nat := do\n  let n : Nat <- do\n    if b then return 7\n    return 8\n  for x in items do mark x\n  if n == 7 then return 3\n  mark 9\n  return 4",
        "def f (b : Bool) : State Nat := do\n  let n <- do\n    return 8\n  for x in items do mark x\n  if n == 7 then mark 3\n  mark 9\n  return 4",
        "def f (b : Bool) : State Nat := do\n  let n <- do\n    if b then return 7\n    return 8\n  for x in items do mark x\n  if n == 7 then return 3\n  return 4",
        "def f (b : Bool) : State Nat := do\n  let n <- do\n    return 8\n  return n",
        "def f (b : Bool) : State Nat := do\n  let n <- do\n    if b then return 7\n    return 8\n  return n",
        "def f (b : Bool) : State Nat := do\n  let n : Nat <- do\n    if b then return 7\n    return 8\n  return n",
        "def f (b : Bool) : State Nat := do\n  let n <- do\n    if b then return 7\n    return 8\n  for x in items do mark x\n  return n",
        "def f (b : Bool) : State Nat := do\n  let n : Nat <- do\n    if b then return 7\n    return 8\n  for x in items do mark x\n  return n",
        "def f (b : Bool) : State Nat := do\n  let n <- do\n    if b then return 7\n    return 8\n  if n == 7 then return 3\n  return 4",
        "def f (b : Bool) : State Nat := do\n  let n : Nat <- do\n    if b then return 7\n    return 8\n  if n == 7 then return 3\n  return 4",
    ] {
        checked(&base, source);
    }
}

#[test]
fn higher_order_and_boolean_results_retain_the_enclosing_expected_type() {
    checked(
        &super::super::engine(),
        r#"
def booleanResult (flag : Bool) : Id Bool := do
  if flag then return false
  return true
theorem booleanYes : booleanResult true = false := by rfl
theorem booleanNo : booleanResult false = true := by rfl
def functionResult (flag : Bool) (x : Nat) : Id (Nat -> Nat) := do
  if flag then
    let y := x + 1
    return fun n => n + y
  return fun n => n + x
theorem functionYes : functionResult true 7 2 = 10 := by rfl
theorem functionNo : functionResult false 7 2 = 9 := by rfl
"#,
    );
}

#[test]
fn both_returning_branches_keep_an_unused_well_typed_suffix_lazy() {
    let base = checked(
        &state_engine(),
        r#"
def bothReturn (flag : Bool) : State Nat := do
  mark 1
  if flag then
    mark 2
    return 7
  else
    mark 3
    return 8
  mark 9
  return 0
theorem firstBranch : (bothReturn true 0).state = 102 := by rfl
theorem secondBranch : (bothReturn false 0).state = 103 := by rfl
"#,
    );
    for (query, expected) in [
        ("#eval (bothReturn true 0).state", "102"),
        ("#eval (bothReturn false 0).state", "103"),
    ] {
        let result = base
            .execute_source_definitions(
                &[query.as_bytes()],
                &KVMap::new(),
                EngineExecutionLimits::new(limits().admission.kernel),
            )
            .unwrap_or_else(|e| panic!("{query}: {e:?}"))
            .into_complete()
            .unwrap();
        let VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
            panic!("returning branch did not return")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}
