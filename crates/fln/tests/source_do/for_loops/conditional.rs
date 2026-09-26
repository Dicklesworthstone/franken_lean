//! Source-level conditional control flow retains both council seats and Golem.
use super::*;

const PROGRAMS: &str = r#"
def skipFirst : State Nat := do
  for x in items do
    if x == 1 then continue else mark x
    mark (x + 10)
  mark 9
  return 7
def stopSecond : State Nat := do
  for x in items do
    mark x
    if x == 2 then break else mark (x + 10)
    mark (x + 20)
  mark 9
  return 7
def onlyExits : State Nat := do
  for x in items do
    mark x
    if x == 1 then continue else break
    mark 99
  mark 9
  return 7
theorem skippedSuffix : (skipFirst 0).state = 21209 := by rfl
theorem stoppedLoop : (stopSecond 0).state = 111210209 := by rfl
theorem bothExits : (onlyExits 0).state = 10209 := by rfl
theorem unchangedResult : (stopSecond 0).value = 7 := by rfl
"#;

#[test]
fn conditional_break_and_continue_choose_distinct_exits_without_replaying_effects() {
    checked(&state_engine(), PROGRAMS);
}

#[test]
fn ordinary_do_conditionals_preserve_terminal_values_and_sequencing() {
    checked(&state_engine(), r#"
def select (flag : Bool) : Id Nat := do
  if flag then (17 : Id Nat) else (23 : Id Nat)
theorem selectedYes : select true = 17 := by rfl
theorem selectedNo : select false = 23 := by rfl
def effects (flag : Bool) : State Nat := do
  if flag then mark 1 else mark 2
  mark 9
  return 7
theorem yesEffects : (effects true 0).state = 109 := by rfl
theorem noEffects : (effects false 0).state = 209 := by rfl
def nestedTerm : Id Nat := do
  if true then (do return 42) else (do return 13)
theorem nestedValue : nestedTerm = 42 := by rfl
"#);
}

#[test]
fn nested_conditionals_and_nested_loops_keep_their_control_scopes() {
    checked(&state_engine(), r#"
def nestedChoices : State PUnit := do
  for x in items do
    if x == 1 then if false then break else continue else mark 2
    mark 9
theorem nestedChoiceValue : (nestedChoices 0).state = 209 := by rfl
def nestedLoops : State PUnit := do
  for x in items do
    for y in items do
      if y == 1 then continue else mark (x * 10 + y)
      break
    mark (x * 10 + 9)
theorem independentLoops : (nestedLoops 0).state = 12192229 := by rfl
"#);
}

#[test]
fn proof_binders_in_conditional_branches_cannot_capture_the_shared_suffix() {
    checked(&state_engine(), r#"
def scoped (h : Nat) : State PUnit := do
  for x in items do
    if h : x = 1 then continue else mark x
    mark h
theorem outerBinder : (scoped 9 0).state = 209 := by rfl
"#);
}

#[test]
fn abstract_monads_and_collections_share_the_checked_conditional_path() {
    checked(&engine(), r#"
def visitUntil {M : Type -> Type} [Pure M] [Bind M] {R A : Type} [ForIn M R A]
    (xs : R) (stop : A -> Bool) (action : A -> M PUnit) : M PUnit := do
  for x in xs do
    if stop x then break else action x
def filterVisit {M : Type -> Type} [Pure M] [Bind M] {R A : Type} [ForIn M R A]
    (xs : R) (skip : A -> Bool) (action : A -> M PUnit) : M PUnit := do
  for x in xs do
    if skip x then continue else action x
    action x
"#);
}

#[test]
fn invalid_unchosen_branches_and_out_of_scope_exits_do_not_publish() {
    let base = state_engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad : State PUnit := do if false then break else mark 1",
        "def bad : State PUnit := do if true then mark 1 else continue",
        "def bad : State PUnit := do for x in items do if false then missing x else mark x",
        "def bad : State PUnit := do for x in items do if true then break else (7 : Id Nat)",
        "def bad : State PUnit := do for x in items do if true then (do continue) else mark x",
        "def bad : State PUnit := do for x in items do if true then return PUnit.unit else mark x",
        "def bad : State PUnit := do for x in items do if true then break 1 else mark x",
        "def bad : State PUnit := do for x in items do if true then continue x else mark x",
        "def bad : State PUnit := do for x in items do if true then mark x",
        "def bad : State PUnit := do { for x in items do { if true then break else continue; missing } }",
    ] {
        assert!(base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits()).is_err(), "{source}");
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    checked(&base, "def recovery : State PUnit := do for x in items do if x == 1 then continue else mark x");
}

#[test]
fn conditional_exit_traces_execute_through_the_existing_runtime() {
    let base = checked(&state_engine(), PROGRAMS);
    for (query, expected) in [
        ("#eval (skipFirst 0).state", "21209"),
        ("#eval (stopSecond 0).state", "111210209"),
        ("#eval (onlyExits 0).state", "10209"),
    ] {
        let result = base.execute_source_definitions(
            &[query.as_bytes()], &KVMap::new(), EngineExecutionLimits::new(limits().admission.kernel),
        ).unwrap_or_else(|e| panic!("{query}: {e:?}")).into_complete().unwrap();
        let VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
            panic!("conditional loop did not return")
        };
        assert_eq!(fln_vm::interpreter::nat_decimal(&value.value).as_deref(), Some(expected));
    }
}
