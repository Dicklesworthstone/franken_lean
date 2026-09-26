//! Real source and real State dictionaries distinguish loop exit from iteration exit.
use super::*;

const PROGRAMS: &str = r#"
def stopping : State Nat := do
  for x in items do
    mark x
    break
  mark 9
  return 7
def continuing : State Nat := do
  for x in items do
    mark x
    continue
  mark 9
  return 7
theorem stoppedAtFirst : (stopping 0).state = 109 := by rfl
theorem continuedBoth : (continuing 0).state = 10209 := by rfl
theorem stoppedResult : (stopping 0).value = 7 := by rfl
theorem continuedResult : (continuing 0).value = 7 := by rfl
"#;

#[test]
fn break_preserves_prefix_effects_and_continue_reaches_the_next_iteration() {
    checked(&state_engine(), PROGRAMS);
}

#[test]
fn nested_break_exits_only_the_innermost_loop() {
    checked(&state_engine(), r#"
def nestedStops : State PUnit := do
  for x in items do
    for y in items do
      mark (x * 10 + y)
      break
    mark (x * 10 + 9)
theorem innerOnly : (nestedStops 0).state = 11192129 := by rfl
"#);
}

#[test]
fn jumps_work_with_abstract_dictionaries_and_do_not_capture_shadowed_names() {
    checked(&engine(), r#"
def stopFirst {M : Type -> Type} [Pure M] {R A : Type} [ForIn M R A] (xs : R) : M PUnit := do
  for x in xs do break
def nextEach {M : Type -> Type} [Pure M] {R A : Type} [ForIn M R A] (xs : R) : M PUnit := do
  for x in xs do continue
namespace ShadowControl
def ForInStep.done : Nat := 0
def «break» : Id PUnit := PUnit.unit
def noCapture : Id Nat := do
  «break»
  for x in true do break
  return 42
theorem result : noCapture = 42 := by rfl
end ShadowControl
"#);
}

#[test]
fn invalid_control_flow_never_publishes_and_a_fresh_request_recovers() {
    let base = state_engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad : State PUnit := do break",
        "def bad : State PUnit := do continue",
        "def bad : State PUnit := do for x in items do { (do break) }",
        "def bad : State PUnit := do for x in items do { (do continue) }",
        "def bad : State PUnit := do for x in items do { break; missing }",
        "def bad : State PUnit := do for x in items do { continue; missing }",
        "def bad : State PUnit := do for x in items do { let unused : Bool := 7; break }",
        "def bad : State PUnit := do for x in items do { let y := missing; continue }",
    ] {
        assert!(base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits()).is_err(), "{source}");
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    checked(&base, "def recovery : State PUnit := do for x in items do { mark x; break }");
}

#[test]
fn both_loop_exits_execute_on_the_existing_golem_path() {
    let base = checked(&state_engine(), PROGRAMS);
    for (query, expected) in [("#eval (stopping 0).state", "109"), ("#eval (continuing 0).state", "10209")] {
        let result = base.execute_source_definitions(
            &[query.as_bytes()], &KVMap::new(), EngineExecutionLimits::new(limits().admission.kernel),
        ).unwrap_or_else(|e| panic!("{query}: {e:?}")).into_complete().unwrap();
        let VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
            panic!("loop control did not return")
        };
        assert_eq!(fln_vm::interpreter::nat_decimal(&value.value).as_deref(), Some(expected));
    }
}
