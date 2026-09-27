//! Source text -> branch sequences -> both checkers -> native Golem execution.
use super::*;

const PROGRAMS: &str = r#"
def branched (flag : Bool) : State Nat := do
  if flag then
    let x := 1
    mark x
    mark (x + 1)
  else
    mark 3
    mark 4
  mark 9
  return 42
theorem yesBranch : (branched true 0).state = 10209 := by rfl
theorem noBranch : (branched false 0).state = 30409 := by rfl
def guarded (flag : Bool) : State Nat := do
  if flag then
    mark 1
    let ignored <- mark 2
    mark 3
  mark 9
  return 42
theorem guardYes : (guarded true 0).state = 1020309 := by rfl
theorem guardNo : (guarded false 0).state = 9 := by rfl
def branchLoop : State Nat := do
  for x in items do
    if x == 1 then
      mark 1
      if false then
        mark 8
        break
      continue
    else
      mark 2
      mark 3
    mark 4
  mark 9
  return 42
theorem loopTrace : (branchLoop 0).state = 102030409 := by rfl
def stopping : State Nat := do
  for x in items do
    if x == 1 then
      mark x
      break
    mark 8
  mark 9
  return 42
theorem stoppedTrace : (stopping 0).state = 109 := by rfl
"#;

#[test]
fn branches_guards_and_loop_exits_preserve_exact_effect_order() {
    checked(&state_engine(), PROGRAMS);
}

#[test]
fn braces_and_terminal_branch_returns_use_the_same_source_path() {
    checked(
        &engine(),
        r#"
def choose (flag : Bool) : Id Nat := do
  if flag then { let x := 17; return x } else { let y <- (23 : Id Nat); return y }
theorem yes : choose true = 17 := by rfl
theorem no : choose false = 23 := by rfl
def silent (flag : Bool) : Id PUnit := do
  if flag then
    Pure.pure (f := Id) PUnit.unit
    Pure.pure (f := Id) PUnit.unit
theorem skipped : silent false = PUnit.unit := by rfl
def nestedDo : Id Nat := do
  if true then
    let x <- (do return 41)
    return (x + 1)
  else
    return 0
theorem nestedReturn : nestedDo = 42 := by rfl
"#,
    );
}

#[test]
fn dangling_else_layout_and_else_if_chains_have_observable_branch_selection() {
    checked(
        &state_engine(),
        r#"
def nestedChoice (a b : Bool) : State Nat := do
  if a then
    if b then
      mark 1
      mark 2
  else
    mark 3
    mark 4
  mark 9
  return 42
theorem outerElse : (nestedChoice false true 0).state = 30409 := by rfl
theorem innerSkip : (nestedChoice true false 0).state = 9 := by rfl
def chain (a b : Bool) : State Nat := do
  if a then
    mark 1
  else if b then
    mark 2
  else
    mark 3
  mark 9
  return 42
theorem chainLast : (chain false false 0).state = 309 := by rfl
theorem chainMiddle : (chain false true 0).state = 209 := by rfl
"#,
    );
}

#[test]
fn proposition_evidence_and_branch_locals_do_not_capture_the_shared_suffix() {
    checked(
        &state_engine(),
        r#"
def scoped (h : Nat) : State PUnit := do
  for x in items do
    if h : x = 1 then
      let y := x
      mark y
      continue
    else
      let h := 7
      mark h
    mark h
theorem scopeTrace : (scoped 9 0).state = 10709 := by rfl
"#,
    );
}

#[test]
fn generic_branch_sequences_and_loop_guards_use_local_dictionaries() {
    checked(
        &engine(),
        r#"
def genericBranch {M : Type -> Type} [Pure M] [Bind M] (flag : Bool) (action : M PUnit) : M PUnit := do
  if flag then
    action
    action
def genericLoop {M : Type -> Type} [Pure M] [Bind M] {R A : Type} [ForIn M R A]
    (xs : R) (stop : A -> Bool) (action : A -> M PUnit) : M PUnit := do
  for x in xs do
    if stop x then
      action x
      break
    action x
"#,
    );
}

#[test]
fn invalid_unchosen_branch_locals_and_escaping_controls_do_not_publish() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad : Id Nat := do if false then return 7",
        "def bad : Id PUnit := do if false then { let x := unknown; Pure.pure (f := Id) PUnit.unit }",
        "def bad : Id PUnit := do if false then { let x : Bool := 7; Pure.pure (f := Id) PUnit.unit }",
        "def bad : Id PUnit := do if false then { Pure.pure (f := Id) PUnit.unit; break }",
        "def bad : Id PUnit := do if true then { continue } else { Pure.pure (f := Id) PUnit.unit }",
        "def bad : Id Nat := do { if true then { let x := 7; Pure.pure (f := Id) PUnit.unit }; return x }",
        "def bad : Id Nat := do { if true then { return 7 }; return 9 }",
        "def bad : Id PUnit := do for x in true do { if false then { return PUnit.unit }; Pure.pure (f := Id) PUnit.unit }",
        "def bad : Id PUnit := do for x in true do if true then { (do continue) }",
        "def bad : Id PUnit := do if true then { Pure.pure (f := Id) PUnit.unit } else { missing }",
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
        "def recovery : Id PUnit := do if true then { Pure.pure (f := Id) PUnit.unit; Pure.pure (f := Id) PUnit.unit }",
    );
}

#[test]
fn multistatement_branches_and_guards_execute_on_golem() {
    let base = checked(&state_engine(), PROGRAMS);
    for (query, expected) in [
        ("#eval (branched true 0).state", "10209"),
        ("#eval (branched false 0).state", "30409"),
        ("#eval (guarded false 0).state", "9"),
        ("#eval (branchLoop 0).state", "102030409"),
        ("#eval (stopping 0).state", "109"),
    ] {
        let result = base
            .execute_source_definitions(
                &[query.as_bytes()],
                &KVMap::new(),
                EngineExecutionLimits::new(limits().admission.kernel),
            )
            .unwrap_or_else(|e| panic!("{query}\n{e:?}"))
            .into_complete()
            .unwrap();
        let VmExit::Returned(value) = &result.executions.last().unwrap().exit else {
            panic!("branch execution did not return")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}

#[test]
fn if_and_unless_nesting_share_the_surrounding_loop_exit_scope() {
    checked(
        &state_engine(),
        r#"
def mixed : State Nat := do
  for x in items do
    if x == 1 then
      unless false do
        mark 1
        if true then
          mark 2
          continue
        mark 8
    mark 3
  mark 9
  return 42
theorem mixedTrace : (mixed 0).state = 1020309 := by rfl
"#,
    );
}
