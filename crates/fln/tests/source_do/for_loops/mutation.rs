//! `let mut` and reassignment over this file's miniature `Id`, `State` and `ForIn`. These are
//! the shapes of `fln-cli`'s `source_do_mutation` (over the pin's own Init, each run through the
//! pinned `lean` v4.32.0), here without imports so they also run where the pin is absent:
//! straight-line reassignment, a branch that reassigns, loop state across iterations, `break` and
//! `continue` after a reassignment, branches that reassign inside a loop, a bound branch inside a
//! loop, branches that reassign and then `break` or `continue`, one that reassigns beside one that
//! breaks, and effects that read the current value.
#![forbid(unsafe_code)]
use super::*;

const PROGRAMS: &str = r#"
structure Prod (A B : Type) where
  fst : A
  snd : B
def straight (n : Nat) : Id Nat := do
  let mut x := n
  x := x + 1
  x := x * 2
  return x
def branch (b : Bool) : Id Nat := do
  let mut x := 1
  if b then
    x := 10
  return x + 1
def total : State Nat := do
  let mut s := 0
  for x in items do
    s := s + x
  return s
def pair : State Nat := do
  let mut s := 0
  let mut c := 10
  for x in items do
    s := s + x
    c := c + 1
  return s * 100 + c
def stopped : State Nat := do
  let mut s := 0
  for x in items do
    s := s + x
    if x = 1 then break
    s := s + 100
  return s
def skipped : State Nat := do
  let mut s := 0
  for x in items do
    s := s + 1
    if x = 1 then continue
    s := s + 10
  return s
def effects : State Nat := do
  let mut s := 0
  for x in items do
    s := s + x
    mark s
  return s
def counted : State Nat := do
  let mut c := 0
  for x in items do
    if x = 1 then
      c := c + 10
  return c
def chosen : State Nat := do
  let mut c := 0
  for x in items do
    if x = 1 then
      c := c + 10
    else
      c := c + 1
  return c
def stepped : State Nat := do
  let mut c := 0
  for x in items do
    if x = 1 then
      c := c + 10
    c := c + 1
  return c
def bound : State Nat := do
  let mut c := 0
  for x in items do
    let y ← if x = 1 then Pure.pure (f := State) 5 else Pure.pure (f := State) 2
    c := c + y
  return c
def leaveWith : State Nat := do
  let mut s := 0
  for x in items do
    if x = 1 then
      s := s + 100
      break
    s := s + x
  return s
def skipWith : State Nat := do
  let mut s := 0
  for x in items do
    if x = 1 then
      s := s + 100
      continue
    s := s + x
  return s
def bothJump : State Nat := do
  let mut s := 0
  for x in items do
    if x = 2 then
      s := s + 1000
      break
    else
      s := s + x
      continue
  return s
def mixed : State Nat := do
  let mut s := 0
  for x in items do
    if x = 1 then
      s := s + 10
    else
      break
    s := s + x
  return s
def typedLoop : State Nat := do
  let mut s := 0
  for (x : Nat) in items do
    s := s + x
  return s
def lastLoop : State PUnit := do
  let mut s := 0
  for x in items do
    s := s + x
    mark s
"#;

#[test]
fn reassignments_reach_every_later_read() {
    checked(
        &state_engine(),
        &format!(
            "{PROGRAMS}\
theorem straightValue : straight 3 = 8 := by rfl
theorem branchTrue : branch true = 11 := by rfl
theorem branchFalse : branch false = 2 := by rfl
theorem totalValue : (total 0).value = 3 := by rfl
theorem pairValue : (pair 0).value = 312 := by rfl
theorem stoppedValue : (stopped 0).value = 1 := by rfl
theorem skippedValue : (skipped 0).value = 12 := by rfl
theorem effectsState : (effects 0).state = 103 := by rfl
theorem effectsValue : (effects 0).value = 3 := by rfl
theorem countedValue : (counted 0).value = 10 := by rfl
theorem chosenValue : (chosen 0).value = 11 := by rfl
theorem steppedValue : (stepped 0).value = 12 := by rfl
theorem boundValue : (bound 0).value = 7 := by rfl
theorem leaveValue : (leaveWith 0).value = 100 := by rfl
theorem skipValue : (skipWith 0).value = 102 := by rfl
theorem bothValue : (bothJump 0).value = 1001 := by rfl
theorem mixedValue : (mixed 0).value = 11 := by rfl
theorem typedValue : (typedLoop 0).value = 3 := by rfl
theorem lastState : (lastLoop 0).state = 103 := by rfl
"
        ),
    );
}

/// Each wrong value is the one a stale read would give: a branch's reassignment lost at its
/// join, a loop that forgets its state, a `break` or `continue` that drops the reassignment
/// before it.
#[test]
fn stale_values_are_refused() {
    let base = state_engine();
    for theorem in [
        "theorem w : branch true = 2 := by rfl",
        "theorem w : (total 0).value = 0 := by rfl",
        "theorem w : (pair 0).value = 10 := by rfl",
        "theorem w : (stopped 0).value = 101 := by rfl",
        "theorem w : (skipped 0).value = 22 := by rfl",
        "theorem w : (effects 0).state = 102 := by rfl",
        "theorem w : (counted 0).value = 0 := by rfl",
        "theorem w : (chosen 0).value = 0 := by rfl",
        "theorem w : (stepped 0).value = 2 := by rfl",
        "theorem w : (bound 0).value = 0 := by rfl",
        "theorem w : (leaveWith 0).value = 0 := by rfl",
        "theorem w : (skipWith 0).value = 2 := by rfl",
        "theorem w : (bothJump 0).value = 1 := by rfl",
        "theorem w : (mixed 0).value = 10 := by rfl",
        "theorem w : (mixed 0).value = 1 := by rfl",
        "theorem w : (typedLoop 0).value = 0 := by rfl",
        "theorem w : (lastLoop 0).state = 102 := by rfl",
    ] {
        let source = format!("{PROGRAMS}{theorem}\n");
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{theorem}"
        );
    }
}

/// The pin's own refusals: a variable not declared `mut` cannot be reassigned (also in a branch
/// that leaves its loop), a `mut` variable cannot be shadowed (by `let` or a loop binder), and a
/// reassignment keeps the variable's type.
#[test]
fn reassigning_an_immutable_and_shadowing_a_mutable_are_refused() {
    let base = state_engine();
    for source in [
        "def bad : Id Nat := do\n  let x := 1\n  x := 2\n  return x\n",
        "def bad : State Nat := do\n  let mut s := 0\n  for (x : Bool) in items do\n    s := s + 1\n  return s\n",
        "def bad : State Nat := do\n  let mut s := 0\n  for x in items do\n    s := s + x\n",
        "def bad : State Nat := do\n  let s := 0\n  for x in items do\n    if x = 1 then\n      s := s + 100\n      break\n  return s\n",
        "def bad : Id Nat := do\n  let mut x := 1\n  let x := 2\n  return x\n",
        "def bad : State Nat := do\n  let mut x := 0\n  for x in items do\n    mark x\n  return x\n",
        "def bad : Id Nat := do\n  let mut x := 1\n  x := true\n  return x\n",
        "def bad : Id Nat := do\n  let mut x := 1\n  let f : Nat -> Id Nat := fun y => do\n    x := y\n    return x\n  return x\n",
    ] {
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
    }
}
