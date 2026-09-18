theorem revertDependent (A : Type) (x : A) (P : A -> Prop) (p : P x) : P x := by
  revert A
  intro B y Q q
  exact q

theorem revertIntroduced : forall (A : Type) (x : A), x = x := by
  intro A x
  revert A
  intro B y
  rfl

theorem revertLocalDefinition (x : Nat) : x = x := by
  let y : Nat := x
  have h : y = x := by rfl
  revert x
  intro n z hz
  exact hz

theorem revertBacktrack (P : Prop) (p : P) : P := by
  first | (revert p; fail) | exact p

theorem generalizeThenRevert : 3 = 3 := by
  generalize 3 = x
  revert x
  intro y
  rfl

theorem generalizeKeepEquation (P : Nat -> Prop) (n : Nat) (p : P n) : P n := by
  generalize h : n = m
  rw [<- h]
  exact p

theorem generalizeUnderBinder (x : Nat) : forall (y : Nat), x = x := by
  generalize x = y
  intro z
  rfl

theorem generalizeDependentFallback (F : Nat -> Type) (n : Nat) (x : F n) : x = x := by
  first | generalize n = m | skip
  rfl