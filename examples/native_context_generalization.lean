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