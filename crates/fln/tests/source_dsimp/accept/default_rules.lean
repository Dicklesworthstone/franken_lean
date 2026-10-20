@[implicit_reducible] def wrapped (A : Type) (x : A) : A := x
@[simp] theorem unwrap (A : Type) (x : A) : wrapped A x = x := rfl
theorem defaults (A : Type) (x : A) (P : A → Prop) (ready : P x) : P (wrapped A x) := by
  fail_if_success dsimp only
  guard_target =ₛ P (wrapped A x)
  dsimp
  guard_target =ₛ P x
  exact ready
