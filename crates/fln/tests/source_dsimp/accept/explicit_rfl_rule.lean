@[implicit_reducible] def wrapped (A : Type) (x : A) : A := x
theorem unwrap (A : Type) (x : A) : wrapped A x = x := rfl
theorem explicitRule (A : Type) (x : A) (P : A → Prop) (ready : P x) : P (wrapped A x) := by
  dsimp only [unwrap]
  guard_target =ₛ P x
  exact ready
