def wrapped (A : Type) (x : A) : A := x
theorem partialCall (A : Type) (P : (A → A) → Prop) (ready : P (wrapped A)) : P (wrapped A) := by
  fail_if_success dsimp only [wrapped]
  guard_target =ₛ P (wrapped A)
  exact ready
