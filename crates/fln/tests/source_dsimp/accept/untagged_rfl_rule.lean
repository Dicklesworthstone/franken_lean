@[implicit_reducible] def wrapped (A : Type) (x : A) : A := x
theorem parenthesized (A : Type) (x : A) : wrapped A x = x := (rfl)
theorem tacticProof (A : Type) (x : A) : wrapped A x = x := by rfl
theorem untagged (A : Type) (x : A) (P : A → Prop) (ready : P x) : P (wrapped A x) := by
  fail_if_success dsimp only [parenthesized, tacticProof]
  guard_target =ₛ P (wrapped A x)
  dsimp only [wrapped]
  guard_target =ₛ P x
  exact ready
