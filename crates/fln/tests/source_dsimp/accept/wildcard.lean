def IdP (P : Prop) : Prop := P
theorem independent (P : Prop) (h : IdP P) : P := by
  dsimp only [IdP] at *
  guard_hyp h :ₛ P
  exact h
theorem dependent (P : Prop) (h : IdP P) (F : IdP P → Type) (w : F h)
    (ready : P) : P := by
  fail_if_success dsimp only [IdP] at *
  guard_hyp h :ₛ IdP P
  exact ready
