def IdP (P : Prop) : Prop := P
theorem named (P : Prop) (h : IdP P) : IdP P := by
  dsimp only [IdP] at h ⊢
  guard_hyp h :ₛ P
  guard_target =ₛ P
  exact h
