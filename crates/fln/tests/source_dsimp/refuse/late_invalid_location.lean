def IdP (P : Prop) : Prop := P
theorem bad (P : Prop) (h : IdP P) : P := by
  dsimp only [IdP] at h missing
  exact h
