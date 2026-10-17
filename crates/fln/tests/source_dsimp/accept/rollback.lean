def IdP (P : Prop) : Prop := P
theorem rollback (P : Prop) (h : IdP P) : P := by
  first
  | dsimp only [IdP] at h; fail
  | skip
  guard_hyp h :ₛ IdP P
  dsimp only [IdP] at h
  guard_hyp h :ₛ P
  exact h
