def wrap (A : Type) (x : A) : A := x
theorem repeatStops (A : Type) (x : A) (P : A → Prop) (ready : P x) : P (wrap A x) := by
  repeat dsimp only [wrap]
  guard_target =ₛ P x
  fail_if_success dsimp only [wrap]
  exact ready
