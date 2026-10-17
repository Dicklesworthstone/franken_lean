theorem localEquality (A : Type) (x y : A) (h : x = y) (P : A → Prop)
    (ready : P x) : P x := by
  fail_if_success dsimp only [h]
  guard_target =ₛ P x
  exact ready
