def Carrier : Type := Nat
theorem dataType (x : Carrier) (P : Prop) (ready : P) : P := by
  dsimp only [Carrier] at x
  guard_hyp x :ₛ Nat
  exact ready
