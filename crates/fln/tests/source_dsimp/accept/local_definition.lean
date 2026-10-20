theorem localValue (A : Type) (x : A) (P : A → Prop) (ready : P x) : P x := by
  let y : A := x
  change P y
  dsimp only [y]
  guard_target =ₛ P x
  exact ready
