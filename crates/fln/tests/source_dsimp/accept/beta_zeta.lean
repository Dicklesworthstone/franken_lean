theorem betaZeta (A : Type) (x : A) (P : A → Prop) (ready : P x) :
    P ((fun y : A => let z : A := y; z) x) := by
  dsimp only
  guard_target =ₛ P x
  exact ready
