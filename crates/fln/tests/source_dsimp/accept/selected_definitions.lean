def wrapped (A : Type) (x : A) : A := x
def twice (A : Type) (x : A) : A := wrapped A (wrapped A x)
theorem selected (A : Type) (x : A) (P : A → Prop) (ready : P x) : P (twice A x) := by
  dsimp only [twice, wrapped]
  guard_target =ₛ P x
  exact ready
