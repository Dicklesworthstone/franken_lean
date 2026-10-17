universe u v
def wrapped (A : Sort u) (x : A) : A := x
theorem dependent (A : Sort u) (B : A → Sort v)
    (P : (a : A) → B a → Prop) (ready : ∀ a b, P a b) :
    ∀ a b, P a (wrapped (B a) b) := by
  dsimp only [wrapped]
  guard_target =ₛ ∀ a b, P a b
  exact ready
