-- Semantic rollback retains spent work and all checked proof obligations.
inductive Both (P Q : Prop) : Prop where
  | intro (left : P) (right : Q)

theorem fallback (n m : Nat) (h : n = m) : n = m := by
  first | rfl | exact h

theorem introduced (P : Prop) : P -> P := by
  try (intro discarded; fail)
  intro kept
  exact kept

theorem paired (P Q : Prop) (p : P) (q : Q) : Both P Q := by
  first
  | constructor <;> exact p
  | constructor <;> assumption

structure Package where
  carrier : Type
  value : carrier

-- The rollback is checked by the value itself: "preserved" has type `String` only if `first`
-- discarded the `Nat` carrier. An `example` is elaborated and never compiled.
example : Package := by
  refine Package.mk ?carrier ?value
  first
  | (exact Nat; fail)
  | exact String
  exact "preserved"

def chosen : Nat := by
  first | (exact 7; fail) | exact 9

theorem chosen_ok : chosen = 9 := by rfl

theorem inner : 0 = 0 := by
  first
  | have h : 0 = 0 := by
      first | fail | rfl
    exact h
  | fail

theorem scoped_goals (P Q : Prop) (p : P) (q : Q) : Both P Q := by
  constructor
  · first | exact q | exact p
  · try exact p
    exact q
