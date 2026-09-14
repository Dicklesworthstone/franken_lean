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

def packed : Package := by
  refine Package.mk ?carrier ?value
  first
  | (exact Nat; fail)
  | exact String
  exact "preserved"

theorem packed_ok : packed.value = "preserved" := by rfl

def chosen : Nat := by
  first | (exact 7; fail) | exact 9

theorem chosen_ok : chosen = 9 := by rfl

theorem inner : 0 = 0 := by
  first
  | have local : 0 = 0 := by
      first | fail | rfl
    exact local
  | fail

theorem scoped (P Q : Prop) (p : P) (q : Q) : Both P Q := by
  constructor
  · first | exact q | exact p
  · try exact p
    exact q
