theorem true_proof : True := by decide
theorem not_false : Not False := by decide
theorem double_negation : Not (Not True) := by decide

inductive Holds : Prop where
  | proof

instance holdsDecision : Decidable Holds := Decidable.isTrue Holds.proof
theorem registered : Holds := by decide

theorem supplied (p : Prop) [Decidable p] (computed : decide p = true) : p :=
  of_decide_eq_true computed

theorem available (p : Prop) (hp : p) : p := by
  let witness : Decidable p := Decidable.isTrue hp
  decide

theorem generated : True := by
  have h : Not False := by decide
  exact True.intro

inductive Both (P Q : Prop) : Prop where
  | intro (left : P) (right : Q)

theorem parallel : Both True (Not False) := by
  constructor <;> decide

theorem fallback (p : Prop) [Decidable p] (h : p) : p := by
  first | decide | exact h