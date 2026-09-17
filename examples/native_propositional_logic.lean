-- Constructive propositions; no imports, classical axioms, or external solver.
theorem arithmetic : 2 + 3 = 5 ∧ ¬3 = 4 := by decide
theorem disjunction : 1 = 2 ∨ 3 = 3 := by decide
theorem equivalent : (2 = 2) ↔ ¬(3 = 4) := by decide
theorem implication : (2 = 3) -> (3 = 4) := by decide

-- The same declarations work with ordinary proof terms and native tactics.
theorem conjunction (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  assumption
  assumption
theorem first (p q : Prop) (h : p ∧ q) : p := h.left
theorem exchange (p q : Prop) (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)
theorem reflexive (p : Prop) : p ↔ p :=
  Iff.intro (fun h => h) (fun h => h)

-- Branch selection retains proof-carrying dictionaries.
def select (x y : Nat) : Nat := if x = y ∧ ¬x = 0 then 17 else 23
theorem selected : select 4 4 = 17 := by rfl
theorem rejected : select 0 0 = 23 := by rfl
