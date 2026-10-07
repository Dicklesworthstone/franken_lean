theorem contraction (f : Nat -> Nat) (x : Nat) (h : f x = x) : f (f x) = x := by
  simp only [*]

theorem conditional (f : Nat -> Nat) (P : Nat -> Prop) (x : Nat)
    (h : ∀ n : Nat, P n -> f n = n) (p : P x) : f x = x := by
  simp only [*]

theorem equivalence (P Q : Prop) (h : P ↔ Q) (q : Q) : P := by
  simp only [*]

-- The pin's simp set is built once: after `hx` is rewritten to `P y`, its
-- rule no longer fires, so the goal is not closed by the tactic and the
-- rewritten hypothesis closes it explicitly.
theorem transport (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by
  simp only [*] at hx ⊢
  exact hx

theorem shadow (P Q : Prop) (h : P) : Q -> P := by
  intro h
  simp only [*]
