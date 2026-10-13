def wrap (P : Prop) : Prop := P
@[simp] theorem unwrap (P : Prop) : wrap P ↔ P := by
  constructor
  · intro h; exact h
  · intro h; exact h

theorem registered (P : Prop) (h : wrap (wrap P)) : P := by
  simpa using h

theorem bothSides (P : Nat -> Prop) (f g : Nat -> Nat) (x : Nat)
    (hf : f x = x) (hg : g x = x) (p : P (f x)) : P (g x) := by
  simpa only [hf, hg] using p

-- Bare `simpa` simplifies the goal and closes with plain `assumption`
-- against the unsimplified hypotheses, so the context evidence must already
-- have the simplified shape; `bothSides` above is the form that simplifies
-- its evidence too.
theorem fromContext (P : Nat -> Prop) (f g : Nat -> Nat) (x : Nat)
    (hf : f x = x) (hg : g x = x) (p : P x) : P (g x) := by
  simpa only [hg]

theorem wildcard (P : Nat -> Prop) (f g : Nat -> Nat) (x : Nat)
    (hf : f x = x) (hg : g x = x) (p : P (f x)) : P (g x) := by
  simpa only [*] using p

theorem self (x : Nat) : x = x := by simpa only []
