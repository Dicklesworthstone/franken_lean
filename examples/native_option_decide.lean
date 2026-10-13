-- The candidate is admitted by the native source seed. Register its ordinary
-- instance metadata explicitly; no kernel axiom or trusted host comparison.
attribute [instance] Option.instDecidableEq

theorem option_same : (Option.some 0 : Option Nat) = Option.some 0 := by decide
theorem option_different : Not ((Option.some 0 : Option Nat) = Option.some 1) := by decide
theorem option_empty_left : Not ((Option.none : Option Nat) = Option.some 0) := by decide
theorem option_empty_right : Not ((Option.some 0 : Option Nat) = Option.none) := by decide
theorem option_empty_same : (Option.none : Option Nat) = Option.none := by decide

theorem option_nested_same : Option.some (Option.none : Option Bool) = Option.some (Option.none : Option Bool) := by decide
theorem option_nested_different : Not (Option.some (Option.none : Option Bool) = Option.some (Option.some Bool.false)) := by decide

-- Generic decisions use the caller's element dictionary, including above Type 0.
def option_lifted {A : Type 1} [DecidableEq A] (x y : Option A) : Decidable (x = y) := decEq x y
