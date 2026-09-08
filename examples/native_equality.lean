-- Run with: fln check-source --json native_equality.lean
-- These are source proofs, not executable proof stubs.
def identity (x : Nat) : Nat := x

theorem identity_self (x : Nat) : identity x = x := by rfl

theorem equality_symmetry (x y : Nat) (h : x = y) : y = x := by
  rw [h]

theorem equality_congruence (f : Nat -> Nat) (x y : Nat) (h : x = y) : f x = f y := by
  rw [h]

theorem equality_transitivity (x y z : Nat) (h : x = y) (k : y = z) : x = z := by
  rw [h, k]

theorem predicate_transport (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by
  rw [← h]
  exact hx
