structure Pair where
  first : Nat
  second : Nat
theorem projection (x y : Nat) (P : Nat → Prop) (ready : P x) : P (Pair.first (Pair.mk x y)) := by
  dsimp only
  guard_target =ₛ P x
  exact ready
theorem recordEta (r : Pair) (P : Pair → Prop) (ready : P r) : P (Pair.mk r.first r.second) := by
  fail_if_success dsimp only
  guard_target =ₛ P (Pair.mk r.first r.second)
  exact ready
-- The same eta equality still closes by conversion, in both orientations.
theorem recordEtaEquality (r : Pair) : Pair.mk r.first r.second = r := by dsimp only
theorem recordEtaEqualityReverse (r : Pair) : r = Pair.mk r.first r.second := by dsimp only
