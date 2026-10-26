prelude
import Init.Data.Array.Basic
import Init.Data.List.Control

def indexedNat (xs : Array Nat) (i : Nat) (h : i < xs.size) : Nat := Array.getInternal xs i h
def indexed {α : Type} (xs : Array α) (i : Nat) (h : i < xs.size) : α := Array.getInternal xs i h
def savedGet : (xs : Array Nat) → (i : Nat) → i < xs.size → Nat := @Array.getInternal Nat
def guardedGet (xs : Array Nat) (i : Nat) : Nat :=
  if h : i < xs.size then Array.getInternal xs i h else 99

-- FLN_EXPECT_NAT 4
#eval indexedNat #[4, 5, 6] 0 (by decide)
-- FLN_EXPECT_NAT 6
#eval indexedNat #[4, 5, 6] 2 (by decide)
-- FLN_EXPECT_NAT 7
#eval if indexed #[true, false] 0 (by decide) then 7 else 9
-- FLN_EXPECT_NAT 9
#eval if indexed #[true, false] 1 (by decide) then 7 else 9
-- FLN_EXPECT_STRING cd
#eval indexed #["ab", "cd"] 1 (by decide)
-- FLN_EXPECT_NAT 18
#eval savedGet #[18] 0 (by decide)
-- FLN_EXPECT_NAT 2
#eval let access := @Array.getInternal Nat #[1, 2, 3]; access 1 (by decide)
-- FLN_EXPECT_NAT 18446744073709551616
#eval indexedNat #[18446744073709551616, 0] 0 (by decide)
-- FLN_EXPECT_NAT 5
#eval guardedGet #[4, 5] 1
-- FLN_EXPECT_NAT 99
#eval guardedGet #[] 0
-- FLN_EXPECT_NAT 99
#eval guardedGet #[4, 5] 2
-- FLN_EXPECT_NAT 99
#eval guardedGet #[4, 5] 18446744073709551616
