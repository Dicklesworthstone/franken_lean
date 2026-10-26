prelude
import Init.Data.Array.Basic
import Init.Data.List.Control

def localLength (xs : Array Nat) : Nat := xs.size
def genericLength {α : Type} (xs : Array α) : Nat := Array.size xs
def savedLength : Array Nat → Nat := @Array.size Nat

-- FLN_EXPECT_NAT 0
#eval localLength #[]
-- FLN_EXPECT_NAT 3
#eval localLength #[4, 5, 6]
-- FLN_EXPECT_NAT 2
#eval genericLength #[true, false]
-- FLN_EXPECT_NAT 4
#eval genericLength #["ab", "cd", "ef", "gh"]
-- FLN_EXPECT_NAT 1
#eval savedLength #[18]
-- FLN_EXPECT_NAT 5
#eval let length := @Array.size Nat; length #[1, 2, 3, 4, 5]
-- FLN_EXPECT_NAT 3
#eval let length := fun xs : Array Bool => xs.size; length #[true, false, true]
-- FLN_EXPECT_NAT 2
#eval Array.size #[18446744073709551616, 0]
