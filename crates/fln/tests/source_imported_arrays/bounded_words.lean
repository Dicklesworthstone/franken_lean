prelude
import Init.Data.Array.Basic
import Init.Data.List.Control

def boundedCopy (x : USize) : USize :=
  USize.ofNatLT (USize.toNat x) (Fin.isLt (BitVec.toFin (USize.toBitVec x)))
def boundedAlias : (n : Nat) → n < USize.size → USize := USize.ofNatLT
def boundedZero : 0 < USize.size → USize := USize.ofNatLT 0
def useBounded (f : (n : Nat) → n < USize.size → USize) : Nat :=
  USize.toNat (f 0 USize.size_pos)
-- FLN_EXPECT_NAT 0
#eval USize.toNat (USize.ofNatLT 0 USize.size_pos)
-- FLN_EXPECT_NAT 42
#eval USize.toNat (boundedCopy (USize.ofNat 42))
-- FLN_EXPECT_NAT 18446744073709551615
#eval USize.toNat (boundedCopy (USize.ofNat 18446744073709551615))
-- FLN_EXPECT_NAT 0
#eval USize.toNat (boundedCopy (USize.ofNat 18446744073709551616))
-- FLN_EXPECT_NAT 5
#eval USize.toNat (boundedCopy (USize.ofNat 18446744073709551621))
-- FLN_EXPECT_NAT 0
#eval USize.toNat (boundedAlias 0 USize.size_pos)
-- FLN_EXPECT_NAT 0
#eval USize.toNat (boundedZero USize.size_pos)
-- FLN_EXPECT_NAT 0
#eval useBounded USize.ofNatLT
