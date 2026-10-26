prelude
import Init.Data.Array.Basic
import Init.Data.List.Control

-- FLN_EXPECT_STRING A
#eval String.push "" (Char.ofNat 65)
-- FLN_EXPECT_STRING λ
#eval String.push "" (Char.ofNat 955)
-- FLN_EXPECT_STRING 😀
#eval String.push "" (Char.ofNat 128512)
def makeCharacter : Nat → Char := Char.ofNat
def useCharacter (f : Nat → Char) (n : Nat) : String := String.push "" (f n)
-- FLN_EXPECT_STRING Ω
#eval useCharacter makeCharacter 937
-- FLN_EXPECT_STRING λ
#eval String.push "" (Char.ofNatAux 955 (by decide))
-- FLN_EXPECT_NAT 1
#eval (String.push "" (Char.ofNat 0)).utf8ByteSize
-- FLN_EXPECT_NAT 3
#eval (String.push "" (Char.ofNat 55295)).utf8ByteSize
-- FLN_EXPECT_NAT 3
#eval (String.push "" (Char.ofNat 57344)).utf8ByteSize
-- FLN_EXPECT_NAT 4
#eval (String.push "" (Char.ofNat 1114111)).utf8ByteSize
-- FLN_EXPECT_NAT 1
#eval (String.push "" (Char.ofNat 55296)).utf8ByteSize
-- FLN_EXPECT_NAT 1
#eval (String.push "" (Char.ofNat 1114112)).utf8ByteSize
-- FLN_EXPECT_NAT 1
#eval (String.push "" (Char.ofNat 18446744073709551616)).utf8ByteSize
