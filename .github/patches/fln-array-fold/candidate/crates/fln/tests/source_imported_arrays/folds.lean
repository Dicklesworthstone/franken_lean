prelude
import Init.Data.Array.Basic
import Init.Data.List.Control
import Init.Data.String.Defs

def foldInput (first step : Nat) : Array Nat :=
  List.toArray [first, first + step, first + step + step, first + step + step + step]

def boundedArrayDigits (xs : Array Nat) (initial start stop : Nat) : Id Nat :=
  Array.foldlM (m := Id) (fun acc x => Pure.pure (acc * 10 + x))
    initial xs start stop

def defaultArrayDigits (xs : Array Nat) (initial : Nat) : Id Nat :=
  Array.foldlM (m := Id) (fun acc x => Pure.pure (acc * 10 + x)) initial xs

def pureArrayDigits (xs : Array Nat) (initial : Nat) : Nat :=
  Array.foldl (fun acc x => acc * 10 + x) initial xs

def applyArrayFold
    (fold : (Nat -> Nat -> Id Nat) -> Nat -> Array Nat -> Nat -> Nat -> Id Nat)
    (xs : Array Nat) (initial : Nat) : Id Nat :=
  fold (fun acc x => Pure.pure (acc * 10 + x)) initial xs 1 (Array.size xs)

def foldLetter (x : Nat) : String :=
  if x == 1 then "a" else if x == 2 then "b" else if x == 3 then "c" else "d"

-- The returned partial fold owns both String captures. Its accumulator and
-- element types deliberately differ.
def capturedArrayFold (left right : String) :
    String -> Array Nat -> Nat -> Nat -> Id String :=
  @Array.foldlM Nat String Id (inferInstance : Monad Id)
    (fun acc x => Pure.pure
      (String.append (String.append acc left) (String.append (foldLetter x) right)))

def useCapturedArrayFold
    (fold : String -> Array Nat -> Nat -> Nat -> Id String) (xs : Array Nat) : String :=
  fold "!" xs 1 99

def ownedArrayFold (xs : Array String) (initial : String) : String :=
  Array.foldl (fun acc x => String.append (String.append acc "|") x) initial xs

-- Dynamic array arguments exercise omitted stop := Array.size as well as
-- explicit half-open bounds, without replacing the imported Array functions.
-- FLN_EXPECT_NAT 41234
#eval defaultArrayDigits (foldInput 1 1) 4
-- FLN_EXPECT_NAT 923
#eval boundedArrayDigits (foldInput 1 1) 9 1 3
-- FLN_EXPECT_NAT 234
#eval boundedArrayDigits (foldInput 1 1) 0 1 99
-- FLN_EXPECT_NAT 17
#eval boundedArrayDigits (foldInput 1 1) 17 3 1
-- FLN_EXPECT_NAT 17
#eval boundedArrayDigits (foldInput 1 1) 17 2 2
-- FLN_EXPECT_NAT 17
#eval boundedArrayDigits (foldInput 1 1) 17 8 99
-- FLN_EXPECT_NAT 17
#eval defaultArrayDigits (List.toArray []) 17
-- Bounds remain arbitrary Nat values; neither may be truncated to USize.
-- FLN_EXPECT_NAT 1234
#eval boundedArrayDigits (foldInput 1 1) 0 0 18446744073709551616
-- FLN_EXPECT_NAT 17
#eval boundedArrayDigits (foldInput 1 1) 17 18446744073709551616 18446744073709551619
-- FLN_EXPECT_NAT 2468
#eval pureArrayDigits (foldInput 2 2) 0
-- FLN_EXPECT_NAT 5234
#eval applyArrayFold (@Array.foldlM Nat Nat Id (inferInstance : Monad Id)) (foldInput 1 1) 5
-- FLN_EXPECT_STRING !<b><c><d>
#eval useCapturedArrayFold (capturedArrayFold "<" ">") (foldInput 1 1)
-- FLN_EXPECT_STRING S|red|green
#eval ownedArrayFold (List.toArray ["red", "green"]) "S"
