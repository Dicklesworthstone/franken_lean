prelude
import Init.Data.Array.Basic
import Init.Data.List.Control
import Init.Data.String.Defs

def dynamicNatArray (first step : Nat) : Array Nat :=
  List.toArray [first, first + step, first + step + step]

def dynamicStringArray (first second : String) : Array String :=
  List.toArray [first, second]

def arrayDigits (xs : Array Nat) (initial : Nat) : Id Nat :=
  Array.forIn' (m := Id) xs initial
    (fun x _ acc => Pure.pure (ForInStep.yield (acc * 10 + x)))

def arraySum (xs : Array Nat) (initial : Nat) : Id Nat := do
  let mut total := initial
  for x in xs do
    total := total + x
  return total

def arrayStatistics (xs : Array Nat) (initial : Nat) : Id Nat := do
  let mut total := initial
  let mut count := 0
  for x in xs do
    total := total + x
    count := count + 1
  return total * 100 + count

def arraySkipBreak (xs : Array Nat) (skip stop initial : Nat) : Id Nat := do
  let mut result := initial
  for x in xs do
    if x == skip then continue
    result := result * 10 + x
    if x == stop then break
    result := result * 10 + 9
  return result

def arrayEarlyReturn (xs : Array Nat) (stop fallback : Nat) : Id Nat := do
  let mut result := 0
  for x in xs do
    result := result * 10 + x
    if x == stop then return result
    result := result * 10 + 9
  return fallback

def arrayWitnessValue (xs : Array Nat) (x : Nat) (_h : Array.Mem xs x) : Id Nat :=
  Pure.pure x

def arrayMembershipSum (xs : Array Nat) : Id Nat := do
  let mut result := 0
  for h : x in xs do
    let value <- arrayWitnessValue xs x h
    result := result + value
  return result

structure ArrayWitness (xs : Array Nat) where
  value : Nat
  evidence : Array.Mem xs value

def arrayFirstWitness (xs : Array Nat) : Id (Option (ArrayWitness xs)) := do
  for h : x in xs do
    return Option.some { value := x, evidence := h }
  return Option.none

def arrayWitnessOr (xs : Array Nat) (fallback : Nat) : Nat :=
  match arrayFirstWitness xs with
  | Option.none => fallback
  | Option.some found => found.value

def applyArrayLoop
    (loop : (xs : Array Nat) -> Nat ->
      ((x : Nat) -> Array.Mem xs x -> Nat -> Id (ForInStep Nat)) -> Id Nat)
    (xs : Array Nat) (initial captured : Nat) : Id Nat :=
  loop xs initial (fun x _ acc => Pure.pure (ForInStep.yield (acc + x + captured)))

def partialArrayLoop (xs : Array Nat) (initial : Nat) :
    ((x : Nat) -> Array.Mem xs x -> Nat -> Id (ForInStep Nat)) -> Id Nat :=
  Array.forIn' (m := Id) xs initial

structure ArrayTotals where
  sum : Nat
  count : Nat

def arrayRecordFold (xs : Array Nat) : Id ArrayTotals :=
  Array.forIn' (m := Id) xs { sum := 0, count := 0 }
    (fun x _ acc => Pure.pure (ForInStep.yield
      { sum := acc.sum + x, count := acc.count + 1 }))

def arrayRecordCode (xs : Array Nat) : Nat :=
  let result := arrayRecordFold xs
  result.sum * 100 + result.count

def arrayFunctionFold (xs : Array Nat) (offset : Nat) : Nat -> Nat :=
  Array.forIn' (m := Id) xs (fun n => n + offset)
    (fun x _ previous => Pure.pure (ForInStep.yield (fun n => previous n + x)))

def arrayLastString (xs : Array String) (fallback : String) : Id String :=
  Array.forIn' (m := Id) xs fallback
    (fun value _ _ => Pure.pure (ForInStep.yield value))

def arrayCapturedStrings (xs : Array String) (capturedText : String) : Id String :=
  Array.forIn' (m := Id) xs ""
    (fun value _ acc => Pure.pure
      (ForInStep.yield (String.append (String.append acc capturedText) value)))

def arrayStringReuse (xs : Array String) (capturedText : String) : String :=
  let first := arrayCapturedStrings xs capturedText
  let last := arrayLastString xs first
  String.append first (String.append "|" last)

def arrayStringStage (xs : Array String) (capturedText : String) : String -> String :=
  fun suffix => String.append (arrayCapturedStrings xs capturedText) suffix

def arrayStringStages (xs : Array String) (capturedText : String) : String :=
  let stage := arrayStringStage xs capturedText
  let first := stage "!"
  String.append first (stage "?")

-- FLN_EXPECT_NAT 4123
#eval arrayDigits (dynamicNatArray 1 1) 4
-- FLN_EXPECT_NAT 7
#eval arrayDigits (List.toArray []) 7
-- FLN_EXPECT_NAT 42
#eval arraySum (dynamicNatArray 1 1) 36
-- FLN_EXPECT_NAT 1603
#eval arrayStatistics (dynamicNatArray 1 1) 10
-- FLN_EXPECT_NAT 1000
#eval arrayStatistics (List.toArray []) 10
-- FLN_EXPECT_NAT 193
#eval arraySkipBreak (List.toArray [1, 2, 3, 4]) 2 3 0
-- FLN_EXPECT_NAT 8
#eval arraySkipBreak (List.toArray []) 2 3 8
-- FLN_EXPECT_NAT 192
#eval arrayEarlyReturn (dynamicNatArray 1 1) 2 77
-- FLN_EXPECT_NAT 77
#eval arrayEarlyReturn (dynamicNatArray 1 1) 9 77
-- FLN_EXPECT_NAT 77
#eval arrayEarlyReturn (List.toArray []) 1 77
-- FLN_EXPECT_NAT 42
#eval arrayMembershipSum (List.toArray [20, 22])
-- FLN_EXPECT_NAT 41
#eval arrayWitnessOr (dynamicNatArray 41 2) 9
-- FLN_EXPECT_NAT 9
#eval arrayWitnessOr (List.toArray []) 9
-- FLN_EXPECT_NAT 22
#eval applyArrayLoop (@Array.forIn' Nat Nat Id inferInstance) (dynamicNatArray 1 1) 10 2
-- FLN_EXPECT_NAT 11
#eval partialArrayLoop (dynamicNatArray 1 1) 5 (fun x _ acc => Pure.pure (ForInStep.yield (acc + x)))
-- FLN_EXPECT_NAT 603
#eval arrayRecordCode (dynamicNatArray 1 1)
-- FLN_EXPECT_NAT 42
#eval arrayFunctionFold (dynamicNatArray 1 1) 30 6
-- FLN_EXPECT_NAT 18446744073709551658
#eval arraySum (List.toArray [18446744073709551616, 26]) 16
-- FLN_EXPECT_STRING β
#eval arrayLastString (dynamicStringArray "alpha" "β") "empty"
-- FLN_EXPECT_STRING empty
#eval arrayLastString (List.toArray []) "empty"
-- FLN_EXPECT_STRING !a!b
#eval arrayCapturedStrings (dynamicStringArray "a" "b") "!"
-- FLN_EXPECT_STRING !a!b|b
#eval arrayStringReuse (dynamicStringArray "a" "b") "!"
-- FLN_EXPECT_STRING :a:b!:a:b?
#eval arrayStringStages (dynamicStringArray "a" "b") ":"
