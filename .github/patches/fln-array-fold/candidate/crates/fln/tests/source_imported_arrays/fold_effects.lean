prelude
import Init.Data.Array.Basic
import Init.Data.List.Control
import Init.Data.String.Defs

structure FoldTraceResult (A : Type) where
  value : Option A
  trace : Nat

def FoldTrace (A : Type) : Type := Nat -> FoldTraceResult A

def foldTracePure {A : Type} (value : A) : FoldTrace A :=
  fun state => { value := Option.some value, trace := state * 10 + 8 }

def foldTraceBind {A B : Type}
    (action : FoldTrace A) (next : A -> FoldTrace B) : FoldTrace B :=
  fun state =>
    let result := action (state * 10 + 7)
    match result.value with
    | Option.none => { value := Option.none, trace := result.trace }
    | Option.some value => next value result.trace

-- Intentionally no LawfulMonad: 7 records each bind and 8 each pure.
-- Callback digits record exact left-to-right selection and short-circuiting.
instance foldTraceMonad : Monad FoldTrace :=
  { pure := fun value => foldTracePure value,
    bind := fun action next => foldTraceBind action next }

def foldTraceStep (abort acc x : Nat) : FoldTrace Nat :=
  fun state =>
    { value := if x == abort then Option.none else Option.some (acc * 10 + x),
      trace := state * 10 + x }

def tracedArrayFold (xs : Array Nat) (start stop abort initial : Nat) : FoldTrace Nat :=
  Array.foldlM (m := FoldTrace) (fun acc x => foldTraceStep abort acc x)
    initial xs start stop

def foldTraceValue (result : FoldTraceResult Nat) (fallback : Nat) : Nat :=
  match result.value with
  | Option.none => fallback
  | Option.some value => value

def foldTraceMark (abort x : Nat) : FoldTrace PUnit :=
  fun state =>
    { value := if x == abort then Option.none else Option.some PUnit.unit,
      trace := state * 10 + x }

def tracedArrayForM (xs : Array Nat) (start stop abort : Nat) : FoldTrace PUnit :=
  Array.forM (m := FoldTrace) (fun x => foldTraceMark abort x) xs start stop

def defaultArrayForM (xs : Array Nat) (abort : Nat) : FoldTrace PUnit :=
  Array.forM (m := FoldTrace) (fun x => foldTraceMark abort x) xs

def foldTraceUnitStatus (result : FoldTraceResult PUnit) : Nat :=
  match result.value with
  | Option.none => 0
  | Option.some _ => 1

-- Three callbacks require exactly three binds and one final pure.
-- FLN_EXPECT_NAT 4123
#eval foldTraceValue (tracedArrayFold (List.toArray [1, 2, 3]) 0 3 9 4 0) 999
-- FLN_EXPECT_NAT 7172738
#eval (tracedArrayFold (List.toArray [1, 2, 3]) 0 3 9 4 0).trace
-- FLN_EXPECT_NAT 423
#eval foldTraceValue (tracedArrayFold (List.toArray [1, 2, 3]) 1 99 9 4 0) 999
-- FLN_EXPECT_NAT 72738
#eval (tracedArrayFold (List.toArray [1, 2, 3]) 1 99 9 4 0).trace
-- Aborting at the second callback must omit both the third callback and
-- the terminal pure, not merely discard their eventual return value.
-- FLN_EXPECT_NAT 999
#eval foldTraceValue (tracedArrayFold (List.toArray [1, 2, 3]) 0 3 2 4 0) 999
-- FLN_EXPECT_NAT 7172
#eval (tracedArrayFold (List.toArray [1, 2, 3]) 0 3 2 4 0).trace
-- Empty and inverted intervals perform only one pure and preserve the seed.
-- FLN_EXPECT_NAT 4
#eval foldTraceValue (tracedArrayFold (List.toArray []) 0 99 9 4 0) 999
-- FLN_EXPECT_NAT 8
#eval (tracedArrayFold (List.toArray []) 0 99 9 4 0).trace
-- FLN_EXPECT_NAT 8
#eval (tracedArrayFold (List.toArray [1, 2, 3]) 3 1 9 4 0).trace
-- Array.forM is an actual imported foldlM wrapper, with a PUnit accumulator.
-- FLN_EXPECT_NAT 7172738
#eval (defaultArrayForM (List.toArray [1, 2, 3]) 9 0).trace
-- FLN_EXPECT_NAT 72738
#eval (tracedArrayForM (List.toArray [1, 2, 3]) 1 99 9 0).trace
-- FLN_EXPECT_NAT 7172
#eval (defaultArrayForM (List.toArray [1, 2, 3]) 2 0).trace
-- FLN_EXPECT_NAT 0
#eval foldTraceUnitStatus (defaultArrayForM (List.toArray [1, 2, 3]) 2 0)
-- FLN_EXPECT_NAT 1
#eval foldTraceUnitStatus (defaultArrayForM (List.toArray [1, 2, 3]) 9 0)
