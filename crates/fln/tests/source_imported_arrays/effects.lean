prelude
import Init.Data.Array.Basic
import Init.Data.List.Control
import Init.Data.String.Defs

structure ArrayTraceResult (A : Type) where
  value : A
  trace : Nat

def ArrayTrace (A : Type) : Type := Nat -> ArrayTraceResult A

def arrayTracePure {A : Type} (value : A) : ArrayTrace A :=
  fun state => { value := value, trace := state * 10 + 8 }

def arrayTraceBind {A B : Type}
    (action : ArrayTrace A) (next : A -> ArrayTrace B) : ArrayTrace B :=
  fun state =>
    let result := action (state * 10 + 7)
    next result.value result.trace

instance arrayTraceMonad : Monad ArrayTrace :=
  { pure := fun value => arrayTracePure value,
    bind := fun action next => arrayTraceBind action next }

def arrayTraceStep (xs : Array Nat) (stop x : Nat)
    (_h : Array.Mem xs x) (acc : Nat) : ArrayTrace (ForInStep Nat) :=
  fun state =>
    { value := if x == stop then ForInStep.done (acc * 10 + x)
        else ForInStep.yield (acc * 10 + x),
      trace := state * 10 + x }

def arrayTraced (xs : Array Nat) (stop initial : Nat) : ArrayTrace Nat :=
  Array.forIn' (m := ArrayTrace) xs initial
    (fun x h acc => arrayTraceStep xs stop x h acc)

structure ArrayEventResult (A : Type) where
  value : A
  trace : Nat

def ArrayEvents (A : Type) : Type := Nat -> ArrayEventResult A

def arrayEventPure {A : Type} (value : A) : ArrayEvents A :=
  fun state => { value := value, trace := state }

def arrayEventBind {A B : Type}
    (action : ArrayEvents A) (next : A -> ArrayEvents B) : ArrayEvents B :=
  fun state =>
    let result := action state
    next result.value result.trace

instance arrayEventsMonad : Monad ArrayEvents :=
  { pure := fun value => arrayEventPure value,
    bind := fun action next => arrayEventBind action next }

def arrayEventMark (x : Nat) : ArrayEvents PUnit :=
  fun state => { value := PUnit.unit, trace := state * 100 + x }

def arrayEventReturn (xs : Array Nat) (stop : Nat) : ArrayEvents Nat := do
  for x in xs do
    arrayEventMark x
    if x == stop then return (40 + x)
  arrayEventMark 9
  return 0

def arrayEventContinueBreak (xs : Array Nat) : ArrayEvents Nat := do
  let mut result := 0
  for x in xs do
    arrayEventMark x
    if x == 1 then continue
    result := result + x
    if x == 2 then break
    arrayEventMark 6
  return result

def arrayEventNestedReturn (xs : Array Nat) (stop : Nat) : ArrayEvents Nat := do
  for x in xs do
    for y in xs do
      arrayEventMark (x * 10 + y)
      if y == 1 then continue
      if x == stop then return (x * 10 + y)
      break
    arrayEventMark 9
  arrayEventMark 8
  return 0

-- Neither this Monad nor its intentionally visible pure/bind operations
-- has a LawfulMonad instance. The direct loop checks exact sequencing,
-- including the empty and early-done branches.
-- FLN_EXPECT_NAT 4123
#eval (arrayTraced (List.toArray [1, 2, 3]) 9 4 0).value
-- FLN_EXPECT_NAT 7172738
#eval (arrayTraced (List.toArray [1, 2, 3]) 9 4 0).trace
-- FLN_EXPECT_NAT 412
#eval (arrayTraced (List.toArray [1, 2, 3]) 2 4 0).value
-- FLN_EXPECT_NAT 71728
#eval (arrayTraced (List.toArray [1, 2, 3]) 2 4 0).trace
-- FLN_EXPECT_NAT 41
#eval (arrayTraced (List.toArray [1, 2, 3]) 1 4 0).value
-- FLN_EXPECT_NAT 718
#eval (arrayTraced (List.toArray [1, 2, 3]) 1 4 0).trace
-- FLN_EXPECT_NAT 4
#eval (arrayTraced (List.toArray []) 1 4 0).value
-- FLN_EXPECT_NAT 8
#eval (arrayTraced (List.toArray []) 1 4 0).trace
-- FLN_EXPECT_NAT 42
#eval (arrayEventReturn (List.toArray [1, 2, 3]) 2 0).value
-- FLN_EXPECT_NAT 102
#eval (arrayEventReturn (List.toArray [1, 2, 3]) 2 0).trace
-- FLN_EXPECT_NAT 0
#eval (arrayEventReturn (List.toArray [1, 2, 3]) 8 0).value
-- FLN_EXPECT_NAT 1020309
#eval (arrayEventReturn (List.toArray [1, 2, 3]) 8 0).trace
-- FLN_EXPECT_NAT 9
#eval (arrayEventReturn (List.toArray []) 8 0).trace
-- FLN_EXPECT_NAT 2
#eval (arrayEventContinueBreak (List.toArray [1, 2, 3]) 0).value
-- FLN_EXPECT_NAT 102
#eval (arrayEventContinueBreak (List.toArray [1, 2, 3]) 0).trace
-- FLN_EXPECT_NAT 12
#eval (arrayEventNestedReturn (List.toArray [1, 2]) 1 0).value
-- FLN_EXPECT_NAT 1112
#eval (arrayEventNestedReturn (List.toArray [1, 2]) 1 0).trace
-- FLN_EXPECT_NAT 22
#eval (arrayEventNestedReturn (List.toArray [1, 2]) 2 0).value
-- FLN_EXPECT_NAT 1112092122
#eval (arrayEventNestedReturn (List.toArray [1, 2]) 2 0).trace
-- FLN_EXPECT_NAT 11120921220908
#eval (arrayEventNestedReturn (List.toArray [1, 2]) 3 0).trace
