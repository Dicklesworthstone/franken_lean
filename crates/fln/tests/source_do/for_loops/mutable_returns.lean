prelude
import Init.Data.List.Control
import Init.Control.Id

structure MutableItems where
  active : Bool
  first : Nat
  second : Nat

def mutableItems (active : Bool) : MutableItems :=
  { active := active, first := 1, second := 2 }

def mutableStepValue {A : Type} (step : ForInStep A) : A :=
  match step with
  | ForInStep.done value => value
  | ForInStep.yield value => value

def mutableIdBoolFor {B : Type}
    (active : Bool) (initial : B) (step : Nat -> B -> Id (ForInStep B)) : Id B :=
  if active then mutableStepValue (step 42 initial) else initial

instance mutableIdBoolIteration : ForIn Id Bool Nat :=
  { forIn := fun active initial step => mutableIdBoolFor active initial step }

structure MutableStateResult (A : Type) where
  value : A
  state : Nat

def MutableState (A : Type) : Type := Nat -> MutableStateResult A

def mutableStatePure {A : Type} (value : A) : MutableState A :=
  fun state => { value := value, state := state }

def mutableStateBind {A B : Type}
    (action : MutableState A) (next : A -> MutableState B) : MutableState B :=
  fun state =>
    let result := action state
    next result.value result.state

instance mutableStatePureInstance : Pure MutableState :=
  { pure := fun value => mutableStatePure value }

instance mutableStateBindInstance : Bind MutableState :=
  { bind := fun action next => mutableStateBind action next }

def mutableStateMark (value : Nat) : MutableState PUnit :=
  fun state => { value := PUnit.unit, state := state * 100 + value }

structure MutableTraceResult (A : Type) where
  value : A
  trace : Nat

def MutableTrace (A : Type) : Type := Nat -> MutableTraceResult A

def mutableTracePure {A : Type} (value : A) : MutableTrace A :=
  fun state => { value := value, trace := state * 10 + 8 }

def mutableTraceBind {A B : Type}
    (action : MutableTrace A) (next : A -> MutableTrace B) : MutableTrace B :=
  fun state =>
    let result := action (state * 10 + 7)
    next result.value result.trace

instance mutableTracePureInstance : Pure MutableTrace :=
  { pure := fun value => mutableTracePure value }

instance mutableTraceBindInstance : Bind MutableTrace :=
  { bind := fun action next => mutableTraceBind action next }

def mutableTraceMark (value : Nat) : MutableTrace PUnit :=
  fun state => { value := PUnit.unit, trace := state * 10 + value }

-- FLN_MUTABLE_MONAD_WITNESSES

def mutableFinish {M : Type -> Type} [Pure M] [Bind M] {B : Type}
    (last : Nat) (step : Nat -> B -> M (ForInStep B)) (first : ForInStep B) : M B :=
  match first with
  | ForInStep.done value => Pure.pure (f := M) value
  | ForInStep.yield value =>
    Bind.bind (m := M) (step last value)
      (fun finalStep => Pure.pure (f := M) (mutableStepValue finalStep))

def mutableFor {M : Type -> Type} [Pure M] [Bind M] {B : Type}
    (items : MutableItems) (initial : B) (step : Nat -> B -> M (ForInStep B)) : M B :=
  if items.active then
    Bind.bind (m := M) (step items.first initial)
      (fun firstStep => mutableFinish items.second step firstStep)
  else
    Pure.pure (f := M) initial

instance mutableStateIteration : ForIn MutableState MutableItems Nat :=
  { forIn := fun items initial step => mutableFor items initial step }

instance mutableTraceIteration : ForIn MutableTrace MutableItems Nat :=
  { forIn := fun items initial step => mutableFor items initial step }

def mutableStringResult
    (active stop : Bool) (initial : Nat) (hit fallback : String) : Id String := do
  let mut total := initial
  for value in active do
    total := total + value
    if stop then return hit
    total := total + 1
  return fallback

def mutablePairResult
    (active : Bool) (stop initial fallback : Nat) : MutableState Nat := do
  let mut total := initial
  let mut count := 0
  for value in mutableItems active do
    total := total + value
    count := count + 1
    if value == stop then return (total * 100 + count)
    total := total + 10
  return (fallback + total * 100 + count)

def mutableEffects (active : Bool) (stop : Nat) : MutableState Nat := do
  mutableStateMark 8
  let mut total := 10
  for value in mutableItems active do
    total := total + value
    mutableStateMark total
    if value == stop then return total
    total := total + 10
    mutableStateMark 7
  mutableStateMark 9
  return total

def mutableNested (stop : Nat) : MutableState Nat := do
  let mut total := 0
  let mut count := 0
  for first in mutableItems true do
    for second in mutableItems true do
      total := total + first * 10 + second
      count := count + 1
      mutableStateMark (first * 10 + second)
      if second == 1 then continue
      if first == stop then return (total * 100 + count)
      break
    mutableStateMark 9
  mutableStateMark 8
  return (total * 100 + count)

def mutableTracedReturn
    (active : Bool) (stop initial fallback : Nat) : MutableTrace Nat := do
  let mut total := initial
  for value in mutableItems active do
    total := total + value
    mutableTraceMark value
    if value == stop then return total
    total := total + 10
    mutableTraceMark 9
  mutableTraceMark 6
  return (fallback + total)

def mutableTerminalIf (selected : Bool) : Id Nat := do
  let mut total := 10
  if selected then
    total := total + 5
    return total
  total := total + 2
  return total

def mutableTerminalMatch (selected : Bool) : Id Nat := do
  let mut total := 10
  match selected with
  | true =>
    total := total + 7
    return total
  | false => Pure.pure PUnit.unit
  total := total + 3
  return total

def mutableTerminalUnless (skipBranch : Bool) : Id Nat := do
  let mut total := 10
  unless skipBranch do
    total := total + 9
    return total
  total := total + 4
  return total

def mutableTerminalLoop (active : Bool) (stop : Nat) : MutableState Nat := do
  let mut total := 10
  for value in mutableItems active do
    if value == stop then
      total := total + value
      return total
    total := total * 10 + value
  return total

def mutableTerminalMixed (active stop : Bool) : MutableState Nat := do
  let mut total := 0
  for value in mutableItems active do
    if value == 1 then
      total := total + 10
      continue
    if stop then
      total := total + 20
      return total
    total := total + 30
    break
  return (total + 100)

def mutableTerminalString (active stop : Bool) : Id String := do
  let mut total := 0
  for value in active do
    if stop then
      total := total + value
      return "hit"
    total := total + 1
  return "fallback"

-- Moving the same pure state computation into each branch does not add
-- Pure.pure or Bind.bind operations, even for this observable non-lawful monad.
def mutableTerminalTraced
    (active : Bool) (stop initial fallback : Nat) : MutableTrace Nat := do
  let mut total := initial
  for value in mutableItems active do
    if value == stop then
      total := total + value
      mutableTraceMark value
      return total
    total := total + value
    mutableTraceMark value
    total := total + 10
    mutableTraceMark 9
  mutableTraceMark 6
  return (fallback + total)

-- FLN_MUTABLE_PROBE string_hit String
#eval mutableStringResult true true 5 "hit" "fallback"
-- FLN_MUTABLE_PROBE string_fallback String
#eval mutableStringResult true false 5 "hit" "fallback"
-- FLN_MUTABLE_PROBE string_empty String
#eval mutableStringResult false true 5 "hit" "empty"
-- FLN_MUTABLE_PROBE pair_first Nat
#eval (mutablePairResult true 1 5 1000 0).value
-- FLN_MUTABLE_PROBE pair_second Nat
#eval (mutablePairResult true 2 5 1000 0).value
-- FLN_MUTABLE_PROBE pair_fallback Nat
#eval (mutablePairResult true 9 5 1000 0).value
-- FLN_MUTABLE_PROBE pair_empty Nat
#eval (mutablePairResult false 1 5 1000 0).value
-- FLN_MUTABLE_PROBE effects_first_value Nat
#eval (mutableEffects true 1 0).value
-- FLN_MUTABLE_PROBE effects_first_trace Nat
#eval (mutableEffects true 1 0).state
-- FLN_MUTABLE_PROBE effects_second_value Nat
#eval (mutableEffects true 2 0).value
-- FLN_MUTABLE_PROBE effects_second_trace Nat
#eval (mutableEffects true 2 0).state
-- FLN_MUTABLE_PROBE effects_fallback_value Nat
#eval (mutableEffects true 9 0).value
-- FLN_MUTABLE_PROBE effects_fallback_trace Nat
#eval (mutableEffects true 9 0).state
-- FLN_MUTABLE_PROBE effects_empty_value Nat
#eval (mutableEffects false 1 0).value
-- FLN_MUTABLE_PROBE effects_empty_trace Nat
#eval (mutableEffects false 1 0).state
-- FLN_MUTABLE_PROBE nested_first_value Nat
#eval (mutableNested 1 0).value
-- FLN_MUTABLE_PROBE nested_first_trace Nat
#eval (mutableNested 1 0).state
-- FLN_MUTABLE_PROBE nested_second_value Nat
#eval (mutableNested 2 0).value
-- FLN_MUTABLE_PROBE nested_second_trace Nat
#eval (mutableNested 2 0).state
-- FLN_MUTABLE_PROBE nested_fallback_value Nat
#eval (mutableNested 3 0).value
-- FLN_MUTABLE_PROBE nested_fallback_trace Nat
#eval (mutableNested 3 0).state
-- FLN_MUTABLE_PROBE nonlawful_first_value Nat
#eval (mutableTracedReturn true 1 5 100 0).value
-- FLN_MUTABLE_PROBE nonlawful_first_trace Nat
#eval (mutableTracedReturn true 1 5 100 0).trace
-- FLN_MUTABLE_PROBE nonlawful_second_value Nat
#eval (mutableTracedReturn true 2 5 100 0).value
-- FLN_MUTABLE_PROBE nonlawful_second_trace Nat
#eval (mutableTracedReturn true 2 5 100 0).trace
-- FLN_MUTABLE_PROBE nonlawful_fallback_value Nat
#eval (mutableTracedReturn true 9 5 100 0).value
-- FLN_MUTABLE_PROBE nonlawful_fallback_trace Nat
#eval (mutableTracedReturn true 9 5 100 0).trace
-- FLN_MUTABLE_PROBE nonlawful_empty_value Nat
#eval (mutableTracedReturn false 1 5 100 0).value
-- FLN_MUTABLE_PROBE nonlawful_empty_trace Nat
#eval (mutableTracedReturn false 1 5 100 0).trace

-- FLN_MUTABLE_PROBE terminal_if_hit Nat
#eval mutableTerminalIf true

-- FLN_MUTABLE_PROBE terminal_if_fallback Nat
#eval mutableTerminalIf false

-- FLN_MUTABLE_PROBE terminal_match_hit Nat
#eval mutableTerminalMatch true

-- FLN_MUTABLE_PROBE terminal_match_fallback Nat
#eval mutableTerminalMatch false

-- FLN_MUTABLE_PROBE terminal_unless_hit Nat
#eval mutableTerminalUnless false

-- FLN_MUTABLE_PROBE terminal_unless_fallback Nat
#eval mutableTerminalUnless true

-- FLN_MUTABLE_PROBE terminal_loop_first Nat
#eval (mutableTerminalLoop true 1 0).value

-- FLN_MUTABLE_PROBE terminal_loop_second Nat
#eval (mutableTerminalLoop true 2 0).value

-- FLN_MUTABLE_PROBE terminal_loop_fallback Nat
#eval (mutableTerminalLoop true 0 0).value

-- FLN_MUTABLE_PROBE terminal_loop_empty Nat
#eval (mutableTerminalLoop false 1 0).value

-- FLN_MUTABLE_PROBE terminal_mixed_return Nat
#eval (mutableTerminalMixed true true 0).value

-- FLN_MUTABLE_PROBE terminal_mixed_break Nat
#eval (mutableTerminalMixed true false 0).value

-- FLN_MUTABLE_PROBE terminal_mixed_empty Nat
#eval (mutableTerminalMixed false true 0).value

-- FLN_MUTABLE_PROBE terminal_string_hit String
#eval mutableTerminalString true true

-- FLN_MUTABLE_PROBE terminal_string_fallback String
#eval mutableTerminalString true false

-- FLN_MUTABLE_PROBE terminal_string_empty String
#eval mutableTerminalString false true

-- FLN_MUTABLE_PROBE terminal_nonlawful_first_value Nat
#eval (mutableTerminalTraced true 1 5 100 0).value

-- FLN_MUTABLE_PROBE terminal_nonlawful_first_trace Nat
#eval (mutableTerminalTraced true 1 5 100 0).trace

-- FLN_MUTABLE_PROBE terminal_nonlawful_second_value Nat
#eval (mutableTerminalTraced true 2 5 100 0).value

-- FLN_MUTABLE_PROBE terminal_nonlawful_second_trace Nat
#eval (mutableTerminalTraced true 2 5 100 0).trace

-- FLN_MUTABLE_PROBE terminal_nonlawful_fallback_value Nat
#eval (mutableTerminalTraced true 9 5 100 0).value

-- FLN_MUTABLE_PROBE terminal_nonlawful_fallback_trace Nat
#eval (mutableTerminalTraced true 9 5 100 0).trace

-- FLN_MUTABLE_PROBE terminal_nonlawful_empty_value Nat
#eval (mutableTerminalTraced false 1 5 100 0).value

-- FLN_MUTABLE_PROBE terminal_nonlawful_empty_trace Nat
#eval (mutableTerminalTraced false 1 5 100 0).trace
