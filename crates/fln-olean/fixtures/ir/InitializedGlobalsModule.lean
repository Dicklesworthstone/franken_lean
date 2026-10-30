module

prelude
public import Init

public section

-- Named initialization alone: the later global depends on the earlier one.
-- Consumers must retain one reference across ordinary calls and closures.
@[noinline] def initializeSharedCounter : IO (IO.Ref Nat) := IO.mkRef 40
@[init initializeSharedCounter] opaque sharedCounter : IO.Ref Nat

@[noinline] def initializeRememberedCounter : IO Nat := sharedCounter.get
@[init initializeRememberedCounter] opaque rememberedCounter : Nat

@[noinline] def incrementInitializedCounter (amount : Nat) : IO Nat := do
  sharedCounter.modify (· + amount)
  sharedCounter.get

@[noinline] def applyInitializedIncrement (action : Nat → IO Nat) (amount : Nat) : IO Nat :=
  action amount

@[noinline] def initializedGlobalsAnswer : IO Nat := do
  let first ← incrementInitializedCounter 1
  let second ← applyInitializedIncrement incrementInitializedCounter 2
  return first + second + rememberedCounter + (← sharedCounter.get)
