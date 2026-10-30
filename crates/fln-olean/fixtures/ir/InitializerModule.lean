module

prelude
public import Init

public section

-- Explicit attribute names let the decoder's test compare the actual journal
-- with independent source expectations, including a deliberately unsorted
-- global order and a standalone action between two named globals.
@[noinline] def initializeZ : IO (IO.Ref Nat) := IO.mkRef 40
@[init initializeZ] opaque zValue : IO.Ref Nat

@[init] def advanceZ : IO Unit := zValue.modify (· + 1)

@[noinline] def initializeA : IO Nat := zValue.get
@[init initializeA] opaque aValue : Nat

@[noinline] def readInitializedValues : IO Nat := do
  return (← zValue.get) + aValue
