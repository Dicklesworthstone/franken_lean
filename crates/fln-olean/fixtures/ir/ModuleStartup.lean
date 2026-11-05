module

prelude
public import Init

public section

@[noinline] def initializeStartupCounter : IO (IO.Ref Nat) := IO.mkRef 1
@[init initializeStartupCounter] opaque startupCounter : IO.Ref Nat

-- Neither action is called by the entry. Their order with the named snapshot
-- is observable: (1 + 2) * 3 = 9, while the intervening snapshot is 3.
initialize startupCounter.modify (· + 2)

@[noinline] def initializeStartupSnapshot : IO Nat := startupCounter.get
@[init initializeStartupSnapshot] opaque startupSnapshot : Nat

initialize startupCounter.modify (· * 3)

@[noinline] def startupAnswer : IO Nat := do
  return (← startupCounter.get) * 10 + startupSnapshot
