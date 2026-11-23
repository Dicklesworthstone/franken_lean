module

-- User-code fixture compiled by the pinned Reference for Golem differentials.
-- Native Thunk implementations are never interpreted from Reference IR.
prelude
public import Init.Core

public section

@[noinline] def useThunkConstructor (make : (Unit → Nat) → Thunk Nat) (n : Nat) : Nat :=
  let delayed := make (fun _ => n + 1)
  delayed.get + delayed.get

@[noinline] def useThunkPure (make : Nat → Thunk Nat) (n : Nat) : Nat :=
  (make n).get

@[noinline] def useThunkGet (force : Thunk Nat → Nat) (n : Nat) : Nat :=
  let delayed := Thunk.mk (fun _ => n + 1)
  force delayed + force delayed

def thunkDirect (n : Nat) : Nat := (Thunk.pure n).get
def thunkConstructor (n : Nat) : Nat := useThunkConstructor Thunk.mk n
def thunkPure (n : Nat) : Nat := useThunkPure Thunk.pure n
def thunkGet (n : Nat) : Nat := useThunkGet Thunk.get n

@[noinline] def thunkCapturedBody (n : Nat) (_ : Unit) : Nat := n + 1

def thunkCaptured (n : Nat) : Nat :=
  let delayed := Thunk.mk (thunkCapturedBody n)
  delayed.get + delayed.get

partial def thunkLoop (n : Nat) (u : Unit) : Nat := thunkLoop (n + 1) u

def thunkLazy (n : Nat) : Nat :=
  let delayed := Thunk.mk (thunkLoop n)
  if n == 0 then n else delayed.get
