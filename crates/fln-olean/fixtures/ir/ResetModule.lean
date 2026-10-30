module

prelude
public import Init

public section

-- User-class code only. The Reference supplies executable IR as an oracle;
-- Golem must execute every selected function using its own runtime.
inductive ResetChain where
  | nil
  | cons (head : Nat) (tail : ResetChain)

@[noinline] def resetMap (delta : Nat) : ResetChain → ResetChain
  | .nil => .nil
  | .cons x xs => .cons (x + delta) (resetMap delta xs)

@[noinline] def resetSum : ResetChain → Nat
  | .nil => 0
  | .cons x xs => x + resetSum xs

@[noinline] def resetHead (replacement : Nat) : ResetChain → ResetChain
  | .nil => .nil
  | .cons _ xs => .cons replacement xs

@[noinline] def resetApply (f : ResetChain → ResetChain) (xs : ResetChain) : ResetChain :=
  f xs

@[noinline] def resetAnswer (delta : Nat) : Nat :=
  resetSum (resetMap delta (.cons 19 (.cons 23 (.cons 7 .nil))))

@[noinline] def resetSharedAnswer (delta : Nat) : Nat :=
  let xs := ResetChain.cons 19 (.cons 23 (.cons 7 .nil))
  let ys := resetMap delta xs
  let zs := resetHead 42 xs
  resetSum ys + resetSum xs + resetSum zs

@[noinline] def resetClosureAnswer (delta : Nat) : Nat :=
  resetSum (resetApply (resetMap delta) (.cons 19 (.cons 23 .nil)))

@[noinline] def resetEmptyAnswer (delta : Nat) : Nat :=
  resetSum (resetMap delta .nil)
