-- Native source recursion is lowered to checked recursor applications.
def sumTo (n : Nat) : Nat := match n with
  | .zero => n
  | .succ k => sumTo k + n

def sumAcc (n : Nat) (acc : Nat) : Nat := match n with
  | .zero => acc
  | .succ k => sumAcc k (acc + n)

inductive Tree where
  | leaf (value : Nat)
  | fork (left right : Tree)

def treeSum (tree : Tree) : Nat := match tree with
  | .leaf value => value
  | .fork left right => treeSum left + treeSum right

def repeat (n : Nat) {A : Type} (step : A -> A) (acc : A) : A := match n with
  | .zero => acc
  | .succ k => repeat k step (step acc)

def add (n : Nat) (m : Nat) : Nat := match n with
  | .zero => m
  | .succ k => let smaller := add k; smaller (m + 1)

def checkedSteps (n : Nat) (h : n = n) : Nat := match n with
  | .zero => 0
  | .succ k => checkedSteps k rfl + 1

theorem sum_ok : sumTo 4 = 10 := by rfl
theorem acc_ok : sumAcc 4 7 = 17 := by rfl
theorem tree_ok : treeSum (Tree.fork (Tree.leaf 3) (Tree.fork (Tree.leaf 7) (Tree.leaf 11))) = 21 := by rfl
theorem generic_ok : repeat 3 (fun x => x + 2) 1 = 7 := by rfl
theorem partial_ok : add 3 5 = 8 := by rfl
theorem dependent_ok : checkedSteps 4 rfl = 4 := by rfl
