-- Open equations are proved with ordinary checked induction hypotheses.
def copy (n : Nat) : Nat := match n with
  | .zero => 0
  | .succ k => Nat.succ (copy k)

theorem copy_ok (n : Nat) : copy n = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [copy, ih]

-- Generalizing gives the hypothesis a new accumulator argument on each call.
def zeroAcc (n : Nat) (acc : Nat) : Nat := match n with
  | .zero => 0
  | .succ k => zeroAcc k (acc + 1)

theorem zeroAcc_ok (n acc : Nat) : zeroAcc n acc = 0 := by
  induction n generalizing acc with
  | zero => rfl
  | succ k ih => exact ih (acc + 1)

inductive Tree where
  | leaf (value : Nat)
  | fork (left right : Tree)

def treeCopy (tree : Tree) : Tree := match tree with
  | .leaf n => Tree.leaf n
  | .fork left right => Tree.fork (treeCopy left) (treeCopy right)

theorem treeCopy_ok (tree : Tree) : treeCopy tree = tree := by
  induction tree with
  | leaf n => rfl
  | fork left right left_ih right_ih => simp only [treeCopy, left_ih, right_ih]

structure Package where
  carrier : Type
  value : carrier

def unpack (package : Package) : package.carrier := by
  cases package with
  | mk carrier value => exact value

def packed : Package := { carrier := Nat, value := 31 }
theorem unpack_ok : unpack packed = 31 := by rfl

theorem by_cases (b : Bool) : b = b := by
  cases b with
  | false => rfl
  | true => rfl
