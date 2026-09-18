-- Case analysis keeps a checked equation relating each branch to the original
-- computation. The earlier hypothesis still speaks about that computation.
theorem keepComputed (f : Nat -> Bool) (n : Nat) (P : Bool -> Prop)
    (p : P (f n)) : P (f n) := by
  cases h : f n with
  | false => rw [<- h]; exact p
  | true => rw [<- h]; exact p

def copyComputed (n : Nat) : Nat := match n with
  | .zero => 0
  | .succ k => Nat.succ (copyComputed k)

-- The induction hypothesis is produced by Nat.rec, not guessed from the goal.
theorem copyComputation (f : Nat -> Nat) (n : Nat) : copyComputed (f n) = f n := by
  induction (f n) with
  | zero => rfl
  | succ k ih => simp only [copyComputed, ih]

structure ComputedPackage where
  carrier : Type
  value : carrier

-- The result type depends on the value being analyzed.
def computedPayload (f : Nat -> ComputedPackage) (n : Nat) : (f n).carrier := by
  cases f n with
  | mk A a => exact a

inductive ComputedFlag : Bool -> Type where
  | no : ComputedFlag false
  | yes : ComputedFlag true

-- The index excludes the other constructor through the existing checked
-- index-refinement machinery, even for an expression discriminant.
theorem onlyPossible (f : Nat -> ComputedFlag true) (n : Nat) : true = true := by
  cases h : f n with
  | yes => rfl