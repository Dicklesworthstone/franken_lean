-- Both families are admitted together; no provisional global is published.
mutual
  inductive Tree (A : Type) where
    | node (value : A) (children : Forest A)
  inductive Forest (A : Type) where
    | nil
    | cons (head : Tree A) (tail : Forest A)
end

def value (t : Tree Nat) : Nat :=
  match t with
  | .node n children => n

def sample : Tree Nat := Tree.node 7 (@Forest.nil Nat)
theorem computed : value sample = 7 := by rfl

theorem preserve (t : Tree Nat) (P : Tree Nat -> Prop) (h : P t) : P t := by
  cases t with
  | node n children => exact h
