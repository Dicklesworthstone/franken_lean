mutual
inductive Tree (A : Type) where
  | node (value : A) (children : Forest A)
inductive Forest (A : Type) where
  | nil
  | cons (head : Tree A) (tail : Forest A)
end

def action (t : Tree Nat) : Nat -> Nat :=
  match t with
  | .node n children => fun k => n + k

def first (xs : Forest Nat) : Nat :=
  match xs with
  | .nil => 0
  | .cons t rest => action t 2

#eval first (Forest.cons (Tree.node 40 (@Forest.nil Nat)) (@Forest.nil Nat))