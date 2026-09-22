mutual
inductive Tree (A : Type) where
  | node (value : A) (children : Forest A)
inductive Forest (B : Type) where
  | nil
  | cons (head : Tree B) (tail : Forest B)
end

def action (t : Tree Nat) : Nat -> Nat :=
  match t with
  | .node n children => fun k => n + k

def first (xs : Forest Nat) : Nat :=
  match xs with
  | .nil => 0
  | .cons t rest => action t 2

#eval first (Forest.cons (Tree.node 40 (@Forest.nil Nat)) (@Forest.nil Nat))