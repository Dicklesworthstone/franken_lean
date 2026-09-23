mutual
inductive Tree : Nat -> Type where
  | leaf (n : Nat) (value : Nat) : Tree n
  | node (child : (i : Nat) -> Forest i) : Tree 0
inductive Forest : Nat -> Type where
  | leaf (n : Nat) (value : Nat) : Forest n
  | node (n : Nat) (child : (i : Nat) -> Tree i) : Forest n
end

def map (delta : Nat) (n : Nat) (t : Tree n) : Tree n :=
  @Tree.rec (fun n t => Tree n) (fun n f => Forest n)
    (fun n value => Tree.leaf n (value + delta))
    (fun child ih => Tree.node (fun i => ih i))
    (fun n value => Forest.leaf n (value + delta))
    (fun n child ih => Forest.node n (fun i => ih i)) n t

def total (n : Nat) (t : Tree n) : Nat :=
  @Tree.rec (fun n t => Nat) (fun n f => Nat)
    (fun n value => value) (fun child ih => ih 20)
    (fun n value => value) (fun n child ih => ih 20) n t

#eval total 0 (map 2 0 (Tree.node (fun i => Forest.node i (fun j => Tree.leaf j (i + j)))))