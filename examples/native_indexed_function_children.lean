inductive Tree : Nat -> Type where
  | leaf (index : Nat) (value : Nat) : Tree index
  | node (index : Nat) (child : (n : Nat) -> Tree n) : Tree index

def map (delta : Nat) (index : Nat) (tree : Tree index) : Tree index := by
  induction tree with
  | leaf k value => exact Tree.leaf k (value + delta)
  | node k child ih => exact Tree.node k (fun n => ih n)

def read (index : Nat) (tree : Tree index) : Nat := match tree with
  | .leaf k value => value
  | .node k child => read 20 (child 20)

#eval read 0 (map 2 0 (Tree.node 0 (fun i => Tree.node i (fun j => Tree.leaf j (i + j)))))
