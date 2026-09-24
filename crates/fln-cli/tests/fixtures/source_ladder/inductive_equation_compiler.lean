inductive Tree where
  | leaf : Tree
  | node : Tree → Tree → Tree

def Tree.size : Tree → Nat
  | .leaf => 1
  | .node l r => l.size + r.size + 1

#eval (Tree.node .leaf .leaf).size
