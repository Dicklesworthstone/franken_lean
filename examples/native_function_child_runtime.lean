inductive Branching where
  | leaf (value : Nat)
  | node (children : Nat -> Branching)

def map (delta : Nat) (tree : Branching) : Branching := match tree with
  | .leaf value => Branching.leaf (value + delta)
  | .node children => Branching.node (fun n => map delta (children n))

def follow (tree : Branching) (route : Nat) : Nat := match tree with
  | .leaf value => value
  | .node children => follow (children route) (route + 1)

def sample : Branching :=
  Branching.node (fun n => Branching.node (fun m => Branching.leaf (n + m)))

#eval follow (map 3 sample) 19