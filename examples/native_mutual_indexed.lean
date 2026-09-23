mutual
inductive Tree : Nat -> Type where
  | leaf (n : Nat) (value : Nat) : Tree n
  | node (n : Nat) (children : Forest n) : Tree n
inductive Forest : Nat -> Type where
  | nil (n : Nat) : Forest n
  | cons (n : Nat) (head : Tree n) (tail : Forest n) : Forest n
end

def map (delta : Nat) (n : Nat) (xs : Forest n) : Forest n :=
  @Forest.rec (fun n t => Tree n) (fun n xs => Forest n)
    (fun n value => Tree.leaf n (value + delta))
    (fun n children ih => Tree.node n ih)
    (fun n => Forest.nil n)
    (fun n head tail ihHead ihTail => Forest.cons n ihHead ihTail) n xs

def sum (n : Nat) (xs : Forest n) : Nat :=
  @Forest.rec (fun n t => Nat) (fun n xs => Nat)
    (fun n value => value) (fun n children ih => ih) (fun n => 0)
    (fun n head tail ihHead ihTail => ihHead + ihTail) n xs

#eval sum 7 (map 1 7 (Forest.cons 7 (Tree.leaf 7 39) (Forest.cons 7 (Tree.node 7 (Forest.cons 7 (Tree.leaf 7 1) (Forest.nil 7))) (Forest.nil 7))))
