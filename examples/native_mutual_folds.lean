mutual
inductive Tree (A : Type) where
  | leaf (value : A)
  | node (children : Forest A)
inductive Forest (B : Type) where
  | nil
  | cons (head : Tree B) (tail : Forest B)
end

-- The Tree peer has an accumulator; the Forest peer returns a plain Nat.
-- Only the Tree peer reads the outer offset.
def total (offset : Nat) (xs : Forest Nat) : Nat :=
  @Forest.rec Nat
    (fun (t : Tree Nat) => Nat -> Nat)
    (fun (xs : Forest Nat) => Nat)
    (fun (n : Nat) (acc : Nat) => n + acc + offset)
    (fun (xs : Forest Nat) (ih : Nat) (acc : Nat) => ih + acc)
    0
    (fun (t : Tree Nat) (xs : Forest Nat) (ihT : Nat -> Nat) (ihF : Nat) => ihT ihF)
    xs

#eval total 2 (Forest.cons (Tree.leaf 40) (@Forest.nil Nat))