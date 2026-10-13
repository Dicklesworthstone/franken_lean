module
prelude

mutual
  public inductive Tree (A : Type) where
    | leaf (value : A)
    | node (children : Forest A)
  public inductive Forest (A : Type) where
    | nil
    | cons (head : Tree A) (tail : Forest A)
end
