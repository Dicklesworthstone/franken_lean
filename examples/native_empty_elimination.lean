-- The empty vector case cannot supply a head; checked evidence rules it out.
inductive Vec (A : Type) : Nat -> Type where
  | nil : Vec A 0
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

def first {A : Type} (n : Nat) (xs : Vec A n) (h : n = 0 -> False) : A :=
  Vec.rec (motive := fun k _ => (k = 0 -> False) -> A)
    (fun h => False.elim (h (by rfl)))
    (fun k x tail ih h => x) xs h

-- No constructor is invented for an empty data type inside an ordinary sum.
inductive NeverValue : Type where

def missingOrTwo (x : Option NeverValue) : Nat :=
  match x with
  | .none => 2
  | .some impossible => NeverValue.rec (motive := fun _ => Nat) impossible

#eval first 1 (Vec.cons 0 40 Vec.nil) (by decide) + missingOrTwo Option.none
