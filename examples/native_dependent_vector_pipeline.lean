inductive Vec (A : Type) : Nat -> Type where
  | nil : Vec A 0
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

def first {A : Type} (n : Nat) (xs : Vec A (Nat.succ n)) : A :=
  match xs with | .cons k x tail => x

def rest {A : Type} (n : Nat) (xs : Vec A (Nat.succ n)) : Vec A n :=
  match xs with | .cons k x tail => tail

#eval first 0 (rest 1 (rest 2 (Vec.cons 2 5 (Vec.cons 1 7 (Vec.cons 0 42 Vec.nil)))))
