inductive Vec (A : Type) : Nat -> Type where
  | nil : Vec A 0
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

def map {A B : Type} (f : A -> B) (n : Nat) (xs : Vec A n) : Vec B n := match xs with
  | .nil => Vec.nil
  | .cons k x tail => Vec.cons k (f x) (map f k tail)

def total (n : Nat) (xs : Vec Nat n) : Nat := match xs with
  | .nil => 0
  | .cons k x tail => x + total k tail

#eval total 2 (map (fun n => n + 1) 2 (Vec.cons 1 20 (Vec.cons 0 20 Vec.nil)))
