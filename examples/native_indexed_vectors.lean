inductive Vec (A : Type) : Nat -> Type where
  | nil : Vec A 0
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

def map {A B : Type} (f : A -> B) (n : Nat) (xs : Vec A n) : Vec B n := by
  induction xs with
  | nil => exact Vec.nil
  | cons k x tail ih => exact Vec.cons k (f x) ih

def total (n : Nat) (xs : Vec Nat n) : Nat := by
  induction xs with
  | nil => exact 0
  | cons k x tail ih => exact x + ih

#eval total 2 (map (fun n => n + 1) 2 (Vec.cons 1 20 (Vec.cons 0 20 Vec.nil)))
