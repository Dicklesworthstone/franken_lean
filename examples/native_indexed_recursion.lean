inductive Vec (A : Type) : Nat -> Type where
  | nil : Vec A 0
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

def copyVec {A : Type} (n : Nat) (xs : Vec A n) : Vec A n := match xs with
  | .nil => Vec.nil
  | .cons k x tail => Vec.cons k x (copyVec k tail)

def mapVec {A B : Type} (f : A -> B) (n : Nat) (xs : Vec A n) : Vec B n := match xs with
  | .nil => Vec.nil
  | .cons k x tail => Vec.cons k (f x) (mapVec f k tail)

def sumInto (n : Nat) (xs : Vec Nat n) (acc : Nat) : Nat := match xs with
  | .nil => acc
  | .cons k x tail => sumInto k tail (acc + x)

def indexSum {A : Type} (n : Nat) (xs : Vec A n) : Nat := match xs with
  | .nil => n
  | .cons k x tail => indexSum k tail + n

def two : Vec Nat 2 := Vec.cons 1 7 (Vec.cons 0 9 Vec.nil)

theorem copied : copyVec 2 two = two := by rfl
theorem mapped : mapVec (fun x => x + 1) 2 two = Vec.cons 1 8 (Vec.cons 0 10 Vec.nil) := by rfl
theorem accumulated : sumInto 2 two 10 = 26 := by rfl
theorem indices_rebound : indexSum 2 two = 3 := by rfl

theorem copy_identity {A : Type} (n : Nat) (xs : Vec A n) : copyVec n xs = xs := by
  induction xs with
  | nil => rfl
  | cons k x tail ih => simp only [copyVec, ih]

theorem map_identity {A : Type} (n : Nat) (xs : Vec A n) : mapVec (fun x => x) n xs = xs := by
  induction xs with
  | nil => rfl
  | cons k x tail ih => simp only [mapVec, ih]