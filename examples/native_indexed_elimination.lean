inductive Vec (A : Type) : Nat -> Type where
  | nil : Vec A 0
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

def length {A : Type} (n : Nat) (xs : Vec A n) : Nat := by
  induction xs with
  | nil => exact 0
  | cons k x tail ih => exact Nat.succ ih

theorem length_ok {A : Type} (n : Nat) (xs : Vec A n) : length n xs = n := by
  induction xs with
  | nil => rfl
  | cons k x tail ih => simp only [length, ih]

def copy {A : Type} (n : Nat) (xs : Vec A n) : Vec A n := by
  induction xs with
  | nil => exact Vec.nil
  | cons k x tail ih => exact Vec.cons k x ih

theorem copy_ok {A : Type} (n : Nat) (xs : Vec A n) : copy n xs = xs := by
  induction xs with
  | nil => rfl
  | cons k x tail ih => simp only [copy, ih]

def two : Vec Nat 2 := Vec.cons 1 7 (Vec.cons 0 9 Vec.nil)
theorem length_two : length 2 two = 2 := by rfl
theorem copy_two : copy 2 two = two := by rfl

inductive Witness (A : Type) (P : A -> Type) : forall a : A, P a -> Type where
  | intro (a : A) (value : P a) : Witness A P a value

def extract {A : Type} {P : A -> Type} (a : A) (value : P a)
    (w : Witness A P a value) : P a := by
  cases w with
  | intro x v => exact v

theorem dependent_example :
    extract 3 true (Witness.intro 3 true : Witness Nat (fun x => Bool) 3 true) = true := by rfl
