inductive Vec (A : Type) : Nat -> Type where
  | nil : Vec A 0
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

def head {A : Type} (n : Nat) (xs : Vec A (Nat.succ n)) : A := by
  cases xs with
  | cons k x tail => exact x

def tail {A : Type} (n : Nat) (xs : Vec A (Nat.succ n)) : Vec A n := by
  cases xs with
  | cons k x rest => exact rest

def second (xs : Vec Nat 2) : Nat := by
  cases xs with
  | cons k x rest =>
    cases rest with
    | cons j y end => exact y

theorem head_ok : head 1 (Vec.cons 1 7 (Vec.cons 0 9 Vec.nil)) = 7 := by rfl
theorem tail_ok : tail 1 (Vec.cons 1 7 (Vec.cons 0 9 Vec.nil)) = Vec.cons 0 9 Vec.nil := by rfl
theorem second_ok : second (Vec.cons 1 7 (Vec.cons 0 9 Vec.nil)) = 9 := by rfl

inductive PairAt : Nat -> Nat -> Type where
  | mk (a b : Nat) : PairAt a b

def repeated (n : Nat) (p : PairAt n n) : Nat := by
  cases p with
  | mk a b => exact a + b

theorem repeated_ok : repeated 7 (PairAt.mk 7 7) = 14 := by rfl

inductive Witness (A : Type) (P : A -> Type) : forall a : A, P a -> Type where
  | intro (a : A) (value : P a) : Witness A P a value

def getWitness (w : Witness Nat (fun x => Bool) 7 true) : Bool := by
  cases w with
  | intro a value => exact value

theorem witness_ok : getWitness (Witness.intro 7 true) = true := by rfl

inductive Diagonal : Nat -> Nat -> Type where
  | mk (n : Nat) : Diagonal n n

def impossible (x : Diagonal 0 1) : Nat := by cases x
