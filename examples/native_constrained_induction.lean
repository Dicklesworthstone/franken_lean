inductive Loop : Nat -> Type where
  | seed (n : Nat) : Loop n
  | step (n : Nat) (rest : Loop n) : Loop n

def copyLoop (n : Nat) (x : Loop n) : Loop n := match x with
  | .seed k => Loop.seed k
  | .step k rest => Loop.step k (copyLoop k rest)

theorem fixed_copy (x : Loop 7) : copyLoop 7 x = x := by
  induction x with
  | seed n => rfl
  | step n rest ih => simp only [copyLoop, ih rest (HEq.refl 7) (HEq.refl rest)]

theorem accumulator_copy (x : Loop 7) (acc : Nat) : copyLoop 7 x = x := by
  induction x generalizing acc with
  | seed n => rfl
  | step n rest ih => simp only [copyLoop, ih rest (acc + 1) (HEq.refl 7) (HEq.refl rest)]

inductive Vec (A : Type) : Nat -> Type where
  | nil : Vec A 0
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

def length (n : Nat) (xs : Vec Nat n) : Nat := match xs with
  | .nil => 0
  | .cons k x tail => Nat.succ (length k tail)

theorem positive_length (n : Nat) (xs : Vec Nat (Nat.succ n)) : length (Nat.succ n) xs = Nat.succ n := by
  induction xs generalizing n with
  | cons k x tail ih =>
    cases k with
    | zero =>
      cases tail with
      | nil => rfl
    | succ j => simp only [length, ih j tail (HEq.refl (Nat.succ j)) (HEq.refl tail)]

theorem copy_computes : copyLoop 7 (Loop.step 7 (Loop.seed 7)) = Loop.step 7 (Loop.seed 7) := by rfl

theorem length_computes : length 2 (Vec.cons 1 3 (Vec.cons 0 9 Vec.nil)) = 2 := by rfl

inductive Trace (A : Type) (P : A -> Type) : forall a : A, P a -> Type where
  | base (a : A) (v : P a) : Trace A P a v
  | step (a : A) (v : P a) (child : Trace A P a v) : Trace A P a v

def traceCopy {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) : Trace A P a v := match t with
  | .base x y => Trace.base x y
  | .step x y child => Trace.step x y (traceCopy x y child)

theorem dependent_copy (A : Type) (P : A -> Type) (f : A -> A) (a : A) (v : P (f a))
    (value : Trace A P (f a) v) : traceCopy (f a) v value = value := by
  induction value with
  | base x y => rfl
  | step x y child ih =>
    simp only [traceCopy, ih child (HEq.refl (f a)) (HEq.refl v) (HEq.refl child)]
    rfl
