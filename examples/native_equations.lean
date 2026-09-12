-- Equation-style declarations use the same checked matcher and recursion engine.
inductive Seq (A : Type) where
  | nil
  | cons (value : A) (tail : Seq A)

def append {A : Type} : Seq A -> Seq A -> Seq A
  | .nil, ys => ys
  | .cons x xs, ys => Seq.cons x (append xs ys)

def numbers : Seq Nat := Seq.cons 2 (Seq.cons 3 Seq.nil)
theorem append_value : append numbers (Seq.cons 4 Seq.nil) = Seq.cons 2 (Seq.cons 3 (Seq.cons 4 Seq.nil)) := by rfl

theorem append_right_nil {A : Type} (xs : Seq A) : append xs Seq.nil = xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp only [append, ih]

def priority : Bool -> Bool -> Nat
  | true, _ => 1
  | _, true => 2
  | _, _ => 3

theorem priority_value : priority false true = 2 := by rfl

def sumFrom : Nat -> Nat -> Nat
  | .zero, acc => acc
  | .succ k, acc => sumFrom k (acc + k)
theorem sum_value : sumFrom 4 7 = 13 := by rfl

inductive Vec (A : Type) : Nat -> Type where
  | nil : Vec A 0
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

def tail {A : Type} (n : Nat) : Vec A (Nat.succ n) -> Vec A n
  | .cons k x rest => rest

theorem tail_value : tail 0 (Vec.cons 0 8 Vec.nil) = Vec.nil := by rfl

def copyVec {A : Type} (n : Nat) : Vec A n -> Vec A n
  | .nil => Vec.nil
  | .cons k x rest => Vec.cons k x (copyVec k rest)

theorem copy_value : copyVec 1 (Vec.cons 0 8 Vec.nil) = Vec.cons 0 8 Vec.nil := by rfl

theorem bool_self : forall b : Bool, b = b
  | true => by
    have h : true = true := rfl
    exact h
  | false => rfl
