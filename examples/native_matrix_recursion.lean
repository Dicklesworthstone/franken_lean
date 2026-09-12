-- Recursive matrix programs and a proof for every input.
inductive Seq (A : Type) where
  | nil
  | cons (value : A) (tail : Seq A)

def zipSum (xs ys : Seq Nat) : Seq Nat := match xs, ys with
  | .nil, _ => Seq.nil
  | .cons x xt, .nil => Seq.nil
  | .cons x xt, .cons y yt => Seq.cons (x + y) (zipSum xt yt)

theorem zip_example : zipSum (Seq.cons 1 (Seq.cons 2 Seq.nil)) (Seq.cons 3 (Seq.cons 4 Seq.nil)) = Seq.cons 4 (Seq.cons 6 Seq.nil) := by rfl

inductive Vec (A : Type) : Nat -> Type where
  | nil : Vec A 0
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

def zipVec (n : Nat) (xs ys : Vec Nat n) : Vec Nat n := match xs, ys with
  | .nil, .nil => Vec.nil
  | .cons k x xt, .cons j y yt => Vec.cons k (x + y) (zipVec k xt yt)

theorem vector_example : zipVec 2 (Vec.cons 1 1 (Vec.cons 0 2 Vec.nil)) (Vec.cons 1 3 (Vec.cons 0 4 Vec.nil)) = Vec.cons 1 4 (Vec.cons 0 6 Vec.nil) := by rfl

def copyMatrix (n : Nat) (b : Bool) : Nat := match n, b with
  | .zero, _ => 0
  | .succ k, _ => Nat.succ (copyMatrix k b)

theorem copy_all (n : Nat) (b : Bool) : copyMatrix n b = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [copyMatrix, ih]

def accumulate (n : Nat) (flag : Bool) (acc : Nat) : Nat := match n, flag with
  | .zero, _ => acc
  | .succ k, true => accumulate k false (acc + 1)
  | .succ k, false => accumulate k true (acc + 2)

theorem accumulated : accumulate 4 true 10 = 16 := by rfl

inductive Walk : Nat -> Type where
  | done (n : Nat) : Walk n
  | step (n : Nat) (child : Walk n) : Walk n

def constrained (w : Walk 7) (flag : Bool) : Nat := match w, flag with
  | .done k, _ => k
  | .step k child, true => constrained child false + 1
  | .step k child, false => constrained child true + 2

theorem constrained_ok : constrained (Walk.step 7 (Walk.step 7 (Walk.done 7))) true = 10 := by rfl

def sumNested (xs : Seq (Seq Nat)) : Nat := match xs with
  | .nil => 0
  | .cons .nil tail => sumNested tail
  | .cons (.cons x inner) tail => x + sumNested tail

theorem nested_ok : sumNested (Seq.cons (Seq.cons 3 Seq.nil) (Seq.cons (Seq.cons 4 Seq.nil) Seq.nil)) = 7 := by rfl

def zipWith {A B C : Type} (f : A -> B -> C) (xs : Seq A) (ys : Seq B) : Seq C := match xs, ys with
  | .nil, _ => Seq.nil
  | .cons x xt, .nil => Seq.nil
  | .cons x xt, .cons y yt => Seq.cons (f x y) (zipWith f xt yt)

theorem polymorphic_ok : zipWith (fun x y => x + y) (Seq.cons 4 Seq.nil) (Seq.cons 5 Seq.nil) = Seq.cons 9 Seq.nil := by rfl
