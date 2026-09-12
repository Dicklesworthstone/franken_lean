inductive Walk : Nat -> Type where
  | done (n : Nat) : Walk n
  | step (n : Nat) (child : Walk n) : Walk n

def copyAtSeven (w : Walk 7) : Walk 7 := match w with
  | .done n => Walk.done n
  | .step n child => Walk.step n (copyAtSeven child)

def countFrom (w : Walk 7) (acc : Nat) : Nat := match w with
  | .done n => acc
  | .step n child => countFrom child (acc + 1)

def sample : Walk 7 := Walk.step 7 (Walk.step 7 (Walk.done 7))
theorem copied : copyAtSeven sample = sample := by rfl
theorem counted : countFrom sample 4 = 6 := by rfl

theorem copy_identity (w : Walk 7) : copyAtSeven w = w := by
  induction w with
  | done n => rfl
  | step n child ih => simp only [copyAtSeven, ih]

inductive TreeAt : Nat -> Nat -> Type where
  | leaf (a b : Nat) : TreeAt a b
  | fork (a b : Nat) (left right : TreeAt a b) : TreeAt a b

def sizeRepeated (n : Nat) (tree : TreeAt n n) : Nat := match tree with
  | .leaf a b => 1
  | .fork a b left right => sizeRepeated n left + sizeRepeated n right

theorem two_leaves : sizeRepeated 3 (TreeAt.fork 3 3 (TreeAt.leaf 3 3) (TreeAt.leaf 3 3)) = 2 := by rfl

def combine (w : Walk 7) (a b : Nat) : Nat := match w with
  | .done n => a * 10 + b
  | .step n child =>
    let next : Nat -> Nat -> Nat := fun v => combine child v;
    next a (b + 1)

theorem partial_application : combine sample 3 5 = 37 := by rfl

inductive Trace (A : Type) (P : A -> Type) : forall a : A, P a -> Type where
  | base (a : A) (v : P a) : Trace A P a v
  | step (a : A) (v : P a) (child : Trace A P a v) : Trace A P a v

def traceDepth {A : Type} {P : A -> Type} (f : A -> A) (a : A) (v : P (f a))
    (t : Trace A P (f a) v) (acc : Nat) : Nat := match t with
  | .base x vx => acc
  | .step x vx child => traceDepth f a v child (acc + 1)

def traceSample : Trace Nat (fun n => Bool) 7 true := Trace.step 7 true (Trace.base 7 true)
theorem dependent_indices : traceDepth Nat.succ 6 true traceSample 4 = 5 := by rfl
