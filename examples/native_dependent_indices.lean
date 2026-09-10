inductive Trace (A : Type) (P : A -> Type) : forall a : A, P a -> Type where
  | stop (a : A) (v : P a) : Trace A P a v
  | step (a b : A) (v : P a) (w : P b) (child : Trace A P a v) : Trace A P b w

def trace : Trace Nat (fun a => Bool) 2 false := Trace.step 1 2 true false (Trace.stop 1 true)

def rebuild {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) : Trace A P a v := match t with
  | .stop x vx => Trace.stop x vx
  | .step x y vx vy child => Trace.step x y vx vy child

def copyTrace {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) : Trace A P a v := match t with
  | .stop x vx => Trace.stop x vx
  | .step x y vx vy child => Trace.step x y vx vy (copyTrace x vx child)

def depth {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) : Nat := match t with
  | .stop x vx => 0
  | .step x y vx vy child => depth x vx child + 1

theorem rebuilt : rebuild 2 false trace = trace := by rfl
theorem copied : copyTrace 2 false trace = trace := by rfl
theorem counted : depth 2 false trace = 1 := by rfl

theorem copy_identity {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) : copyTrace a v t = t := by
  induction t with
  | stop x vx => rfl
  | step x y vx vy child ih => simp only [copyTrace, ih]; rfl
