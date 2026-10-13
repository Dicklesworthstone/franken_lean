inductive Trace (A : Type) (P : A -> Type) : forall a : A, P a -> Type where
  | stop (a : A) (v : P a) : Trace A P a v
  | step (a b : A) (v : P a) (w : P b) (child : Trace A P a v) : Trace A P b w

def copyTrace {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) : Trace A P a v := match t with
  | .stop x vx => Trace.stop x vx
  | .step x y vx vy child => Trace.step x y vx vy (copyTrace x vx child)

theorem copy_identity {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) : copyTrace a v t = t := by
  induction t with
  | stop x vx => rfl
  | step x y vx vy child ih => simp only [copyTrace, ih]

theorem copy_step {A : Type} {P : A -> Type} (a b : A) (v : P a) (w : P b)
    (child : Trace A P a v) (ih : copyTrace a v child = child) :
    copyTrace b w (Trace.step a b v w child) = Trace.step a b v w child := by
  simp only [copyTrace, ih]
