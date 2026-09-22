-- Both checkers see the real indices and equality proofs. Native casts retain
-- the checked value only when its source and destination layouts agree.
inductive Walk : Nat -> Type where
  | done (n : Nat) : Walk n
  | step (n : Nat) (child : Walk n) : Walk n

def copy (n : Nat) (w : Walk n) : Walk n :=
  match w with
  | .done k => Walk.done k
  | .step k child => Walk.step k (copy k child)

def depth (n : Nat) (w : Walk n) : Nat := by
  induction w with
  | done k => exact k
  | step k child ih => exact ih + 1

def transport (a b : Nat) (h : a = b) (x : Nat) : Nat :=
  Eq.rec (motive := fun k proof => Nat) x h

#eval transport 1 1 (by rfl) (depth 40 (copy 40 (Walk.step 40 (Walk.step 40 (Walk.done 40)))))
