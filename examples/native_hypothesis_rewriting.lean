-- These are ordinary proof terms checked by K1 and the independent checker.
-- fln check-source --json examples/native_hypothesis_rewriting.lean

def hypWrap (n : Nat) : Nat := n

theorem hypForward (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by
  rw [h] at hx
  exact hx

theorem hypReverse (P : Nat -> Prop) (x y : Nat) (h : x = y) (hy : P y) : P x := by
  rewrite [← h] at hy
  exact hy

theorem hypMany (f : Nat -> Nat) (h : forall n : Nat, f n = n)
    (P : Nat -> Prop) (p : P (f 1)) (q : P (f 2)) : P 2 := by
  rewrite [h] at p q
  exact q

-- A conditional rewrite does not silently assume its premise.
theorem hypConditional (R : Prop) (r : R) (x y : Nat) (h : R -> x = y)
    (P : Nat -> Prop) (hx : P x) : P y := by
  rewrite [h] at hx
  exact hx
  exact r

-- A later dependent hypothesis keeps its original, well-typed identity.
theorem hypDependent (P : Nat -> Prop) (x y : Nat) (h : x = y)
    (hx : P x) (Q : P x -> Prop) (q : Q hx) : Q hx := by
  rewrite [h] at hx
  exact q

-- Simplification uses only the selected definition, equality, and premise.
theorem hypSimplify (R : Prop) (r : R) (x y : Nat) (h : R -> x = y)
    (P : Nat -> Prop) (hx : P (hypWrap (hypWrap x))) : P y := by
  simp only [hypWrap, h, r] at hx
  exact hx

def hypCast (A B : Type) (h : A = B) (x : A) : B := by
  rewrite [h] at x
  exact x
