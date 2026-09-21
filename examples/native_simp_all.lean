-- Native fixed-point context simplification; no imports or runtime execution.
theorem localEvidence (P : Prop) (h : P) : P := by simp_all

theorem transported (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by
  simp_all only

theorem fixedPoint (P : Nat -> Prop) (f : Nat -> Nat) (x y z : Nat)
    (hp : P (f y)) (he : f x = z) (hxy : x = y) : P z := by
  simp_all only

theorem introduced (P : Prop) : P -> P := by
  intro h
  simp_all only

theorem computed : 2 + 3 = 5 := by simp_all only
