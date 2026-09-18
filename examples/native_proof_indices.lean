class Evidence (P : Prop) (proof : P) where
  value : Nat

def reuse (P : Prop) (h k : P) [i : Evidence P h] : Evidence P k := inferInstance

theorem reused (P : Prop) (h k : P) [i : Evidence P h] :
  reuse P h k = i := by rfl

def newest (P : Prop) (h k : P) (first : Evidence P h) (second : Evidence P k) :
  Evidence P h := inferInstance

theorem newest_selected (P : Prop) (h k : P) (first : Evidence P h) (second : Evidence P k) :
  newest P h k first second = second := by rfl

def reuse_at (P : Nat -> Prop) (n : Nat) (h k : P n) [i : Evidence (P n) h] :
  Evidence (P n) k := inferInstance

theorem selected_at (P : Nat -> Prop) (n : Nat) (h k : P n) [i : Evidence (P n) h] :
  reuse_at P n h k = i := by rfl
