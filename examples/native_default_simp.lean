namespace Wrapper

def wrap.{u} {A : Sort u} (x : A) : A := x

@[simp] theorem unwrap.{u} {A : Sort u} (x : A) : wrap x = x := by rfl

theorem nested (n : Nat) : wrap (wrap n) = n := by simp

theorem universe (A : Type) : wrap A = A := by simp []

end Wrapper

theorem transported (P : Nat -> Prop) (n : Nat) (h : P (Wrapper.wrap n)) : P n := by
  simp at h
  exact h

theorem selected (f : Nat -> Nat) (n : Nat) (h : f n = n) : Wrapper.wrap (f n) = n := by
  simp [h]

attribute [-simp] Wrapper.unwrap

theorem explicitOnly (n : Nat) : Wrapper.wrap n = n := by
  simp only [Wrapper.unwrap]
