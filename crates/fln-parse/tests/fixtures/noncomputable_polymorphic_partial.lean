noncomputable def secret {A : Type} (x : A) : A := x
noncomputable section
variable {A : Type} (x : A)
mutual
partial def provider (n : Nat) : A := secret x
partial def consumer (n : Nat) : A := provider n
partial def clean (n : Nat) : A := x
end
end
theorem value : consumer 43 0 = 43 := by rfl
