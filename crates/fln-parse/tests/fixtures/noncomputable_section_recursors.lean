inductive T where | a | b (x : T)
noncomputable section
def count (t : T) : Nat := T.rec (motive := fun _ => Nat) 0 (fun _ ih => ih + 1) t
theorem computed : count (T.b T.a) = 1 := by rfl
end
