namespace Logic

def wrap (p : Prop) : Prop := p

@[simp] theorem unwrap (p : Prop) : wrap p ↔ p := by
  constructor
  · intro h; exact h
  · intro h; exact h

end Logic

theorem normalized (p : Prop) : Logic.wrap (Logic.wrap p) = p := by simp

theorem transport (P Q : Prop) (F : Prop -> Prop) (h : P ↔ Q) (q : F Q) : F P := by
  simp only [h]
  exact q

theorem localTransport (P Q : Prop) (h : P ↔ Q) (p : P) : Q := by
  rw [h] at p
  exact p

theorem conditional (P Q R : Prop) (h : R -> (P ↔ Q)) (r : R) (q : Q) : P := by
  simp only [h, r]
  exact q
