theorem reflexive (A : Type) (x : A) : x = x := by dsimp only
theorem trivial : True := by dsimp only
def Bottom : Prop := False
theorem eliminateFalse (P : Prop) (h : Bottom) : P := by dsimp only [Bottom] at h
def eliminateData (A : Type) (h : Bottom) : A := by dsimp only [Bottom] at h
