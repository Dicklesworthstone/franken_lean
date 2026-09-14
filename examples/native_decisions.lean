-- Constructive decisions, including user-defined predicates and local instances.
inductive Ready : Prop where | proof
instance readyDecision : Decidable Ready := Decidable.isTrue Ready.proof

def choose {A : Type} (p : Prop) [Decidable p] (yes no : A) : A := ite p yes no

def useEvidence (p : Prop) [Decidable p] (good : p -> Nat) (fallback : Nat) : Nat :=
  dite p good (fun unused => fallback)

theorem chosen : choose Ready 17 19 = 17 := by rfl
theorem refuted : choose False 17 19 = 19 := by rfl
theorem proof_used : useEvidence Ready (fun proof => 23) 0 = 23 := by rfl
theorem decided : decide Ready = true := by rfl
theorem negated : decide (Not Ready) = false := by rfl
theorem double_negated : decide (Not (Not Ready)) = true := by rfl
