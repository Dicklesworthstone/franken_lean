inductive Choice (P Q : Prop) : Prop where
  | left (proof : P)
  | right (proof : Q)

theorem alternatives (p : Prop) [Decidable p] : Choice p (Not p) := by
  by_cases h : p
  · exact Choice.left h
  · exact Choice.right h

def flag (p : Prop) [Decidable p] : Nat := by
  by_cases h : p
  · exact 7
  · exact 9

theorem flag_yes : flag True = 7 := by rfl
theorem flag_no : flag False = 9 := by rfl

theorem scoped (p q : Prop) [Decidable p] [Decidable q] (saved : p) : p := by
  by_cases h : q
  · by_cases hp : p <;> exact saved
  · exact saved

theorem negation (p : Prop) [Decidable p] (refute : p -> False) : Not p := by
  by_cases p
  · exact fun ignored => refute h
  · exact h

structure Package where
  carrier : Type
  value : carrier

def boxed : Package := by
  by_cases h : True
  · exact { carrier := Nat, value := 23 }
  · exact { carrier := Bool, value := false }

theorem boxed_carrier : boxed.carrier = Nat := by rfl