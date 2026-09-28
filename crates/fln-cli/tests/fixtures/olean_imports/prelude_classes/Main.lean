import Init.Prelude

def d : Nat := Inhabited.default

theorem dec : Decidable.decide ((2 : Nat) = 2) = true := rfl

def b : Bool := (3 : Nat) == 3

theorem b_true : ((3 : Nat) == 3) = true := rfl
