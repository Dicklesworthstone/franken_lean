structure Package where
  carrier : Type
  value : carrier

def wrapped : Package := Package.mk Nat 23

theorem wrapped_ok : Package.value wrapped = 23 := by rfl

class Choice (A : Type) where
  value : A

instance natChoice : Choice Nat := Choice.mk 11

instance functionChoice {A : Type} [Choice A] : Choice (Nat -> A) :=
  Choice.mk (fun x => Choice.value)

def chosen : Nat -> Nat -> Nat := Choice.value

theorem chosen_ok : chosen 4 5 = 11 := by rfl
