instance (priority := 2000) preferredNat : Inhabited Nat := Inhabited.mk 7

instance constantFunction {A : Type} [Inhabited A] : Inhabited (Nat -> A) :=
  Inhabited.mk (fun x => default)

def selected : Nat := default
def nested : Nat -> Nat -> Nat := default

theorem selected_ok : selected = 7 := by rfl
theorem nested_ok : nested 2 3 = 7 := by rfl
