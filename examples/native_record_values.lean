structure Package where
  carrier : Type
  value : carrier

def wrapped : Package := { value := 23, carrier := Nat }
def unpack (p : Package) : p.carrier := p.value
theorem wrapped_ok : wrapped.value = 23 := by rfl
theorem unpack_ok : unpack wrapped = 23 := by rfl

class Choice (A : Type) where
  value : A

instance selected : Choice Nat := { value := 11 }
def different : Choice Nat := { value := 7 }
theorem explicit_receiver : different.value = 7 := by rfl
theorem selected_receiver : Choice.value = 11 := by rfl
