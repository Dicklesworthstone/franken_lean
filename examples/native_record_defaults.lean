structure Config where
  base : Nat := 3
  twice : Nat := base + base
  transform (x : Nat) : Nat := x + twice

def standard : Config := {}
def custom : Config := { base := 7 }
def copied := { custom with base := 20 }

theorem standard_ok : standard.twice = 6 := by rfl
theorem custom_ok : custom.twice = 14 := by rfl
theorem copied_ok : copied.twice = 14 := by rfl
theorem method_ok : custom.transform 2 = 16 := by rfl

class Choice where
  value : Nat := 11

instance nativeChoice : Choice := {}
def selected : Nat := Choice.value
theorem selected_ok : selected = 11 := by rfl
