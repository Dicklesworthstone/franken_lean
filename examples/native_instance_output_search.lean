-- A recursive instance with a fresh semi-output used to evade cycle detection.
class Choice (A : semiOutParam Type) where
  value : A

instance (priority := 500) baseChoice : Choice Nat := Choice.mk 7
instance (priority := 2000) recursiveChoice {A : Type} [c : Choice A] : Choice Nat := Choice.mk 9

class Result where
  value : Nat

instance selected {A : Type} [c : Choice A] : Result := Result.mk 1

def result : Result := inferInstance
theorem resultChecked : result.value = 1 := by rfl

-- Unknown outputs infer a dictionary, while known semi-outputs still filter it.
class Convert (A : semiOutParam Type) where
  value : A

instance (priority := 500) naturalConversion : Convert Nat := Convert.mk 8
instance (priority := 2000) booleanConversion : Convert Bool := Convert.mk true

def natural : Convert Nat := inferInstance
theorem filterPreserved : natural.value = 8 := by rfl
