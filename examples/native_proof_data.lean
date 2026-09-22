structure Certified where
  value : Nat
  proof : value = value := by rfl
  callback : (n : Nat) -> n = n -> Nat

def answer : Certified := {
  value := 40,
  callback := fun n h => n + 2
}

-- Both witnesses are checked, but neither proof executes in the native VM.
#eval answer.callback answer.value answer.proof
