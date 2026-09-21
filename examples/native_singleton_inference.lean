-- Field equalities infer non-class singleton records, including record-valued functions.
structure Wrap where
  value : Nat

def recover {w : Wrap} (h : w.value = 7) : Wrap := w
def inferred : Wrap := recover (rfl : 7 = 7)
theorem verified : inferred.value = 7 := by rfl

def recoverFunction {f : Nat -> Wrap} (h : ∀ n : Nat, (f n).value = n) : Nat -> Wrap := f
def inferredFunction : Nat -> Wrap := recoverFunction (fun n : Nat => (rfl : n = n))
theorem computed : (inferredFunction 11).value = 11 := by rfl
