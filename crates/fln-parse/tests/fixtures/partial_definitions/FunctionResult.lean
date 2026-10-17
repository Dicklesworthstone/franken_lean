
def FunctionResult (A : Type) : Type := Nat -> A
partial def keep {A : Type} (fallback : FunctionResult A) (n : Nat) : FunctionResult A :=
  if n == 0 then fallback else keep fallback (n - 1)
#eval keep (fun n => n + 30) 3 12
