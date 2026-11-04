prelude
import Init.Data.Repr

def mapping {M : Type -> Type} [Pure M] [Bind M]
    {A B : Type} (f : A -> B) (action : M A) : M B := do
  let x ← action
  return (f x)

def answer : Id Nat := do
  let n ← mapping (M := Id) (fun (x : Nat) => x + 1) 40
  return (n + 1)

theorem answerValue : answer = 42 := by rfl
