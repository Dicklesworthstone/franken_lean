class Pure (f : Type -> Type) where
  pure : {A : Type} -> A -> f A

class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B

def Id (A : Type) : Type := A
instance idPure : Pure Id := { pure := fun a => a }
instance idBind : Bind Id := { bind := fun a k => k a }

def mapping {M : Type -> Type} [Pure M] [Bind M]
    {A B : Type} (f : A -> B) (action : M A) : M B := do
  let x ← action
  return (f x)

def answer : Id Nat := do
  let n ← mapping (M := Id) (fun (x : Nat) => x + 1) 40
  return (n + 1)

theorem answerValue : answer = 42 := by rfl
