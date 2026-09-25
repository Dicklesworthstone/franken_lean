-- Native source profile: static parameters can follow ordinary runtime values.
class Pure (f : Type -> Type) where
  pure : {A : Type} -> A -> f A
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B

def Id (A : Type) : Type := A
instance idPure : Pure Id := { pure := fun a => a }
instance idBind : Bind Id := { bind := fun a k => k a }

def keep (ignored : Nat) {A : Type} (x : A) : A := x

def step (ignored : Nat) {M : Type -> Type} [Pure M] [Bind M]
    (action : M Nat) : M Nat := do
  let x ← action
  return (x + 1)

#eval keep 9 (step 0 (M := Id) 41 : Id Nat)
