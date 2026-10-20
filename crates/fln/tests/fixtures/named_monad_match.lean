prelude
import Init.Prelude

-- A source-owned monad against the actual imported Prelude interfaces.
def HintId.{u} (A : Type u) : Type u := A
instance hintMonad.{u} : Monad.{u,u} HintId.{u} where
  pure x := x
  bind x f := f x
  map f x := f x

def chooseNamed (o : Option Nat) : HintId Nat :=
  bind (m := HintId) (match o with | some n => pure n | none => pure 0) (fun y => pure y)
def choosePlain (o : Option Nat) : HintId Nat :=
  bind (match o with | some n => pure n | none => pure 0) (fun y => pure y)
def chooseAscribed (o : Option Nat) : HintId Nat :=
  bind (m := HintId) ((match o with | some n => pure n | none => pure 0) : HintId Nat) (fun y => pure y)
def chooseType (o : Option Type) : HintId Type :=
  bind (m := HintId) (match o with | some A => pure A | none => pure Nat) (fun A => pure A)

-- `=` (Init/Core) and the `rfl` tactic (Init/Tactics) are not available under this header;
-- the pin answers "expected token" for them. `Eq` and the term `rfl` are in Init.Prelude.
theorem namedSome : Eq (chooseNamed (some 42)) (42 : Nat) := rfl
theorem namedNone : Eq (chooseNamed none) (0 : Nat) := rfl
theorem plainSome : Eq (choosePlain (some 42)) (42 : Nat) := rfl
theorem ascribedSome : Eq (chooseAscribed (some 42)) (42 : Nat) := rfl
theorem higherUniverse : Eq (chooseType (some Bool)) Bool := rfl
theorem higherDefault : Eq (chooseType none) Nat := rfl
