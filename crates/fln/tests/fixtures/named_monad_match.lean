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

theorem namedSome : chooseNamed (some 42) = (42 : Nat) := by rfl
theorem namedNone : chooseNamed none = (0 : Nat) := by rfl
theorem plainSome : choosePlain (some 42) = (42 : Nat) := by rfl
theorem ascribedSome : chooseAscribed (some 42) = (42 : Nat) := by rfl
theorem higherUniverse : chooseType (some Bool) = Bool := by rfl
theorem higherDefault : chooseType none = Nat := by rfl
