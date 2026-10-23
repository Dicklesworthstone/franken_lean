prelude
import Init.Core
-- fln-5efd: the numeral's expected type `b.carrier` is `Nat` only after unfolding the plain
-- (semireducible) `def b`, which the pin's instance resolution does not do.
structure Carrier where
  carrier : Type
structure Value (A : Type) where
  value : A
structure Both extends Carrier, Value carrier where
  tag : Nat
def b : Both := { carrier := Nat, value := 31, tag := 37 }
theorem t : (b.toValue.value : Nat) = 31 := by rfl
