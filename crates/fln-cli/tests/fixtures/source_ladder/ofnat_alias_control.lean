prelude
import Init.Core
-- fln-5efd control: `(31 : Nat)` is elaborated at `Nat`; only checking it against `MyNat`
-- unfolds the plain def, at default transparency. Accepted here as at the pin.
def MyNat := Nat
def z : MyNat := (31 : Nat)
