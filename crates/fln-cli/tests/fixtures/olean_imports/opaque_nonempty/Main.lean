import Init.Prelude

structure P where
  x : Nat

instance : Nonempty P := ⟨⟨0⟩⟩

opaque p : P
