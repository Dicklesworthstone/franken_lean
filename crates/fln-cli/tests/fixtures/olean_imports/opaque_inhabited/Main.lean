import Init.Prelude

structure P where
  x : Nat

instance : Inhabited P := ⟨⟨0⟩⟩

opaque p : P

opaque s : Nat := 5

axiom mine : 1 = 1

theorem uses : 1 = 1 := mine
