prelude
import Init.NotationExtra
example : ∃ n : Nat, n + 1 = 3 := ⟨2, rfl⟩
theorem two : ∃ x y : Nat, x + y = 3 := ⟨1, 2, rfl⟩
theorem grouped : ∃ (n : Nat) (m : Nat), n = m := ⟨0, 0, rfl⟩
theorem witness (p : Nat → Prop) (h : ∀ n, p n) : ∃ n, p n := ⟨0, h 0⟩
