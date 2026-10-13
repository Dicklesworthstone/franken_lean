syntax "picked! " num : term
macro_rules | `(picked! $n:num) => `($n)

namespace Choice
scoped macro_rules | `(picked! 0) => `((10 : Nat))
end Choice

theorem closed : picked! 0 = (0 : Nat) := rfl

open scoped Choice in
theorem active : picked! 0 = (10 : Nat) := rfl

theorem restored : picked! 0 = (0 : Nat) := rfl
