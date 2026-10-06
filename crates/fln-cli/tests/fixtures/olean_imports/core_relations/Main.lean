prelude
import Init.Core
theorem gt : 3 > 2 := by decide
theorem ge : 3 ≥ 3 := by decide
theorem ge_ascii : 5 >= 4 := by decide
theorem le : 2 ≤ 3 := by decide
theorem ne : 2 ≠ 3 := by decide
theorem bne_true : (2 != 3) = true := rfl
theorem and_false : (true && false) = false := rfl
theorem or_true : (false || true) = true := rfl
theorem gt_from_lt (a b : Nat) (h : b < a) : a > b := h
