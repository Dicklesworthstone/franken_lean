def keep (xs : List Nat) : List Nat := match xs with
| whole@(x :: rest) => whole
| [] => []
theorem kept : keep [2, 3, 4] = [2, 3, 4] := by rfl
theorem empty : keep [] = [] := by rfl
def first : List Nat -> Nat | whole@(x :: _) => x | [] => 0
theorem head : first [7, 8] = 7 := by rfl
