def iterate (step : Nat -> Nat) (seed count : Nat) : Nat :=
  let rec go (acc remaining : Nat) : Nat :=
    match acc, remaining with
    | _, .zero => acc
    | _, .succ k => go (step acc) k
  go seed count

def answer : Nat := iterate (fun x : Nat => x + 2) 2 20

theorem answer_correct : answer = 42 := by rfl