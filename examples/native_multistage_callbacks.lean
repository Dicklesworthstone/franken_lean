structure StageResult where
  value : Nat

def pipeline (offset : Nat) : Nat :=
  let first : Nat -> Nat -> Nat -> StageResult := (by
    intro x
    let a := offset + x
    intro y
    let b := a + y
    intro z
    exact StageResult.mk (b + z))
  let second := first 1
  let third := second 2
  let result := third 3
  result.value

#eval pipeline 36
