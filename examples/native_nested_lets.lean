structure NestedResult where
  value : Nat

def pipeline (offset : Nat) : Nat :=
  let first : Nat -> Nat -> Nat -> NestedResult := (fun x =>
    let a := offset + x
    fun y =>
      let b := a + y
      fun z =>
        let result : NestedResult := { value := let c := b + z; c }
        result)
  let second := first 1
  let third := second 2
  let result := third 3
  result.value

#eval pipeline 36
