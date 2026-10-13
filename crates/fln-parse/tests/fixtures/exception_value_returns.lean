def choose (early : Bool) : Logged Nat := do
  let b : Bool ← do
    try
      note 1
      if early then return 42 else succeed true
    finally
      note 3
  note (if b then 5 else 6)
  return 7
#eval observed (choose true)
#eval observed (choose false)
