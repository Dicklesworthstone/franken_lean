def main : IO Unit := do
  let t1 <- IO.asTask (pure (2 + 3) : IO Nat)
  let t2 <- IO.asTask (pure (10 * 4) : IO Nat)
  let a <- IO.ofExcept t1.get
  let b <- IO.ofExcept t2.get
  IO.println s!"sum {a + b}"
  let chained := Task.spawn (fun _ => 6 * 7) |>.map (· + 1)
  IO.println s!"chained {chained.get}"
#eval main
