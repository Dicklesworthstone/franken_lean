def compose (f g : Nat -> Nat) : Nat -> Nat := fun x => f (g x)
def addN (n : Nat) : Nat -> Nat := fun x => x + n
#eval compose (addN 5) (· * 2) 10
#eval (List.range 5).map (addN 100)
#eval (fun x y z => x * y + z) 2 3 4
