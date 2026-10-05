def f (n : Nat) : Nat := g n + 1
where g (m : Nat) : Nat := m * 2
#eval f 4
