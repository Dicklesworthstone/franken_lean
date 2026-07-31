#eval #[1, 2, 3].push 4
#eval (#[10, 20, 30].set! 1 99).toList
#eval #[1, 2, 3, 4].map (· * 2) |>.foldl (· + ·) 0
#eval (Array.range 6).filter (· % 2 == 0)
