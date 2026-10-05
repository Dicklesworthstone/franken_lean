def sumAll {α : Type} [Add α] [OfNat α 0] (xs : List α) : α := xs.foldl (· + ·) 0
#eval sumAll [1, 2, 3]
