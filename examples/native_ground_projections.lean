-- Ground field access is compiled from checked types, not constructor-name guesses.
structure Box (A : Type) where
  value : A

structure Entry (A : Type) where
  item : Box A
  count : Nat

def decorate (e : Entry String) : Entry String :=
  { e with item := { e.item with value := e.item.value ++ "!" } }

def score (e : Entry String) : Nat := String.length e.item.value + e.count

def entry : Entry String := decorate { item := { value := "hello" }, count := 36 }

def numbers : List (Box Nat) := [Box.mk 19, Box.mk 23]

theorem checked : entry.count = 36 := by rfl

#eval score entry
#eval List.foldl Nat.add 0 (List.map Box.value numbers)
