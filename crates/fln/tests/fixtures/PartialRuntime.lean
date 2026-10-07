prelude
import Init.Notation
namespace PartialRuntime
partial def count (n : Nat) : Nat := if Nat.beq n 0 then 42 else count (Nat.sub n 1)
partial def choose (α : Type) (x : α) (n : Nat) : α := if Nat.beq n 0 then x else choose α x (Nat.sub n 1)
mutual
partial def first (n : Nat) : Nat := if Nat.beq n 0 then 17 else second (Nat.sub n 1)
partial def second (n : Nat) : Nat := if Nat.beq n 0 then 42 else first (Nat.sub n 1)
end
partial def spin (n : Nat) : Nat := spin n
def lazy (n : Nat) : Nat := if Nat.beq n 0 then 42 else spin n
end PartialRuntime
