-- Native recursive data uses checked constructor layouts and shared IHs.
inductive Chain where
  | nil
  | cons (head : Nat) (tail : Chain)

def make (n : Nat) : Chain := match n with
  | .zero => Chain.nil
  | .succ k => Chain.cons n (make k)

def sum (xs : Chain) (acc : Nat) : Nat := match xs with
  | .nil => acc
  | .cons head tail =>
    let next : Nat -> Nat := sum tail;
    next (head + acc)

theorem two_values : sum (Chain.cons 17 (Chain.cons 25 Chain.nil)) 0 = 42 := by rfl

def answer : Nat := sum (make 8) 6
