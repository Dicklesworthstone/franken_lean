-- These proofs use the original Nat recursors, not the compiler's lowering.
def sumTo (n : Nat) : Nat := match n with
  | .zero => n
  | .succ k => sumTo k + n

def sumTail (n acc : Nat) : Nat := match n with
  | .zero => acc
  | .succ k => sumTail k (acc + n)

def factorial (n : Nat) : Nat := match n with
  | .zero => 1
  | .succ k => factorial k * n

def copies (s : String) (n : Nat) : String := match n with
  | .zero => s
  | .succ k => copies s k ++ s

theorem sumTo_ok : sumTo 10 = 55 := by rfl
theorem sumTail_ok : sumTail 10 2 = 57 := by rfl
theorem factorial_ok : factorial 6 = 720 := by rfl
