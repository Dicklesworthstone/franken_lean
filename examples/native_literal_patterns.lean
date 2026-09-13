-- Compact natural patterns share the existing ordered match compiler.
def route : Nat -> Bool -> Nat
  | 0, _ => 7
  | n, true => n + 10
  | _, false => 9

theorem first : route 0 true = 7 := by rfl
theorem fallback : route 3 true = 13 := by rfl

def huge : Nat -> Nat
  | 340282366920938463463374607431768211456 => 17
  | _ => 19

theorem huge_equal : huge 340282366920938463463374607431768211456 = 17 := by rfl
theorem huge_other : huge 340282366920938463463374607431768211457 = 19 := by rfl

inductive Maybe (A : Type) where
  | none
  | some (value : A)

def payload : Maybe Nat -> Nat
  | .none => 0
  | .some 7 => 11
  | .some n => n

theorem payload_ok : payload (Maybe.some 7) = 11 := by rfl

def copy : Nat -> Nat
  | 0 => 0
  | .succ k => Nat.succ (copy k)

theorem copy_identity (n : Nat) : copy n = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [copy, ih]

theorem callback : (fun | 7 => 11 | _ => 13) 7 = 11 := by rfl
