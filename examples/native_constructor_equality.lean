structure Pair where
  first : Nat
  second : Nat

inductive NoEvidence : Prop where

theorem predecessor (x y : Nat) (h : Nat.succ x = Nat.succ y) : x = y := by
  injection h with predecessor_eq
  exact predecessor_eq

theorem second_field (a b c d : Nat) (h : Pair.mk a b = Pair.mk c d) : b = d := by
  injection h with first_eq second_eq
  exact second_eq

theorem nested_clash (n : Nat) (h : Nat.succ (Nat.succ n) = Nat.succ 0) : 0 = 1 := by
  contradiction

def huge_clash
    (h : 340282366920938463463374607431768211456 = 340282366920938463463374607431768211455) : Nat := by
  contradiction

theorem negated_field (x y : Nat) (h : Nat.succ x = Nat.succ y)
    (different : (x = y) -> NoEvidence) : 0 = 1 := by
  contradiction

theorem transport (A : Type) (P : A -> Prop) (x y : A)
    (hx : P x) (h : Inhabited.mk x = Inhabited.mk y) : P y := by
  injection h with same
  subst same
  exact hx
