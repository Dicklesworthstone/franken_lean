structure Package where
  carrier : Type
  value : carrier

theorem successor_injective (a b : Nat) (h : Nat.succ a = Nat.succ b) : a = b := by
  injection h with predecessor
  exact predecessor

theorem package_types (A B : Type) (a : A) (b : B)
    (h : Package.mk A a = Package.mk B b) : A = B := by
  injection h with types values
  exact types

theorem package_values (A B : Type) (a : A) (b : B)
    (h : Package.mk A a = Package.mk B b) : HEq a b := by
  injection h with types values
  subst types
  exact heq_of_eq values

inductive Chain where
  | nil
  | cons (head : Nat) (tail : Chain)

theorem disjoint (h : true = false) : 0 = 1 := by
  contradiction

theorem nested (a b : Nat)
    (h : Chain.cons a Chain.nil = Chain.cons b (Chain.cons 7 Chain.nil)) : 0 = 1 := by
  contradiction

theorem enormous
    (h : 340282366920938463463374607431768211456 = 340282366920938463463374607431768211457) : 0 = 1 := by
  contradiction

theorem after_substitution (x y : Nat) (h : Nat.succ x = Nat.succ y) (hy : y = 0) : x = 0 := by
  injection h with predecessors
  subst predecessors
  exact hy
