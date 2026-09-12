-- Checked local facts, nested proofs and transparent tactic lets.
theorem local_identity (A : Type) (a : A) : a = a := by
  have h : a = a := by
    have inner : a = a := rfl
    exact inner
  exact h

theorem successor_congruence (n m : Nat) (h : n = m) : Nat.succ n = Nat.succ m := by
  have same := h
  rw [same]

theorem quantified (n : Nat) : n = n := by
  have all : forall x : Nat, x = x := by
    intro x
    rfl
  exact all n

def localSeven : Nat := by
  let n := 3
  let n := n + 4
  exact n

theorem localSeven_ok : localSeven = 7 := by rfl

theorem split (b : Bool) : b = b := by
  have : b = b := by
    cases b with
    | false => rfl
    | true => rfl
  exact this

def copy (n : Nat) : Nat := match n with
  | .zero => 0
  | .succ k => Nat.succ (copy k)

theorem copy_ok (n : Nat) : copy n = n := by
  have all : forall k : Nat, copy k = k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => simp only [copy, ih]
  exact all n

theorem transport (n m : Nat) (eq : n = m) (P : Nat -> Prop) (h : P n) : P m := by
  have saved : P n := by exact h
  subst eq
  exact saved

structure Package where
  carrier : Type
  value : carrier

def builtValue : Nat := by
  let p : Package := { value := 7, carrier := Nat }
  exact p.value

theorem built_ok : builtValue = 7 := by rfl
