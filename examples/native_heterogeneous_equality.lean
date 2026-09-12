structure Certificate where
  carrier : Type
  value : carrier
  valid : value = value

theorem reflexive (A : Type) (a : A) : HEq a a := by rfl

theorem type_identity (A B : Type) (a : A) (b : B) (h : HEq a b) : A = B :=
  type_eq_of_heq h

theorem symmetric (A B : Type) (a : A) (b : B) (h : HEq a b) : HEq b a :=
  HEq.symm h

theorem transitive (A B C : Type) (a : A) (b : B) (c : C)
    (h : HEq a b) (k : HEq b c) : HEq a c := HEq.trans h k

theorem endpoints (x y : Nat) (h : HEq x y) : y = x := by
  subst h
  rfl

def recover (A B : Type) (a : A) (b : B) (h : HEq a b) : A := by
  subst h
  exact b

theorem predicate_transport (A B : Type) (a : A) (b : B)
    (h : HEq a b) (P : forall T : Type, T -> Prop) (pa : P A a) : P B b := by
  subst h
  exact pa

theorem proof_fields (A B : Type) (a : A) (b : B) (pa : a = a) (pb : b = b)
    (h : Certificate.mk A a pa = Certificate.mk B b pb) : HEq pa pb := by
  injection h with types values proofs
  exact proofs

theorem impossible
    (h : HEq 340282366920938463463374607431768211456 340282366920938463463374607431768211457) : 0 = 1 := by
  contradiction