def readQuot (q : Quot (fun (a b : Nat) => a = b)) : Nat :=
  Quot.lift (fun (n : Nat) => n) (fun (a b : Nat) (h : a = b) => h) q

theorem readQuot_mk (n : Nat) :
  readQuot (Quot.mk (fun (a b : Nat) => a = b) n) = n := by rfl

theorem related_representatives {A : Sort u} {r : A -> A -> Prop} {a b : A}
  (h : r a b) : Quot.mk r a = Quot.mk r b := Quot.sound h

def arrowFromQuot (q : Quot (fun (a b : Nat) => True)) : Type :=
  Quot.lift (fun (n : Nat) => Nat -> Nat)
    (fun (a b : Nat) (h : True) => rfl) q

def quotientFunction : arrowFromQuot (Quot.mk (fun (a b : Nat) => True) 0) :=
  fun (n : Nat) => n

theorem quotientFunction_works (n : Nat) : quotientFunction n = n := by rfl

theorem quotient_induction (q : Quot (fun (a b : Nat) => a = b)) : q = q :=
  @Quot.ind Nat (fun (a b : Nat) => a = b)
    (fun (x : Quot (fun (a b : Nat) => a = b)) => x = x)
    (fun (a : Nat) => rfl) q
