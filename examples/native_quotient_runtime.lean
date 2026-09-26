-- Native quotient construction, elimination, partial application and captures.
def Q : Type := Quot (fun (a b : Nat) => a = b)

def twice (f : Q -> Nat) (q : Q) : Nat := f q + f q

#eval let make : Nat -> Q := Quot.mk (fun (a b : Nat) => a = b);
  let read : Q -> Nat := Quot.lift (fun (n : Nat) => n) (fun (a b : Nat) (h : a = b) => h);
  twice read (make 21)
