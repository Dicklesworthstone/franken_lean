def withCapture (n : Nat) : Nat :=
  let add (x y : Nat) : Nat := n + x + y;
  add 2 3

def nested (n : Nat) : Nat :=
  let outer (x : Nat) : Nat :=
    let inner (y : Nat) : Nat := n + x + y;
    inner 2;
  outer 3

def dependent (A : Type) (x : A) : A :=
  let identity {B : Type} (y : B) : B := y;
  identity x

theorem captured : withCapture 37 = 42 := by rfl
theorem nestedResult : nested 37 = 42 := by rfl
theorem identityResult : dependent Nat 42 = 42 := by rfl
