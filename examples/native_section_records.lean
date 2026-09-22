namespace Demo
section
variable (A : Type u)
structure Box where
  value : A
  echo (x : A) : A := x
end
section
variable {A : Type u} (fallback : A)
structure Config where
  value : A := fallback
end
end Demo

def config : Demo.Config 41 := {}
def box : Demo.Box Nat := { value := config.value }
theorem answer : box.echo 42 = 42 := by rfl
