namespace Library
def wrap.{u} {A : Sort u} (x : A) : A := x
@[simp] theorem unwrap.{u} {A : Sort u} (x : A) : wrap x = x := by rfl
end Library
