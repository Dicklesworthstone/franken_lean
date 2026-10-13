noncomputable def secret : Nat := 41
noncomputable section
variable (offset : Nat)
mutual
partial def left (n : Nat) : Nat := if n == 0 then secret + offset else right (n - 1)
partial def right (n : Nat) : Nat := left n
partial def consumer (n : Nat) : Nat := right n
partial def clean (n : Nat) : Nat := offset + n
end
end
