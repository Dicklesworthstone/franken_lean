def work (n : Nat) : Nat := match n with
  | .zero => 0
  | .succ k => work k + 1

def evidence (n : Nat) : 0 = 0 :=
  let discarded : Nat := work n
  by rfl

def keep (h : 0 = 0) (n : Nat) : Nat := n

-- The million-step proof computation is irrelevant after admission.
#eval keep (evidence 1000000) 42
