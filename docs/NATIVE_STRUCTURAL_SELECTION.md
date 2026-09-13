# Structural argument selection

Equation-style definitions and root pattern matrices try explicit input parameters
in source-column order until one compiles every recursive call into a checked
child hypothesis. The decreasing argument no longer has to be the first column:

```lean
def add : Nat -> Nat -> Nat
  | x, .zero => x
  | x, .succ k => Nat.succ (add x k)

def accumulate : Nat -> Nat -> Nat
  | acc, .zero => acc
  | acc, .succ k => accumulate (acc + 1) k
```

Changing the decision-tree split does not permute the declaration's argument
order, row priority, or simultaneous pattern bindings. Earlier matched inputs
are generalized when they are not uniform parameters of the inductive family.
Actual uniform parameters, including their type dependencies, remain fixed.
Indexed child arguments still carry their original checked index equations.

Each candidate receives the same original elaboration state. Failed candidates
publish no assignments, generated names, local proofs, instance goals, or matrix
state. Work already spent is not refunded. Resource failures and ordinary source
errors are not candidate failures and are not retried to hide an invalid program.
Only failure to use a chosen structural argument licenses another candidate.
Every call, including calls in unused values and annotations, must decrease on
one globally selected input. Selecting a different input per call is not allowed.

Successful candidates use the existing recursor lowering and both final checking
engines. There is no recursive axiom or additional termination/admission rule.
The chosen root must be an actual explicit header parameter. The result type must
be written, and structural calls still target immediate constructor children.
This does not implement general lexicographic or well-founded recursion,
`termination_by`, mutual recursion, or inference from a computed discriminant.

Run `fln check-source --json examples/native_structural_selection.lean` for
computations and a universal induction proof over a later-selected argument.
