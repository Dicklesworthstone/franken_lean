# Checked function-valued recursive children

A constructor field may be a dependent function returning the same inductive
family, with the original parameters and universes and potentially changing
indices. Its argument domains cannot contain the family. For example:

```lean
inductive Branching where
  | leaf (value : Nat)
  | node (children : Nat -> Branching)
```

The `node` branch of induction receives `children : Nat -> Branching` and
`ih : forall n, motive (children n)`. Dependent arguments and result indices are
preserved. Ordinary case analysis and `match` open the same recursor telescope
but do not expose induction hypotheses to source proofs or instance search.

The candidate generator and the independent checker build the corresponding
function-valued induction hypotheses and recursive reduction rules separately.
The checker relocates ambient bounds without moving the recursive function's
own binders. It derives the recursive/reflexive flags from constructor types,
checks field universe bounds, and rejects negative occurrences and forged rules.
K1 independently regenerates the candidate using its existing implementation.
No primary-kernel change or new axiom is needed.

This enables accessibility-shaped propositions:

```lean
inductive Accessible (A : Type) (R : A -> A -> Prop) : A -> Prop where
  | intro (x : A) (next : forall y : A, R y x -> Accessible A R y) : Accessible A R x
```

Its singleton eliminator can compute dependent data: the data field `x` is
exposed in the result index and `next` is a proof. An existential-style predicate
with a hidden data field still cannot eliminate into data. This is checked by
both engines, not asserted by the caller or a metadata flag.

Run `fln check-source --json examples/native_function_children.lean` to check
construction, matching, genuine function-valued induction, and a dependent
accessibility fold, including a computation through supplied accessibility.

This is single-family strictly positive function recursion, not nested or mutual
inductive support. Automatic source self-calls on `children argument`, general
well-founded termination synthesis, and `termination_by` are separate layers.
Kernel conversion and source admission are exercised; full execution-backend,
Reference syntax/generated-name parity and the pinned Prelude council are not
established by the scoped tests.
