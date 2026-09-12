# Structural recursion through dependent pattern matrices

Native source definitions can recurse through a root match with multiple
inputs and nested payload patterns. The first discriminant is the explicit
header parameter that decreases; recursive calls use its immediate recursive
constructor fields. Other inputs and trailing accumulators can change.

```lean
inductive Seq (A : Type) where
  | nil
  | cons (value : A) (tail : Seq A)

def zipSum (xs ys : Seq Nat) : Seq Nat := match xs, ys with
  | .nil, _ => Seq.nil
  | .cons x xt, .nil => Seq.nil
  | .cons x xt, .cons y yt => Seq.cons (x + y) (zipSum xt yt)
```

The implementation also handles correlated indexed inputs. With the usual
`Vec A n` definition, the second vector's constructor refines the same length
as the first, and its tail is transported before the recursive call:

```lean
def zipVec (n : Nat) (xs ys : Vec Nat n) : Vec Nat n := match xs, ys with
  | .nil, .nil => Vec.nil
  | .cons k x xt, .cons j y yt => Vec.cons k (x + y) (zipVec k xt yt)
```

Generic fixed parameters, dependent index telescopes, fixed-index inputs such
as `Walk 7`, multiple immediate children, changing accumulators, and partial
applications after the decreasing child are covered by source tests. Nested
patterns on another input or on a nonrecursive payload work; in particular,
a nested `Seq Nat` payload of `Seq (Seq Nat)` is not misclassified as a child
of the outer family. Results can be proved for all inputs by ordinary induction,
not only evaluated at concrete constructors.

## Construction and checking boundary

The matrix's outer structural split is kept at the original parameter, rather
than hidden behind a generated let. All input bindings inside its alternatives
are elaborated in the generalized recursive context. Thus a changed accumulator
or second list does not accidentally remain captured from the initial call.
The original discriminant's source name is rebound to the current constructor.
Pattern names shadow it only where the source explicitly introduces that name.

Compiler-generated pattern aliases retain checked let bindings while exposing
their exact local referents to structural-call recognition. They never reduce
arbitrary user expressions to pretend a call is decreasing. In particular,
`recur (k + 0)` is outside this lane even when `recur k` is permitted. Incorrect
annotations on ignored inputs and unused aliases remain actual kernel typing
obligations.

A later indexed split can generalize both the first child's type and its
recursor hypothesis. Private, request-local names track the real hypotheses
through that reconstruction; the current local context determines their scope.
Calls are lowered before those branch binders close, so correlated vector tails
do not lose their identity inside nested eliminator lambdas. The final term uses
actual admitted recursion hypotheses, not self constants or additional axioms.

Those compiler-only hypotheses are excluded from ordinary assumption search,
contradiction, substitution-witness search, and instance synthesis. They cannot
be used by a source `by assumption` in place of an explicit decreasing call.
Their private names are not source identifier spellings. Ordinary `cases` still
introduces no source-visible induction hypotheses. User-supplied source values,
annotations, and unresolved recursive markers remain subject to final checking.

No kernel or independent-checker rule changes in this increment. Both engines
still check the complete declaration. Matrix expansion, syntax copying, alias
resolution and recursive-call traversal consume the existing work budget.
Resource stops and failed file suffixes expose no successor environment.

## Current limits

An explicit result type and a root constructor match remain required. The first
matrix column must scrutinize the decreasing header parameter and contain its
constructor split; this implementation does not search other columns for a
termination argument. It does not justify recursion on grandchildren exposed
by nested patterns, arbitrary equivalent expressions, or another input's child.
Grandchild/course-of-values, mutual, and general well-founded recursion remain
separate capabilities. Existing restrictions on redundant rows, unsupported
patterns and inductive families remain in force.

These results concern source admission and checked conversion, not general
execution-backend parity or full Reference conformance. Run the installed
source-check path:

```bash
fln check-source --json examples/native_matrix_recursion.lean
```

The example checks 17 commands and seven theorems, including list/vector zipping,
changing accumulators, constrained recursion, nested payload patterns, generic
function parameters, and a universal induction proof. The installed-CLI
regression rejects a false theorem in a later file without partial success and
then rechecks the original prefix.
