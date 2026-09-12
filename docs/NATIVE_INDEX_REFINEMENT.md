# Checked case analysis at constrained indices

The native `cases` tactic handles fixed expressions, repeated indices, let-bound
indices, and an index also used as a fixed family parameter. It is no longer
necessary to weaken `Vec A (Nat.succ n)` to a family at an unrelated variable just
to inspect its constructor.

```lean
def tail {A : Type} (n : Nat) (xs : Vec A (Nat.succ n)) : Vec A n := by
  cases xs with
  | cons k x rest => exact rest
```

`nil` is omitted because its result index contradicts the input index. The proof
of that contradiction is retained as its recursor branch. The `cons` branch gets
an equality between the child's length and `n`, and dependent transport gives
`rest` the required type. Nested cases support, for example, inspecting two
successive cells of a vector known to have length two.

## Construction and trust boundary

The fallback generalizes indices in family telescope order and the major premise
into fresh parameters. Each original/generic index pair is related by an explicit
heterogeneous equality. A further equality relates the original and generalized
major values. These assumptions are passed reflexivity proofs at the call site.
They are not added as constants, axioms, or unchecked environment facts.

In each constructor branch a metered worklist uses checked Eq/HEq substitution,
constructor field injection, and constructor/literal contradiction proofs. Later
index domains may depend on earlier indices. The original goal, proof-dependent
hypotheses, and local let values are transported together. User-named fields that
are substituted remain available as checked let aliases, not free variables whose
types were mutated. Failed speculative substitutions roll back their semantic
state without refunding the work spent.

Only generated equation evidence can justify automatic branch pruning. If an
equation cannot be solved by the bounded solver, it remains a real hypothesis and
the branch still needs a proof. Arbitrary functions are not assumed injective,
unknown indices are not assigned guessed constructors, and `cases` does not expose
recursor induction hypotheses to tactics or instance search.

Proposition-only recursors remain proposition-only: constraining an existential or
disjunction to a known index does not provide a way to extract its hidden data.
All complete candidates still cross K1 and the independent checker. Literal
endpoints of equality casts are compared directly, limb by limb, in the independent
checker's metered K gate; large integers are never expanded into unary data.

## Coverage and current limits

Scoped alternatives must cover every branch not proved impossible. Unknown,
duplicate, malformed, and missing reachable alternatives refuse. In this bounded
profile, a supplied alternative for an automatically impossible branch also
refuses, rather than silently discarding that branch's source expressions and
annotations. Omit that alternative. An entirely impossible input can be eliminated
with `by cases h`, without a `with` block.

This increment is case analysis, not generalized constrained-index induction.
The existing induction lane still requires distinct parameter indices. Ordinary
source `match`, recursive definitions with constrained header indices, inaccessible
patterns, and full Lean matcher/equation-compiler parity are separate work.
Mutual, nested, and higher-order inductive families retain their existing limits.

The example includes fixed-length head/tail/second, repeated indices, dependent
index domains, and an impossible repeated-index input:

```bash
fln check-source --json examples/native_index_refinement.lean
```

Source and installed-CLI tests exercise both checking engines, false proofs,
unused annotations, local-name shadowing, dependent proof scopes, and failure
isolation. Scoped tests and workspace compilation do not establish a pinned
Prelude council pass, every workspace test, or complete Reference parity.
