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

## Ordinary source matches

The same checked equation-refining backend now serves source `match` expressions
at fixed, repeated, let-bound, and parameter-shared indices. It preserves dependent
index telescopes, infers result types when sufficient information is available,
and supports nested matches, original dependent hypotheses, implicit constructor
fields, and function-valued branches. For example:

```lean
def tail {A : Type} (n : Nat) (xs : Vec A (Nat.succ n)) : Vec A n := match xs with
  | .cons k x rest => rest
```

All original branch syntax is passed to the ordinary iterative term elaborator,
not translated to source strings or evaluated to select a convenient constructor.
The discriminant is retained in a checked let even if no branch uses it. Impossible
omitted constructors receive the actual generated contradiction proofs. An
explicitly supplied impossible alternative is still refused, rather than erasing
its expressions or annotations. A final catch-all binds each reachable constructor
value at its refined type; a catch-all with no reachable use is also refused.

The existing independent-index matching and structural-recursion paths are kept.
Only their precise index-shape refusal selects the new backend, transactionally
and without refunding the work already spent. Other typing, conversion, and
resource failures are not alternative-selection signals. Generated induction
hypotheses remain invisible in both ordinary and constrained source matches.

Direct constructor-field indices also use the equation backend even when the
input indices are independent locals. This relates the original index names to
the fresh fields by checked evidence rather than rejecting their use or changing
their recorded types. The original names may occur in aliases, unused arguments,
dependent results, and proof-dependent hypotheses. For `Cell n` with constructor
`make (x : Nat) : Cell x`, both `n` and `x` remain usable, with a checked relation
between them. A constructor with separate indices does not imply those indices
are equal. Result indices containing arbitrary function applications do not
license an injectivity assumption. The structural-recursion path retains its
separate recursive-hypothesis lowering.

```bash
fln check-source --json examples/native_constrained_matching.lean
```

Constrained-index induction is now implemented with explicit conditional child
hypotheses; see [NATIVE_CONSTRAINED_INDUCTION.md](NATIVE_CONSTRAINED_INDUCTION.md).
Constrained recursive definitions are covered by
[NATIVE_CONSTRAINED_RECURSION.md](NATIVE_CONSTRAINED_RECURSION.md). Multiple
discriminants and nested constructor patterns use the checked
[pattern-matrix compiler](NATIVE_PATTERN_MATRICES.md). Inaccessible patterns and
full Lean matcher/equation-compiler parity remain separate work.
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
