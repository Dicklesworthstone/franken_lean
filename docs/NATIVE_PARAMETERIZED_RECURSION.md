# Native parameterized recursive families

The source checker supports uniformly parameterized, non-indexed families with
direct recursive fields, including generic sequences and branching trees. Their
recursors are reconstructed separately by K1 and the independent checker. The
independent implementation uses checker-owned wire arenas and does not call the
primary inductive generator or kernel.

```lean
inductive Seq (A : Type) where
  | nil
  | cons (head : A) (tail : Seq A)

def append {A : Type} (xs : Seq A) (ys : Seq A) : Seq A := match xs with
  | .nil => ys
  | .cons x tail => Seq.cons x (append tail ys)

theorem append_right_nil {A : Type} (xs : Seq A) : append xs Seq.nil = xs := by
  induction xs with
  | nil => rfl
  | cons x tail ih => simp only [append, ih]
```

Run `fln check-source --json examples/native_parameterized_recursion.lean`.
That file contains seven theorems, including generic map identity/composition,
append associativity and mirror involution, alongside concrete computations.
Checking and kernel conversion are not claims of execution-backend coverage.

## Shape-derived independent checks

Admission is not keyed to a family name such as `List`. The checker derives each
minor premise and the complete iota-rule telescope from the family and constructor
declarations. It checks the actual recursion arguments, parameter order, universe
arguments, number of recursive fields and corresponding induction hypotheses.
A false nonrecursive flag cannot avoid this audit. Rule domains cannot silently
refer to the motive or another minor in place of an earlier parameter.

Multiple parameters, dependent parameter telescopes, dependent constructor fields,
instance-implicit fields, and several direct recursive fields are supported.
The checker also accepts the wire-level universe-polymorphic shape; this does not
add source-level universe-declaration syntax. A recursive field must be exactly
the family at its original parameters and universes. No nested or negative
occurrence is accepted just because its declaration claims uniform recursion.

Field types are independently inferred in their proper parameter/earlier-field
context. A sound sufficient universe inequality checks each field against the
family's result sort. It handles successor, maximum, and safe bounds for imax;
it is not a complete symbolic universe solver. An unproved symbolic bound defers.
Known concrete violations reject. Families whose result sort may be Prop remain
on their existing elimination-policy routes; this increment does not grant them
unrestricted elimination into Type.

All staging is private to the checker. Its output is an observation, never a new
admission authority. Comparison, arena and materialization bounds and cancellation
preserve their nonanswer outcomes. Unsupported indexed, nested or mutual shapes
are not admitted by approximation.

## Recursor conversion

Definitional equality keeps saturated recursor applications intact long enough
for iota reduction to inspect their major premise. Splitting the spine earlier
can lose both the major and trailing arguments, blocking a legitimate append
computation whose recursor returns a function.

If the major remains unknown after reducing a definition, that reduced major is
retained. Otherwise conversion could repeatedly report the same discarded work
and exhaust its budget without progress. Genuinely stuck recursors may still be
compared by congruence after normalization, without guessing a constructor.
Neither repair broadens unsafe/opaque definition unfolding or discards a branch
before the original source typing obligations are checked.

## Boundaries and tests

The lane currently has at most 64 parameters, 32 constructors, 64 total fields,
eight family universe parameters, and 262,144 input/expected arena units, in
addition to caller budgets. Higher-order recursive fields, changed recursive
parameters, indexed/mutual/nested families, maybe-Prop result sorts, and general
well-founded recursion are not added here. Existing root-match/direct-child
source recursion and import-free `check-source` restrictions remain unchanged.

Tests cover handwritten wire-level fixtures and forged variants separately from
primary-generator/source integration. Real source tests use both admission
engines for generic lists, trees, dependent payloads and open induction proofs.
Installed-CLI tests check the committed example and refuse partial success when
a later file supplies a false generic theorem. Tests are scoped evidence, not
whole-workspace or full Lean compatibility claims.
