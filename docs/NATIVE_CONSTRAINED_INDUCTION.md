# Checked induction at constrained indices

`induction` now accepts the constrained index shapes already handled by native
`cases`: fixed expressions, repeated indices, let-bound indices, and an index
shared with a fixed family parameter. Later index domains may depend on earlier
ones. The implementation uses the same equation-refinement backend as `cases`
and ordinary source `match`; it does not introduce a second recursor generator.

## Conditional induction hypotheses

The motive generalizes the original major value and its dependent context in
addition to the fresh family indices. Merely enabling recursive hypotheses on
the old cases motive would leave the original whole input captured in each
hypothesis. Instead, each child hypothesis quantifies a candidate source value
and explicit equations relating that value and its indices to the actual child.

For a definition `copyLoop n x : Loop n` and an input `x : Loop 7`, the step
branch's hypothesis has the useful, honest shape

```text
ih : forall source : Loop 7,
       HEq 7 childIndex -> HEq source child -> copyLoop 7 source = source
```

After branch refinement establishes `childIndex = 7`, this can be instantiated
as `ih child (HEq.refl 7) (HEq.refl child)`. For two repeated indices there are two
index-equation premises, in family telescope order. The final premise always
relates the chosen source major to the recursive child. None asserts that the
original whole input equals its child.

Explicit `generalizing` parameters and locals dependent on the original major
appear in their original telescope order, before the generated equations. This
allows changing accumulators and properly typed child-specific proof arguments.
Dependent hypotheses, local let definitions, and source-name shadowing keep their
existing meaning. Fixed family parameters cannot be generalized out of the
family's parameter telescope.

The hypotheses are conditional when a child does not have the original index
shape. For positive-length vectors, `induction xs generalizing n` produces a
hypothesis applicable to positive-length children after their length is inspected;
the empty child is handled separately. The engine does not fabricate evidence
that every child of a nonempty vector is nonempty. This explicit-premise profile
is not a claim of Reference tactic-generated binder-name or goal-shape parity.

## Checked specializations for selected simplification rules

The explicit hypothesis interface above is unchanged. When a bare hypothesis
name is selected in `simp only`, the simplifier can instead use a checked companion
that instantiates its generated reflexive equations. For a child with the same
index constraints, this removes the redundant source-major and equation arguments:

```lean
theorem copy_at_three (w : Walk 3) : copyWalk 3 w = w := by
  induction w with
  | done k => rfl
  | step k child ih => simp only [copyWalk, ih]
```

The companion is an ordinary local proof term applying the real recursor
hypothesis. Only newly opened returned parameters can be instantiated, and their
replacements must live in the current branch. Unresolved index equations and
ordinary generalized parameters remain quantified. No equation between the
original input and its child is invented. Temporary telescope contexts are
restored even when construction stops for a resource or typing error.

The original hypothesis remains available for explicit applications such as
`ih child (HEq.refl 3) (HEq.refl child)`. Compound or annotated source rules use
ordinary term elaboration, retaining every supplied argument and annotation.
Selecting a hypothesis does not select unrelated local assumptions. Private
companion names are resolved against the live branch context, so dependent
substitution can change core local identities without losing the link, while
shadowing and sibling branches cannot acquire an earlier branch's proof.

Multiple recursive children receive separate companions. Explicit `generalizing`
parameters, including changing accumulators, remain inferable arguments of the
selected rule. The two-child tree and accumulator proofs run at the unchanged
source-work limit. `simp only` recognizes checked proof lets as lemmas rather than
mistaking them for definitions to unfold, and reflexive HEq side conditions use
the existing restricted conversion policy. Unselected ordinary definitions stay
closed.

Direct local aliases of an induction input, such as `let saved := w`, select the
underlying local while retaining the alias's checked let in the dependent context.
This does not normalize arbitrary source expressions or erase their annotations.

The additional runnable example uses automatic companions and the unchanged
explicit-premise interface together:

```bash
fln check-source --json examples/native_induction_specialization.lean
```

It checks fixed-index and repeated-index copy identity, changing accumulators,
nonempty-vector copy with explicitly supplied child-index evidence, dependent
proof scopes, and impossible-input elimination. A child whose type does not yet
meet the original constraints still needs its actual equations; simplification
does not assert that such a child has those constraints.

## Proof construction and refusal behavior

Induction uses only the admitted family recursor. Generated index and major
relations receive reflexivity proofs at the outer application. Branch refinement
uses ordinary Eq/HEq transports and constructor contradictions. Impossible
branches may be omitted only when those equations yield an actual proof of
contradiction. Unknown equations remain obligations; supplying an impossible
alternative still refuses rather than discarding its annotations or expressions.

`cases` continues to hide recursive hypotheses. Proposition-only recursors
remain proposition-only, including at fixed indices. Invalid arguments and type
annotations remain in the checked term even if unused. Failure and resource
exhaustion publish no environment changes. Neither K1 nor the independent
checker is modified by this increment; both check every completed declaration.

Run the example through the real command:

```bash
fln check-source --json examples/native_constrained_induction.lean
```

It proves fixed-index copy identity, a changing-accumulator variant, vector length
at positive indices using conditional child hypotheses, and copy identity for
dependent index telescopes. Source tests additionally cover repeated/shared
indices, multiple recursive children, proposition elimination, bad branches,
shadowing, resource stops and failure recovery; installed CLI tests check complete
multi-file acceptance versus a false suffix without modifying the input files.

Remaining limits include mutual/nested/higher-order families, constrained-index
structural function definitions, inferred measures and arbitrary well-founded
recursion. Scope-specific tests are not full Lean conformance or a pinned Prelude
council pass.
