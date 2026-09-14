# Checked transactional tactic alternatives

`first | tactic | tactic` runs alternatives in source order and commits the first
successful sequence, even when it leaves goals. `try tactic` runs one sequence
and restores its original state on ordinary failure. Parentheses delimit nested
sequences; indented alternatives can contain local proofs, elimination branches,
goal controls, and `<;>`. `skip` succeeds without changing goals, and `fail` (with
an optional literal string) causes an ordinary tactic failure.

```lean
theorem transport (n m : Nat) (h : n = m) : n = m := by
  first | rfl | exact h

theorem identity (P : Prop) : P -> P := by
  try (intro lost; fail)
  intro kept
  exact kept
```

A checkpoint snapshots the source elaboration transaction, pending equations,
instance goals, synthetic holes, local identities, branch state, and proof driver
continuations. Failure unwinds nested term work as well as tactic work. Budgets
are not part of the semantic rollback: every attempted instruction remains spent.
Cancellation, resource stops, and internal scope faults propagate; they are never
converted into successful `try` results or used to choose another alternative.

Rigid typing and equality constraints are checked while an alternative is active,
so an inapplicable `rfl` or ill-typed `exact` does not commit merely because a final
checker would reject it later. This is still untrusted elaboration, not authority:
completed declarations must pass both K1 and the independent checker. Unresolved
holes and unused arguments remain obligations. Successful `first` does not promise
a complete proof; a later failure outside it does not revisit an earlier choice.

The term driver owns a flat checkpoint stack. Nested alternatives do not clone
checkpoint ancestors or recursively invoke another proof evaluator. Existing
strict bullets, constructor-alternative fences, and goal-order rules remain in
force. `all_goals` inside an alternative visits the original visible goals; it
cannot borrow a sibling constructor branch's context. Match row coverage belongs
to the elaboration scope of the chosen match, not to matches in unexecuted tactics.
Malformed source still fails parsing before any tactic can run.

## Bounds

This is native `first` and `try`, not `first | ...` with global search over later
instructions. The other search combinators remain separate work.
The literal text of `fail` is retained in syntax but its current diagnostic is the
stable generic failure class. Unknown tactic grammar cannot be caught at runtime.
This does not add goal tags, `case`, the complete metaprogram API, or a new checking
rule. Scope/resource tests and package tests are not full Reference conformance.

```bash
fln check-source --json examples/native_tactic_alternatives.lean
```

The example exercises actual dependent carrier rollback, scoped alternatives,
proofs after failed introductions, and a nested local proof. The installed CLI
checks the whole batch, refuses a bad suffix without reporting partial success,
and successfully rechecks the original file afterward.

## Transactional repetition

`repeat tactic` checkpoints each iteration independently. Successful iterations
retain their solved goals, introductions and dependent assignments. The final
ordinary failure restores only that iteration and ends repetition successfully.
An enclosing failed `first` or `try` can still roll back the whole repetition.

```lean
theorem identity (P : Prop) : P -> P -> P -> P := by
  repeat (intro x; intro y)
  intro last
  exact last
```

The second attempted pair of introductions fails after its first `intro`; that
partial work is rolled back, leaving the final argument for `intro last`. This is
`repeat`, not `repeat'`: when the first goal rejects a tactic, repetition stops
instead of skipping that goal and visiting its siblings. A sequence can of course
use `all_goals` or `<;>` explicitly, with their existing isolation rules.

No semantic-progress heuristic reports a nonprogressing loop as success.
`repeat skip`, `repeat try fail`, and their enclosing `try`/`first` forms consume
the shared work budget and return a resource nonanswer. The next checkpoint
replaces the old one rather than retaining a growing chain of successful states.
The finite-loop example also runs through the installed CLI:

```bash
fln check-source --json examples/native_tactic_repetition.lean
```
