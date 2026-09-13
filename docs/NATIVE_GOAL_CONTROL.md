# Native scoped goal control

Native source proofs support scoped bullets (`·`), `focus`, `all_goals`, `<;>`, and parenthesized tactic sequences.
They operate on the existing goal and term worklists, including goals created by
`constructor`, `apply`, `refine`, and unscoped elimination.

```lean
theorem pair (P Q : Prop) (p : P) (q : Q) : Both P Q := by
  constructor
  · exact p
  · exact q
```

A bullet isolates the first goal and must solve every descendant it creates.
Its unfinished goals cannot consume the next bullet's instructions. `focus`
isolates the first goal but permits its descendants to remain, returning them
before the untouched sibling goals when its sequence finishes. Named local facts,
introduced binders, substitutions, and let-values remain in their own contexts.

`all_goals` runs its entire body once for each goal in the original visible
frontier. Goals created by that body are collected in order, not immediately
mapped over again. For example, `all_goals constructor` splits each original goal
once; the following bullets solve the resulting goals. The original frontier
shares metavariable assignments, so an earlier solution can determine a later
goal's dependent type. Already solved goals are skipped. On an empty frontier,
`all_goals` succeeds without executing its syntactically parsed body.

Both inline bodies (`focus intro x`) and multiline indented sequences are
supported. Semicolons inside a control body belong to that body; an outer
instruction must return to the outer indentation. Nested control syntax is planned
on the parser's heap worklist. The evaluator stores frames in a flat vector and
suspends proof continuations, rather than recursively invoking an evaluator.
A 500-level parser regression runs on a 128 KiB stack.

Pending declaration-closing actions are retained with the goals that justify
them. Scopes do not cross a `cases`/`induction` alternative or a nested local proof.
An enclosing `focus` cannot weaken the requirement that a scoped constructor
alternative finish its own proof. Extra instructions after a completed goal
refuse, except the defined empty-frontier behavior of `all_goals`.

No new axiom, environment declaration, checking rule, or admission authority is
introduced. Invalid values remain typing obligations even when unused; false
proofs and unsolved synthetic holes still refuse. Resource exhaustion remains an
inconclusive/resource outcome, and failure exposes no successor environment.
Every complete declaration still crosses K1 and the independent checker.

## Scope

`left <;> right` isolates the first goal, runs `left`, and then runs `right` once
on each goal that `left` produced. Old sibling goals remain untouched. Either
operand can leave goals; the resulting frontier returns in order. If the left
operand closes its goal, the right operand is not executed. This is an explicit
tactic-control rule, not permission to discard a term's unused typing obligations.

Parentheses group complete tactic sequences without creating an extra proof
scope. For example, `constructor <;> (intro x; rfl)` applies both steps to each new
goal. Chains nest on the right, and syntax leaves (parentheses, separators, source
positions, and comments) remain intact. Group expansion and chain evaluation use
heap frames; the parser tests 1,000 groups and 1,000 operators on a 128 KiB stack,
and the source evaluator checks 200 nested controllers around 1,000 groups.

This implementation adds goal isolation, deterministic frontier mapping, and
sequencing, not interactive goal tags, arbitrary parser combinators, or full
tactic-framework conformance. `first`, `try`, and `repeat` remain separate work.
Curly-braced tactic sequences and every Reference precedence/offside interaction
are not claimed. Keep unparenthesized control bodies indented, and use parentheses
when a `<;>` operand contains several instructions.

```bash
fln check-source --json examples/native_goal_control.lean
fln check-source --json examples/native_tactic_sequencing.lean
```

The example checks dependent record construction, predicate transport, nested
constructor goals, quantified local contexts, and a universal induction proof.
The installed CLI regression rejects a false later file without partial success
and then checks the original prefix again. Package-scoped verification is not a
full-workspace, pinned-Prelude, or Reference-conformance claim.
