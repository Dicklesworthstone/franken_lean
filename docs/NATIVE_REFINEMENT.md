# Native partial proof terms

`refine term` elaborates an ordinary source term against the current goal and
turns explicitly written `?_` and `?name` placeholders into proof-state goals.
All these goals must be solved before the parent goal closes. The final candidate
is still admitted by K1 and the independent checker; a hole is never an axiom.

```lean
theorem pair (P Q : Prop) (p : P) (q : Q) : Both P Q := by
  refine Both.intro p ?_
  exact q

def identity : forall A : Type, A -> A := by
  refine fun A x => ?_
  exact x
```

In the second example, the remaining goal has `A : Type` and `x : A` in scope.
The implementation represents a synthetic hole as a closed function metavariable
applied explicitly to its captured parameters. Solving it closes that same
parameter telescope with ordinary lambdas and lets. This prevents hidden free
variables from escaping when a source lambda closes before its hole is solved.
Dependent local domains, let values and proof hypotheses are retained.

Explicit holes are synthetic-opaque to the unifier: an equation does not silently
solve them or turn them into ordinary implicit arguments. The ordinary `_`
placeholder and omitted implicits remain inference problems, not new tactic
goals. A named hole can be reused in the same refinement term at a compatible
type and an identical local context. Reuse across different binder scopes refuses
rather than capturing a same-spelled variable. Names in distinct `refine`
instructions are independent; a hole name is not an assumed local theorem.

Goals are scheduled in first-occurrence elaboration order. Thus a constructor's
type or witness hole is solved before a later field depending on it. Repeated
named holes create one goal. A hole in a type annotation is a type-valued goal.
Holes in ignored arguments still need values: beta reduction of the completed
term does not erase the pending proof-state obligations.

## Constraint progress and trust

A synthetic hole can block a unification batch while an independent equation
already determines one of its argument types. The source solver first tries the
complete batch, retaining its joint-assignment behavior. When it is blocked, it
also makes individually checked progress in the private source transaction and
retries after the assignment generation changes. Work is charged and not refunded.

Source typing equations are distinguished from equations used to select rewrite
occurrences and instance candidates. A fully instantiated source typing equation
remains an obligation of the final retained declaration term. A selection equation
must actually be solved before the algorithm can use its result, even if it has
no metavariables. Deferral is never interpreted as a successful match. Invalid
unused annotations and contradictory endpoint assignments receive normal kernel
rejections; incomplete proofs cannot publish a successor environment.

`constructor`, `left`, `right`, `intro`, scoped induction, local lemmas,
simplification, and dependent `subst` can operate on the resulting goals. The
parent closes only after its descendants. Synthetic goals do not expose hidden
case-analysis induction hypotheses or bypass structural-recursion checks.

Both parsing and elaboration use existing heap worklists. Parser tests include
one thousand nested groups on a 128 KiB stack; source and CLI tests exercise
scope separation, resource stops, failure recovery and checked dependent transport.

## Bounded surface

This is `refine`, not `refine'`: unsolved `_` and implicit metavariables are not
promoted to goals. Explicit synthetic holes outside a refinement skeleton refuse.
The skeleton uses the existing bounded tactic-argument term grammar; arbitrary
nested `by` expressions and nested term-level `let` expressions in those argument
positions are not added by this increment. Tactic `let` and nested local proof
declarations remain available. No goal-selector grammar or interactive server
proof-state interface is claimed here.

```bash
fln check-source --json examples/native_refinement.lean
```

The example checks dependent records, existential witnesses, captured lambda
parameters, separate shadowed function bodies, equality transport, universal
induction and an explicitly supplied value in an ignored argument. Scoped tests
do not establish full Reference compatibility or execution-backend parity.
