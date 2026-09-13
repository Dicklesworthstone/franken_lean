# Checked pattern functions

The native term path supports pattern lambdas (`fun | ...` and `λ | ...`) as
ordinary function values, local definitions, record methods and higher-order
arguments. Expected function types provide the domains and dependent results.

```lean
def apply (f : Bool -> Nat) (b : Bool) : Nat := f b

theorem checked : apply (fun | true => 7 | false => 9) true = 7 := by rfl

def identity : forall A : Type, A -> A := fun | A, value => value
```

Multiple columns retain first-match priority and simultaneous binding. Nested
constructor patterns, indexed domains with unreachable constructors, and nested
pattern functions share the ordinary matrix compiler. A pattern function can
return another function. Explicitly annotated local values and record fields
provide the same expected-type information as top-level function values.

The parser retains the original keyword, pipe, comma, pattern and body leaves,
including comments, CRLF and source positions. Its match planner handles pattern
functions inside out on the heap; the first outer statement after an unparenthesized
local function is not swallowed by its last branch. Nested `by` branches own their
scopes under the existing proof parser. This does not broaden the parser's existing
restrictions on arbitrary nested tactic-proof argument positions.

Elaboration constructs ordinary lambdas over private generated names and uses the
existing lambda/term worklist to check them. The original alternatives go through
one shared pattern matrix implementation; they are not textually rewritten and
reparsed. Constructor coverage, index equations, branch witnesses and dependent
transport have the same checks as ordinary `match`. Hidden recursive hypotheses
remain inaccessible to ordinary source and instance search.

Every source row and written annotation retains its checking obligation. An
unused local pattern function with an invalid branch still fails ordinary kernel
checking. Missing reachable branches, fully redundant rows, duplicate binders,
invalid types, escaping branch names, and forbidden proof-to-data elimination
remain refusals. Ordinary recursive declarations cannot hide a nondecreasing
self-call in an unused pattern function. No new constant, axiom, runtime dependency,
checking-engine rule or admission authority is introduced.

## Current bounds

Pattern functions use explicit pattern columns. Known expected function domains
are needed for constructor patterns; this feature does not guess an arbitrary
input type from constructor names. Inference for an abstract catch-all remains
subject to the ordinary unresolved-metavariable rules. Implicit lambda binders,
non-Nat literal patterns, guards, inaccessible patterns, arbitrary term-level recursion,
and full Lean equation-compiler parity are separate capabilities. Use the existing
explicit signature with equation-style declarations for implicit signature binders.

```bash
fln check-source --json examples/native_pattern_functions.lean
```

The example checks generic map, ordered Boolean clauses, a dependent identity,
a record method, a proof-valued pattern function, and a directly supplied callback.
Source and installed-CLI tests require the entire file batch to pass before any
success is emitted. These are scoped source-admission and conversion results, not
execution-backend parity or complete Reference conformance.
