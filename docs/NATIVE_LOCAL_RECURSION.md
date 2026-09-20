# Native local structural recursion

The source elaborator supports a single `let rec` function with typed parameters
and an explicit result type. The function can capture its lexical context,
contain nested local functions, return a function, and compute types or proofs.
Both semicolon and newline continuations are supported. For example:

```lean
def iterate (step : Nat -> Nat) (seed count : Nat) : Nat :=
  let rec go (acc remaining : Nat) : Nat :=
    match acc, remaining with
    | _, .zero => acc
    | _, .succ k => go (step acc) k
  go seed count
```

The recursive parameter need not be the first parameter or match column.
The elaborator tries eligible structural arguments using the existing admitted
recursors, with the other varying arguments generalized into the motive.
Local recursion also works over the supported user-defined inductive families.
It is not restricted to a special evaluator for `Nat`.

## Checking and execution

`examples/native_local_recursion.lean` includes a computed answer and a checked
theorem. It can be checked without running the program:

```sh
fln check-source examples/native_local_recursion.lean
```

Adding `#eval answer` exercises the ordinary native source-to-FIR-to-FLBC-to-Golem
execution path. The CLI regression also exports and replays the bytecode, checks
the `lean` entry point, and verifies that a later invalid recursive definition
does not publish a new artifact or damage the earlier one.

## Admission, scopes, and retries

The recursive name is visible in its value, shadows an outer homonym, and is
itself shadowed by a same-named parameter. The completed function is closed over
its parameters and installed as an ordinary local binding. No generated global
helper, recursive axiom, Reference fallback, or new admission authority is used.
Nested local functions retain references to enclosing recursive definitions;
the enclosing recursor still checks structural descent for those calls, even in
an unused local value. Fully qualified names and parameter shadowing retain
their ordinary meaning.
The generated declaration still requires K1 admission and the independent
checker's agreement. An invalid recursive value is checked even when unused.

Structural candidates and tactic alternatives share one lexical checkpoint
stack. Retrying a candidate restores speculative assignments, constraints,
local context, recursion state, and name generation, but never refunds spent
work. Resource stops and internal faults are not tactic alternatives. A failed
continuation cannot reopen a completed local declaration.

## Boundaries

This is structural recursion through the existing bounded source recursor
compiler, not full upstream recursion parity. The implementation does not add
mutually recursive local groups, general well-founded recursion, `where`
clauses, or support for `termination_by`, `decreasing_by`, and fixed-point
suffixes. Unsupported suffixes are refused rather than ignored. A genuinely
recursive body must expose a supported structural match; nonrecursive `let rec`
functions do not need a decreasing parameter. Newline support does not claim
complete upstream layout or extensible-parser parity.

`fln-parse`'s `local_recursion` tests cover syntax, original-source preservation,
and small-stack nested parsing. `fln`'s `source_local_recursion` tests cover
kernel-checked computation, scopes, dependent results, retries, refusals,
resource handling, and native execution. The source check CLI tests cover the
installed command path. The parent elaboration workstreams remain open.