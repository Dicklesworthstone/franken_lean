# Checked equation-style definitions

Native source declarations can use constructor equations directly rather than
writing a lambda followed by a match:

```lean
def append {A : Type} : Seq A -> Seq A -> Seq A
  | .nil, ys => ys
  | .cons x xs, ys => Seq.cons x (append xs ys)
```

The result annotation supplies the function telescope. Header parameters remain
in scope. Each pattern column consumes an explicit function binder; generated
parameters preserve implicit, strict-implicit and instance binder information.
Later domains and the result may depend on earlier arguments. Fewer columns can
return a function. Function-type definitions can be unfolded to expose a domain.
Names introduced by patterns are scoped to their own alternative, with the same
simultaneous binding and shadowing behavior as ordinary pattern matrices.

The parser retains the original equation pipes, pattern tokens, commas, bodies,
comments and source positions in `declValEqns`. It uses the existing heap-based
match plan for nested matches and scoped proof bodies; it does not synthesize
and reparse a replacement source string. Elaboration opens the checked signature
into fresh unspellable names and constructs an ordinary match syntax node whose
alternatives are the original syntax. Constructor coverage, nested patterns,
ordered overlapping rows, dependent index equations, implicit arguments, and
recursive-call lowering remain owned by their existing implementations.

Recursive definitions have the same structural checks as explicit root matches.
The first equation column is the structural candidate. A family index may appear
in the declaration header and change on a recursive call when the original
recursor machinery generalizes it. Accumulators may change, while genuinely
uniform parameters remain fixed. Nondecreasing calls in unused values and type
annotations are not erased. No recursive constant, axiom or admission mechanism
is introduced: completed candidates still cross K1 and the independent checker.

Theorems may use equations against a dependent function proposition. Named
instance declarations may do so when their complete type satisfies the existing
instance-registration contract. Instance registration occurs only after ordinary
declaration admission. An unused bad annotation in any branch remains a real
kernel typing obligation. Failed file suffixes expose no successor environment.

## Current bounds

An explicit result type is required for equation declarations. The number of
explicit patterns is the same in every row, and it cannot exceed the declared
function telescope. This does not infer missing argument types from constructors,
add literal patterns, equation lemmas with Reference-compatible names, `where`,
`termination_by`, or well-founded recursion. Completely redundant rows and
supplied automatically impossible alternatives retain the current matrix
compiler's explicit refusal policy. To recurse on a later input, use the existing
explicit root-match form until structural-candidate selection covers that case.
Pattern lambdas are described in `NATIVE_PATTERN_FUNCTIONS.md`. These are scoped source-checking results,
not a full Reference syntax/conformance or execution-backend claim.

Run the installed source path:

```bash
fln check-source --json examples/native_equations.lean
```

The example includes list append with a universal induction proof, ordered
Boolean equations, an accumulator, fixed-length vector tail, indexed recursive
copy, and a theorem with nested local proofs. Source and parser tests cover
malformed arities, resource stops, source round trips, deep nesting, scope errors,
invalid annotations, and rejected recursive calls.
