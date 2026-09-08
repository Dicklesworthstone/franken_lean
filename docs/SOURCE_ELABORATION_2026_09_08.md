# Native source elaboration: September 8, 2026

The environment-aware source entry points now use a private elaboration transaction and the native unifier. This is a functional extension of the source-to-kernel pipeline, not merely an additional metavariable store or a test-only solver API.

## Implemented source behavior

Explicit argument types and expected result types constrain omitted implicit arguments. Constants with universe parameters receive fresh universe metavariables; their types are instantiated simultaneously without conflating universe parameters with expression metavariables. Application results substitute the actual argument into dependent codomains. Nested applications and local lets use the resulting inferred types rather than an unconditional Nat fallback.

The wider parser and elaborator also accept dependent signatures, ordinary implicit binders, strict-implicit binders, Type/Prop, named type parameters, and function types. For example:

```lean
def identity {A : Type} (x : A) : A := x
def answer : Nat := identity 37

def apply (f : Nat -> Nat) (x : Nat) : Nat := f x
```

Source-defined parameter types and result types may refer to earlier parameters. Local names shadow global names. Implicit and strict-implicit insertion have distinct policies. Unsupported instance synthesis is refused rather than filled with a guessed value.

The same source-inference implementation is used by environment-aware definitions, `#check`, and `#eval` elaboration. Query source is not rewritten into a fabricated definition string. The caller-supplied kernel budget reaches assignment checking through the budget-aware source entry points.

## Trust and completion boundaries

The elaboration transaction is private to the command. Generated expression and universe metavariables must be resolved before a complete declaration candidate leaves this source path. An unresolved implicit argument is not silently replaced with Nat, and an unresolved goal is not reported as a proof.

Candidates still go through the ordinary kernel and, where required by the engine, its independent-checker policy. No new declaration-publication capability, Reference-runtime fallback, dependency, or unsafe implementation was introduced. Closed typing mistakes remain subject to actual kernel checking; inference failures retain their distinct error phase.

## Observed verification

The retained source-inference and dependent-signature runs are GitHub Actions runs `34281247053` and `34281557356`. The latter retains artifact `10077831034`, including its exact source patch, published-commit identity, source/elaborator tests, engine tests, parser tests, Clippy output, and workspace-check output.

The dependent-signature run reported 120 elaborator tests, 97 engine-library tests, and 122 parser tests passing. These are package-level observations, not a claim that the entire workspace test suite, Reference comparison corpus, compiler backends, or release gates passed.

## Further work

A separate source-lambda increment is staged in `scripts/land_source_lambdas.py` with its own test-before-publication workflow. Its completion must be established from that workflow's actual result and published commit, not inferred from this document. It targets expected-typed binders, multi-parameter lambdas, Unicode lambda syntax, higher-order arguments, and inference from application.

General coercions, instance search, arbitrary Lean syntax, explicit universe declarations, pattern matching, tactics, complete conversion parity, and execution of arbitrary higher-order closures remain separate implementation work. Acceptance of a source term by the elaborator and kernel does not by itself prove that every compiler or runtime backend can execute that term.
