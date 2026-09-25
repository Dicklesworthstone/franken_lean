# Native interleaved static arguments

The source-to-Golem compiler can specialize a closed type argument or an inert
instance dictionary after ordinary runtime parameters, not just at the start of
a function's parameter list. The source command path inspects the whole outer
parameter telescope when deciding which definitions are checked templates.
A concrete `#eval` must still compile and execute successfully.

```lean
def keep (ignored : Nat) {A : Type} (x : A) : A := x
#eval keep 9 42
#eval let saved : Nat -> Nat := @keep 9 Nat; saved 42
```

Static argument positions and their exact values join the original declaration
and ground universes in the specialization key. Runtime argument values are
not in that key and are not substituted into the function body. They remain
ordered call arguments, including unused arguments and owned values. Partial
and saturated calls with the same static arguments share the same specialized
body. Removing a static binder rebases the later type and value telescopes;
earlier runtime binders retain their own domains and binder metadata.

`examples/native_interleaved_specialization.lean` exercises a generic function
and a monadic `do` function whose monad and dictionaries follow a Nat parameter.
The implementation uses the existing admitted environment, native instance
selection, post-admission specialization, closure conversion, FIR/FLBC
validators and Golem. Private compiler definitions never enter the logical
environment or replace either declaration checker.

## Boundaries

Static arguments must be closed and have domains independent of retained
runtime values. A dictionary indexed by an earlier runtime parameter is not
globally specialized even when one caller supplies a literal. Computed
dictionary initializers are not executed or discarded at compile time.
Specialization stops at a strict let or a computed function-return stage;
it does not eta-expand across that work. Unsupplied polymorphic parameters and
unsupported runtime representations remain refusals. This is not general Lean
compilation, packed-ABI parity or a completed W5 gate.

## Regression commands

```bash
cargo test --locked -p fln --lib --test runtime_interleaved_specialization
cargo test --locked -p fln-cli --test source_interleaved_runtime
cargo run --locked -p fln-cli --bin fln -- run examples/native_interleaved_specialization.lean
```

The added cases cover interleaved types/dictionaries, partial calls, captures,
owned strings, callbacks, monadic execution, strict unused arguments, invalid
source, resource refusal, cache separation, failure-atomic retries and emitted
bytecode replay. Test presence is not execution evidence; consult the exact
commit's constructor-runtime workflow for its observed verification status.
