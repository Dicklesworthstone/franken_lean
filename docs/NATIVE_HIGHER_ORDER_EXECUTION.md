# Native higher-order execution

The checked source runtime now derives callable interfaces from monomorphic,
nondependent function types. A function parameter may itself accept callbacks.
The value is an ordinary Marrow closure: FIR/FLBC dynamic `Apply`, capture
conversion, ownership validation and Golem execution remain the same path used
by local functions. No upstream evaluator, fabricated lambda body, erased type
cast, or new kernel axiom is involved.

```lean
def twice (f : Nat -> Nat) (x : Nat) : Nat := f (f x)
#eval let inc (x : Nat) : Nat := x + 1; twice inc 40
```

This also supports multi-argument callbacks, partial application of local
closures, captured callbacks, owned String captures/results, and a callback
such as `(Nat -> Nat) -> Nat`. Function interfaces can exist before any concrete
callback with that shape is constructed. Source-local interface identities are
resolved against all lambda signatures and partial-application suffixes after
runtime preparation, including the closures used for lazy branches and
recursors. FIR independently checks that table and every application.

The two declaration checkers still see the original source terms. Execution
preparation is post-admission and does not publish or modify declarations.
Failures leave the original immutable engine usable. Interface, expression,
context and compiler-table limits apply to discovery and canonicalization.

This is not general Lean compilation or a G2/G3 claim. Polymorphic/dependent
representations, proof-valued callbacks and effectful callbacks remain outside
this slice. At this checkpoint, use a typed let-bound function as the callback
value; arbitrary anonymous callback expressions and bare global function
values need separate runtime annotation support.

Regression coverage lives in `crates/fln/tests/runtime_higher_order.rs` and
`crates/fln-comp/tests/closure_interfaces.rs`. It exercises native execution,
owned values, distinct and nested interface shapes, deterministic artifacts,
partial application, failure atomicity, malformed interface envelopes, dangling
type references and resource limits.

## Execution ceilings from the command line

`lean`, `fln run`, and `fln flbc run` accept `--fln-max-steps N` and
`--fln-max-frames N` (also `--fln-max-steps=N` and `--fln-max-frames=N`). These
FrankenLean options bound VM instructions and simultaneously live call frames.
For example:

```sh
lean --fln-max-steps 1000000 --fln-max-frames 10000 Main.lean
fln run --json --fln-max-steps=1000000 Main.lean
fln flbc run --fln-max-frames=10000 main.flbc
```

The limits apply independently to each source evaluation, including evaluations
in imported source modules, and to the whole execution of a replayed artifact.
The `lean --stdin` path accepts the same options. Defaults remain no instruction
ceiling and 4,000,000 frames; an explicit zero permits no instructions or frames.
Values must be ASCII nonnegative integers within the `u64` range. Repeated
options, missing values, and limits on `lean --src-deps` are usage errors.

Exhaustion produces a typed inconclusive outcome and exit code 3. Buffered
source output and requested source artifacts are published only after the
program succeeds. These execution limits do not change elaboration heartbeats,
kernel admission, or the independent checker's budgets.

## Export and replay a program with imports

`fln run` can now publish FLBC from an entry module with explicit source or
compiled imports. The product is the exact validated bytecode retained from
the entry module's final executable declaration or `#eval`. Reachable imported
definitions are compiled into that product, so replay needs neither the source
files nor their `.olean` inputs.

For example, with the pinned library available on `LEAN_PATH`:

```lean
-- Main.lean
prelude
import Init.Prelude

def answer : Nat := id 42
#eval answer
```

```sh
fln run --json --emit-flbc main.flbc --emit-sidecar main.sidecar Main.lean
fln flbc run --json --sidecar main.sidecar main.flbc
```

The first command checks and executes the complete source import program in
dependency order. The second executes the retained entry artifact and returns
`42`; it does not rerun earlier source commands or their effects. An entry with
no executable declaration or `#eval` cannot publish a dependency's execution as
its own product. JSON output identifies the emitted product's module and
command index.

The optional standard-profile sidecar binds all source module names and bytes,
their actual execution order and logical inputs, and each imported module's
exported, server, and private artifact parts. Reordering discovery inputs does
not change the binding; changing a sibling source or an imported artifact does.
Replay verifies the exact product and the current toolchain components using
the existing sidecar consumer. This is a product binding, not a certificate that
the consumer has independently rebuilt the source program. Omitting
`--sidecar` on replay uses the existing validated FLBC execution path.

Publication follows successful checking, execution, message guards, and bounded
report preparation for the entire program. Existing output files are refused.
Each file is created atomically, with the sidecar first; if publishing the
product then fails, the error identifies the retained complete sidecar. This
does not promise a two-file filesystem transaction.

Explicit-import programs still refuse `--emit-olean-snapshot`: preserving an
imported environment's module metadata and private artifact parts requires a
separate snapshot export contract.

Regression coverage in `source_imported_execution` includes a native `.olean`
producer, source siblings, deterministic artifacts, replay after the original
inputs become unusable, corrupted-product refusal, failed-source and guard
atomicity, VM limits, output collisions, and recovery. Its
`pinned_prelude_imports_can_publish_replayable_bytecode_and_a_verified_sidecar`
test also runs the producer and consumer over the actual pinned
`Init.Prelude` artifacts when `FLN_REFERENCE_LIB` is set; set
`FLN_REQUIRE_REFERENCE=1` to require those artifacts rather than skip that test.
