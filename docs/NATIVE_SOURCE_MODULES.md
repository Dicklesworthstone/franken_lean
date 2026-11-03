# Native checked source libraries

`fln check-source Main.lean` checks the complete local source import closure of
one entry file. Definitions, theorems, inductive types, records, instances and
simp registrations use the same native frontend and K1-plus-independent-checker
admission path as import-free proof checking. Ordinary checking does not run
user code. The explicit imported-macro mode below executes macros before checking
the declarations they produce.

```sh
cargo run --locked -p fln-cli -- check-source --json examples/native_modules/Main.lean
```

## Local resolution

The directory containing the entry file is the module root. A plain `import A.B`
loads `A/B.lean` beneath that root. All transitive imports use that same root.
Structural quoted names are preserved: `import «A.B»` loads the literal filename
`A.B.lean`, not `A/B.lean`. A leading UTF-8 BOM and CRLF headers retain original
source byte offsets in diagnostic errors.

Pass the entry file alone when it contains imports. Import-free, caller-ordered
multi-file batches continue to work as before. An ambiguous multi-file invocation
containing imports is refused rather than flattening unrelated environments.
Missing files, cycles, conflicting module identities, nonregular imports, and
symlinked import files or directories fail before a successful receipt is emitted.
Import names containing traversal or path-separator components are rejected before
filesystem resolution. The process does not change its current directory or write
source, object files or build artifacts.

Resolution reads bounded snapshots, not a filesystem transaction: applications
that permit another process to replace directory entries during a check must
provide their own stable source snapshot. There is no claim of race-proof sandboxing.

## Module isolation and replay

Each module elaborates once against its explicit initial environment and its own
transitive imports. An unrelated sibling cannot supply a name, instance or simp
rule. In particular, a definition elaborated using one instance does not silently
change when later imported alongside a higher-priority instance.

Consumers import the exact already-elaborated declaration terms. Those terms
cross both ordinary checking engines again before becoming visible. The importer
does not manufacture axioms, treat decoded declarations as trusted, or re-elaborate
dependency source under a larger environment. Shared dependencies in a diamond are
replayed once per consumer closure, in first-discovery dependency order. Independent
modules defining the same constant conflict even when their bodies are identical.

Native append-ordered extension journals carry record information, class/instance
registrations and simp additions/removals. Exports contain only each module's own
suffix, after exact prefix validation against its imported environment. Opaque or
unsupported merge contracts are refused, never guessed safe.

## Checking with imported macros

Use the explicit imported-macro mode when a source file depends on a macro in an
already compiled module:

```sh
fln check-source --json \
  --imported-macros contracts/builtin_partition.tsv \
  --macro-max-bytes 67108864 Main.lean
```

The partition file must be the complete publication for the repository's pinned
Reference; its SHA-256 is verified before it can authorize execution. For a
development checkout with the pinned Reference installed,
`scripts/extract/census_materialize.sh` materializes and verifies that publication.
The command itself uses native code and does not invoke the Reference.

Pass one entry source file. Local imports still resolve from the entry directory;
compiled imports use the ordinary `LEAN_PATH`/pinned-library resolution. The mode
requires a checked external `.olean` import closure. Executable `.ir` companions
come from the same resolved module locations as those checked artifacts; a later
search directory cannot supply a replacement for a missing companion. The
`--macro-max-bytes` ceiling applies cumulatively to the loaded IR companions and
defaults to 64 MiB. `--max-bytes` continues to bound the source closure separately.

Imported registration journals and declaration ownership are validated before
expansion, including inactive scoped registrations. The explicit macro modes in
`check-source`, `fln run` and native `lean` compile a macro's reachable
implementation only when that macro is selected, so an unused macro with an
unsupported operation does not block unrelated declarations or execution.
Successful compilations are shared across module projections and scoped
activations; mutable invocation state remains separate. A selected implementation
that cannot compile stops the command without falling back to an older registration.

User macro code runs on Golem, with toolchain operations provided by native
implementations; the pinned partition cannot be overridden to run a toolchain
implementation as user code. The expanded declarations then pass through
the same kernel and independent-checker admission as ordinary source. Expanding a
macro does not bypass proof checking.

The JSON result reports `importedMacros` work counters and whether code actually
executed; ordinary checks retain their existing output. Each source module gets
its own macro state, quotation context and scoped activations. Expansion budgets
are shared across the entire source graph. A later failure produces no successful
prefix or successor module state, and resource exhaustion remains inconclusive.

This mode checks declarations and proofs. It does not execute `#eval` or a
program's `main`, emit artifacts, or enable imported macros in the drop-in `lean`
personality. It currently uses the parser's supported syntax kinds; source-declared
templates cannot yet be mixed into the imported-macro session. Hygiene starts
from the adapter's explicit seed, rather than the pin's command-hash seed. An
unsupported native macro operation or source construct is reported explicitly.

## Executing programs with imported macros

The installed `fln run` and native `lean` commands opt in separately through
`FLN_MACRO_PARTITION`, using the same verified partition, checked ownership,
complete registration table and adjacent IR companion loader as `check-source`:

```sh
FLN_MACRO_PARTITION="$PWD/contracts/builtin_partition.tsv" \
  LEAN_PATH="/path/to/import/artifacts" fln run --json Main.lean
FLN_MACRO_PARTITION="$PWD/contracts/builtin_partition.tsv" \
  LEAN_PATH="/path/to/import/artifacts" lean Main.lean
```

The runtime route uses the same 64 MiB cumulative IR limit. An unset variable
preserves ordinary runtime behavior and does not read IR companions. This mode
requires a checked external artifact import; it does not execute a source file
containing only local macro declarations.

Expansion feeds the command's actual syntax into elaboration, dual-check
admission, native compilation and execution. Definitions, examples, mutual
declarations, public module exports, ordinary `#check` and `#eval` share one
macro session per source module. A sibling's scoped activation or macro state
cannot leak into another module. Expansion budgets accumulate over the graph,
including work completed before a failure.

Both checking and raw execution JSON include `linkedReferenceFunctions` and
`linkedNativeFunctions` inside the existing `importedMacros` report. These
identify the compiled closures used by attempted dispatches; they are not a
dynamic per-function call trace. Reference-produced functions retain explicit
producer labels. Native `lean` keeps its ordinary query and evaluation output.

Raw `--emit-flbc` is supported. A source-closure sidecar request is refused
before execution because that format does not yet bind macro IR and partition
inputs. Neither output file is created by that refused request.

This remains a bounded macro integration. It expands syntax already recognized
by the native parser and validates the complete imported registration table;
unsupported rows are not silently dropped. Imported parser grammars, atomic and
tactic macro expansion, source templates, and macro execution under `#guard`,
`#reduce` or `#guard_msgs` are not yet supported. Full stock `Init` macro
execution is not claimed.

## Library API and limits

`Engine::check_source_modules` and `Engine::check_source_modules_with_cancel`
accept `SourceModuleInput` values and a structural entry `Name`. Types and the
header parser are exported from `fln::source_check::modules`. A successful
`SourceModuleCheck` contains the checked entry environment, closure-wide file,
command and theorem counts, logical roots, module order and replay counts. The
supplied engine is unchanged on every success, failure and nonanswer.

For an admitted external import receipt,
`SourceOleanImport::check_source_modules_with_deferred_imported_macros` accepts
`SourceModuleDeferredMacroInputs`. `MacroCompilationInputs::new` takes ownership
of decoded IR, the verified partition and the explicit set of permitted user
declarations without cloning IR bodies. The corresponding execution methods are
`execute_source_modules_with_deferred_imported_macros` and
`execute_lean_source_modules_with_deferred_imported_macros_and_validation`.
They retain the ordinary module validator, evaluation presentation and runtime
resource limits. The existing eager APIs remain available for callers that
require every registered implementation to compile before processing starts.

The initial environment is explicit. Without external imports, ordinary checking
uses the native source seed where appropriate. External `.olean` imports are
admitted through the checked import receipt instead; they do not borrow unrelated
source declarations from an ambient environment. The `check-source` command does
not implicitly import the full Reference `Init` library.
The CLI bounds the closure to 256 modules, 4,096 import rows and name depth 128.
`--max-bytes` applies to all source files together, including dependencies. The
library additionally exposes aggregate graph/replay work and extension-byte
ceilings. Cancellation is observed at module and replay boundaries and immediately
before publication; individual kernel checks retain their existing synchronous
resource budgets. Resource exhaustion never becomes a successful proof.

## Remaining scope

This checking command does not discover Lake packages or ancestor source roots,
emit module artifacts, or execute imported user evaluation commands. Use the
separate [native Lake workflow](NATIVE_LAKE.md) for supported module builds.
Unsupported syntax and unimplemented macro operations remain explicit refusals.
The complete Lean language, general metaprogram compatibility and whole-Corpus
conformance are not claimed.
