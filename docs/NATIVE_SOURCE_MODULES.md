# Native checked source libraries

`fln check-source Main.lean` checks the complete local source import closure of
one entry file. Definitions, theorems, inductive types, records, instances and
simp registrations use the same native frontend and K1-plus-independent-checker
admission path as import-free proof checking. No user code is compiled or run.

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

## Library API and limits

`Engine::check_source_modules` and `Engine::check_source_modules_with_cancel`
accept `SourceModuleInput` values and a structural entry `Name`. Types and the
header parser are exported from `fln::source_check::modules`. A successful
`SourceModuleCheck` contains the checked entry environment, closure-wide file,
command and theorem counts, logical roots, module order and replay counts. The
supplied engine is unchanged on every success, failure and nonanswer.

The initial environment is explicit. The CLI supplies its native coercion seed;
this is not an implicit import of the full Reference `Init` library. Optional
`prelude` syntax does not replace the caller's explicitly supplied environment.
The CLI bounds the closure to 256 modules, 4,096 import rows and name depth 128.
`--max-bytes` applies to all source files together, including dependencies. The
library additionally exposes aggregate graph/replay work and extension-byte
ceilings. Cancellation is observed at module and replay boundaries and immediately
before publication; individual kernel checks retain their existing synchronous
resource budgets. Resource exhaustion never becomes a successful proof.

## Remaining scope

This is source-only, admission-only library checking. It does not load `.olean`
imports, search `LEAN_PATH`, discover Lake packages or ancestor roots, emit module
artifacts, persist a build cache, or implement newer `module`/`public import`/`meta
import` visibility semantics. Unsupported syntax remains a refusal. The complete
Lean language, Reference artifact compatibility and whole-Corpus conformance are
not claimed. Imported user evaluation commands are not executed or ignored.
