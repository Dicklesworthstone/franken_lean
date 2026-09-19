# Native editor proof checking and module reuse

`fln serve-lsp` and `lean --server` check supported declarations and proofs through
the native source-library checker. Namespaces, records, inductives, instances,
coercions and registered simp rules use the same admission path as `fln check-source`.
Every newly admitted declaration crosses K1 and the independent checker. The
server does not manufacture axioms or invoke the Reference toolchain.

## Editor source authority

On each accepted open, change or save, the checker receives a borrowed view of
all open documents from the dispatcher's existing versioned session. An open
import uses its latest accepted unsaved text, not the saved file. Open documents
whose source is invalid or unavailable block the import with a nonauthoritative
outcome; the checker must not fall back to disk. Closing an imported document
makes its disk source eligible again on the importer's next check.

A local `file:` entry resolves `import A.B` as `A/B.lean` beneath its own directory.
The entry and final imported files can be unsaved and not yet exist on disk;
parent directories must exist. Closed imports are read afresh as bounded snapshots
on every check. Quoted structural names, percent-escaped file URIs and Unicode
source positions retain their identities. Path traversal components, symlinked
imports and ambiguous open URI aliases are refused. Import-free and untitled
documents require no filesystem resolution. Resolution is not a race-proof
filesystem sandbox or a Lake/LEAN_PATH package resolver.

Dependency edits are consumed on the next open/change/save of the importer.
Automatic rechecking of all open reverse-dependents, cursor goal inspection,
semantic hover/completion/definition, and Lean RPC sessions are not implemented
by this change. An error in a dependency is reported on the importing document
with the module and original dependency offset in the error text; it is not a
claim of dependency-local editor range projection.

## Reusing checked modules

The server uses one long-lived native worker with an explicitly calibrated stack.
Its source seed, options and checking limits are fixed. `SourceModuleSession`,
also available to embedders from `fln::source_check::modules`, retains immutable
successful module snapshots. Cache hits require exact source bytes and private
identities of all checked imports. Changed source invalidates that module and its
transitive consumers; unrelated siblings remain reusable. Cache hits reuse a
previously checked environment, not caller-authored or deserialized proof claims.

A failed graph or cancellation does not update the cache or return its old success
as the new answer. Cached modules still count toward aggregate command limits,
and reserve their original module-work and metadata-byte charges. Retention has
separate module and source-byte bounds; these are not allocator RSS measurements.
Only the current successful closure is retained. Dependency identity stamps own
no engine worlds, so eviction does not keep old environments alive transitively.

This is process-local **module-level** incrementality. It is not declaration-level
invalidation, a durable Ledger/CAS cache, or a performance-gate claim. Closing the
server releases the worker and cache. The optional-to-consume FrankenLean-specific
`$/frankenLean/sourceCheck` notification reports actual reused/elaborated module
counts, actual declaration replays, and `executed:false`; it is not a Reference
protocol method or a proof certificate.

## Execution and nonanswers

The editor proof-checking path is admission-only: no user program is compiled or
executed to obtain diagnostics. `#eval` and unsupported query forms are reported
rather than run or silently ignored. Use `fln run` or the nonserver execution
surface for supported evaluation commands. This differs from the earlier bounded
server's execution-oriented checker and is not full Lean editor parity.

The aggregate source limit is 1 MiB, with 256 modules and 4,096 import rows.
Resource exhaustion, invalidated imported buffers and worker failures remain
inconclusive/internal-fault outcomes, not successful proofs or user type errors.
Existing incremental UTF-16 text synchronization and diagnostic wait/version
handling remain in the dispatcher.

## Focused verification

```sh
cargo test --locked -p fln --test source_module_session --test source_module_check
cargo test --locked -p fln-server
cargo test --locked -p fln-cli --test lsp_proof_modules --test lsp_stdio_e2e
cargo check --locked --workspace --all-targets
```
