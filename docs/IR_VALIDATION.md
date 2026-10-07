# Structural validation of IR file closures

`fln-olean` provides a data-only path from `.ir` containers through structural
validation to a static call graph. This is work on
`fln-ir-decoder-call-graph-sjzl`; it is not permission to execute Reference code.

## Command

```sh
cargo build --locked -p fln-olean --bin fln-ir-check
./target/debug/fln-ir-check A.ir B.ir
./target/debug/fln-ir-check --dot A.ir B.ir
```

Supply the complete declaration closure. The command does not search import
paths, spawn another toolchain, infer signatures from call sites, or replace
missing callees with stubs. An isolated file with imported calls is expected to
fail until its callees' IR declarations are supplied. A container with no IR
entry block is refused rather than treated as an empty validated program.

`--dot` emits DOT diagnostic text to stdout and a summary to stderr. It buffers
the entire bounded graph before writing, so a semantic refusal or output-budget
stop emits no graph. This does not promise atomic filesystem publication: shell
redirection may create an empty file, and a downstream I/O error may interrupt a
write. Numeric node IDs follow structural Name order, not ambiguous printed
names. Module paths are absent from DOT. `fln_dynamic_calls` records closure-value
applications whose targets are not statically known.

Options bound file count, individual and cumulative input bytes, cumulative
captured extension payload bytes, validator work, and DOT output bytes; see
`--help`. Decoder object/node/depth limits additionally apply per file. These
are deterministic accounting limits, not a hard process-memory guarantee or a
filesystem sandbox against concurrent path substitution.

Exit codes are 0 for structural success, 1 for malformed or unclosed IR, 2 for
usage errors, and 5 for unavailable input, unsupported container capability,
resource exhaustion, or I/O failure. An exit 1 about an unclosed supplied file
set is not a claim that its source program is invalid Lean.

## Embedding

- `ir_validate::validate_ir` validates an in-memory module closure. A caller may
  supply reviewed external names and arities explicitly; that map is not loaded
  from a census or validated against a census automatically.
- `ir_validate::build_validated_ir_call_graph` validates every declaration,
  including unreachable declarations, before constructing the existing graph.
- `ir_files::check_ir_files` reads and decodes caller-selected regular files,
  enforcing cumulative byte allowances, then uses that same validation path.
- `ir_files::ir_graph_dot` exports the result under a byte cap.

Structural checking covers definition-before-use, lexical scopes,
declaration-wide variable/join index uniqueness, static callee closure, and
full-call, partial-call and jump arities. Join points are visible in their
continuation, not their own value. Function recursion is allowed. A census-only
callee is displayed as `signature-only`; it has no invented IR body.

## Evidence and remaining contract

The implementation has 49 authored regression tests across `ir_validate`,
`ir_validated_graph`, and `ir_files`. File-path tests re-envelope unchanged
entries decoded from the committed Reference `Init.Data.Nat.Basic.ir` fixture;
their wrapper header is synthetic. Other tests use constructed IR to isolate
scope and budget rules. These are test descriptions, not a claim that a run
passed. The implementation session had no local Rust toolchain, and hosted
execution was still queued when this document was added.

Run `cargo test --locked -p fln-olean` and
`cargo clippy --locked -p fln-olean --all-targets -- -D warnings`. The focused
workflow runs beside the unchanged repository quality gate, not instead of it.

Remaining: full pinned-corpus validation, IR type and ownership checking,
census/extern reconciliation, hostile-container acceptance coverage, and the
canonical content-hashed, census-classified graph artifact required by the
bead. DOT is diagnostic output, not that durable artifact. No kernel authority,
Reference execution permission, or full source compatibility follows from a
successful structural validation.
