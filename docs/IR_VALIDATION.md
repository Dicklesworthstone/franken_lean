# Structural and representation validation of IR file closures

`fln-olean` provides a data-only path from `.ir` containers through validation
to a static call graph. This is work on `fln-ir-decoder-call-graph-sjzl`;
it is not permission to execute Reference code.

## Command

```sh
cargo build --locked -p fln-olean --bin fln-ir-check
./target/debug/fln-ir-check A.ir B.ir
./target/debug/fln-ir-check --dot A.ir B.ir
./target/debug/fln-ir-check --structural-only A.ir B.ir
```

By default the command checks both structure and the pin's expression
representation rules. `--structural-only` preserves the earlier diagnostic
behavior and explicitly prints `IR expression representations: NOT CHECKED`.
An unchecked result is never labeled as representation-checked.

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
applications whose targets are not statically known. DOT itself claims structural
checking only, whether or not the caller also requested representation checks.

Options bound file count, individual and cumulative input bytes, cumulative
captured extension payload bytes, validator work, and DOT output bytes; see
`--help`. Structural and representation checking share `--max-work`: the second
pass does not receive a fresh allowance. Decoder object/node/depth limits
additionally apply per file. Directly constructed aggregate types also have a
bounded iterative traversal. These are deterministic accounting limits, not a
hard process-memory guarantee or a filesystem sandbox against concurrent path
substitution.

Exit codes are 0 when the requested checks pass, 1 for malformed or unclosed IR
including a representation-rule violation, 2 for usage errors, and 5 for
unavailable input, unsupported container capability, resource exhaustion or I/O.
An exit 1 about an unclosed supplied set is not a claim that its source is invalid
Lean. Resource exhaustion is not a type rejection.

## Embedding

- `ir_validate::validate_ir` checks an in-memory module closure structurally.
  A caller may supply reviewed external names and arities explicitly; that map
  is not loaded from or checked against a census automatically.
- `ir_validate::build_validated_ir_call_graph` structurally validates every
  declaration, including unreachable declarations, before building the graph.
- `ir_types::validate_ir_types` composes structural and representation checking
  in memory, sharing one work limit and leaving input unchanged.
- `ir_files::check_ir_files` retains the structural-only file API.
  `ir_files::check_ir_files_with_types` adds representation checking before any
  graph is returned. `CheckedIrFiles.representation` is `Some` only when the
  representation pass actually ran.
- `ir_files::ir_graph_dot` exports the structural graph under a byte cap.

Structural checking covers definition-before-use, lexical scopes,
declaration-wide variable/join index uniqueness, static callee closure, and
full-call, partial-call and jump arities. Join points are visible in their
continuation, not their own value. Function recursion is allowed. A census-only
callee is displayed as `signature-only`; it has no invented IR body.

## Expression representation rules

The native pass follows `IRType.isObj`, `IRType.isScalar` and `Checker.checkExpr`
in the vendored pin. It checks boxed application results and closure operands,
reference constructor results, reset/reuse, scalar box/unbox operations, object
and aggregate projections, usize/scalar projections, string literals and
`isShared`. Aggregate field equality checks owners, field counts and nested
types iteratively, without recursive cloning or printing of hostile types.
`void` belongs to the pin's object category but is not a valid `proj` source;
`tagged` projections retain the pin's permissive result-type rule.

This is not complete IR typing or runtime safety. As in the pin's expression
checker, full applications do not compare argument/result types, numeric
literals have no result-type rule, and returns/mutation/RC instructions retain
structural checks only. Constructor-layout bounds, ownership, reference-count
balance and linear aggregate use remain unproved. External arities do not
establish ABI type signatures.

## Evidence and remaining contract

The initial structural/file implementation introduced 49 regression tests.
The representation increment adds 16 expression-rule tests, three file-API
controls and two native-command tests. These are authored tests, not a claim
that they executed in the implementation session. That session lacked a local
Rust toolchain and network access; the existing hosted and self-hosted jobs
were queued. The real boxed-Nat test decodes a committed Reference declaration
and alters exactly one box annotation; other cases construct IR or synthetic
containers using the generated layout. The command tests re-envelope an
unchanged pinned declaration in a synthetic wrapper.

Run `cargo test --locked -p fln-olean` and
`cargo clippy --locked -p fln-olean --all-targets -- -D warnings`. The focused
workflow runs beside the unchanged repository quality gate, not instead of it.

Remaining: full pinned-corpus validation, complete IR typing and ownership
checking, census/extern reconciliation, hostile-container acceptance coverage,
and the canonical content-hashed, census-classified graph artifact required by
the bead. DOT is diagnostic output, not that durable artifact. No kernel
authority, Reference execution permission, or full source compatibility follows
from a successful validation.
