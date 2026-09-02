# FrankenLean implementation status

This file is the **current-state companion** to the target-state README and the comprehensive design plan.

- [`README.md`](README.md) intentionally describes the finished 1.0 system in present tense.
- [`COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md`](COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md) is the architectural and execution specification.
- [`CHANGELOG.md`](CHANGELOG.md) records what landed over time.
- **This file answers: what is implemented now, what evidence exists now, and what remains open?**

Do not promote a row from *implemented* to *verified* merely because code or a test exists. A runnable real-artifact test that has not been executed at the current pin is still pending evidence.

## Evidence vocabulary

| State | Meaning |
|---|---|
| **landed** | Code is committed on `main`; no claim is made here that the relevant runtime test was executed in the same session. |
| **model-verified** | A focused synthetic/model test exists and has previously been exercised, but the claim is not yet bound to the real pinned artifact. |
| **artifact-bound** | The repository contains a test/runner that consumes the real pinned Reference artifact and fails closed once that artifact is present. |
| **observed** | A concrete run against the real pinned artifact is retained or recorded with enough identity to reproduce it. |
| **target** | Architectural/product intent, not current implementation evidence. |

The project-wide evidence matrix and Beads tracker remain authoritative where they carry stronger, fresher evidence than this summary.

---

## Current frontier summary

### Crucible / independent checker

**Status: active implementation; substantial bounded ground is live.**

Landed checker ground includes declaration admission, definitional equality and inference support, quotient initialization, multiple fixed and shape-derived inductive families, nonrecursive field-bearing inductives, direct recursive-family machinery, and the independent-veto council path used by the product facade.

Recent critical-path work:

- `Init.HEq` reconstruction was corrected to match the pinned eliminator's hygienic rebinding rather than the stale synthetic two-argument motive shape.
- The direct-recursive `Nat` model fixture was corrected so the successor minor really encodes `motive n -> motive (Nat.succ n)`; negative cells assert the specific constructor/recursor rejection class.
- `crates/fln-conformance/tests/pinned_nat_council.rs` decodes the **real** pinned `Nat`, `Nat.zero`, `Nat.succ`, and `Nat.rec` rows from the `Init.Prelude` companion chain and submits that exact block through the normal K1 + independent-checker `Engine::admit_declaration` door.
- `scripts/check_pinned_nat_council.py` derives the Reference tag from `SUITE.lock`, requires the complete Prelude companion chain, and invokes exactly that ignored real-artifact cell. An explicit invocation cannot report a hollow green when the pin is absent.

**Evidence grade for the Nat step in this document: artifact-bound, not observed in the session that added this status file.** The local execution environment used for the latest edits did not contain `cargo`/`rustc`, so this document deliberately does not claim that the pinned-Nat runner passed. Run:

```bash
python3 scripts/check_pinned_nat_council.py
```

on a host with the pinned toolchain to promote that claim with real evidence.

The broader `fln-51y8` Prelude council milestone remains open until the complete pinned `Init.Prelude` frontier is demonstrated, not merely the Nat cell.

### `.olean` / Reference artifact plane

**Status: substantial bounded implementation, still incomplete.**

Landed surfaces include split-artifact parsing, declaration decoding, bounded inspection/diff tooling, olean reconstruction for multiple authority units, provenance/chain auditing, standalone checkable snapshots, and the `fln check-olean` council path.

The Reference remains an **oracle and fixture source only**. No upstream implementation executes as a FrankenLean runtime component.

### Native source pipeline and Golem

**Status: bounded executable vertical slices are live; general Lean elaboration/runtime parity is not complete.**

The repository contains source-to-kernel and source-to-Golem paths for a growing bounded subset, including caller-named definitions, imports, `#check`, Nat/Bool/String operations and emitted intermediate/artifact forms. This is meaningful executable ground, not full source-language compatibility.

### Lantern / LSP server

**Status: usable bounded transport, Full document synchronization, and synchronous diagnostic waiting; semantic editor and daemon architecture remain incomplete.**

Landed transport and syntax ground:

- Content-Length-framed stdio with bounded header bytes, field count, and message size; strict duplicate `Content-Length` / `Content-Type` refusal; canonical CRLF framing; UTF-8-only `application/vscode-jsonrpc` token and quoted charset support; and write-side failure atomicity for oversized messages.
- A complete structural JSON decoder for the supported JSON-RPC/LSP surface. It validates the entire value before dispatch, bounds nesting, rejects malformed strings/numbers/literals/containers and duplicate selected fields, and distinguishes parse errors (`-32700`) from structurally invalid requests (`-32600`).
- Root envelope fields cannot be impersonated by nested payload content. Document fields are resolved only from their exact `params`, `params.textDocument`, and one-element Full-sync `params.contentChanges` containers.
- JSON-RPC request IDs preserve syntactically valid JSON number lexemes, decoded strings, and `null` without integer narrowing or normalization. A malformed or ambiguous ID is not erased into a notification.
- Deterministic wire constructors for lifecycle responses, errors, progress, warnings, diagnostic clearing, and non-authoritative callback faults. Unit cells round-trip every constructor through the same strict parser used on inbound traffic.

Landed lifecycle and document authority:

- LSP lifecycle (`initialize`, `initialized`, `shutdown`, `exit`) with `utf-16` position-encoding advertisement and Full text synchronization.
- Full-sync `didOpen`, `didChange`, `didSave`, and `didClose` handling. Ranged/incremental fragments, duplicate opens, unopened changes/saves, non-monotone versions, and malformed transitions fail closed rather than silently changing state.
- Open-document membership and accepted versions are authoritative independently of retained source bytes. Cache pressure therefore cannot implicitly close a document or erase version monotonicity.
- Session-local source retention is bounded to 1,024 documents and 256 MiB. Textless `didSave` rechecks the newest retained full snapshot; missing or invalidated text is visible and cannot replay stale content.
- Retained-source accounting recovery invalidates the affected text and rebuilds the exact aggregate from unaffected documents where possible; impossible or over-budget reconstructed states discard all retained text while preserving open/version authority.
- `didClose` removes document/source/publication state, clears push diagnostics, and deterministically fails waits that can no longer complete.

Landed diagnostic-publication authority:

- Document checks are bracketed by `$/lean/fileProgress` processing/complete notifications.
- Callback output is parsed structurally before being written. A nested method-looking string, malformed JSON, response-shaped message, duplicate terminal class, or `publishDiagnostics` for another URI cannot masquerade as the current document's terminal result.
- Exactly one current-document diagnostic publication class may coexist with one canonical `$/lean/diagnosticOutcome`. Canonical `authority:true` advances the publication frontier; `authority:false` is retained as diagnostic evidence but grades the frontier failed and forces an editor-visible diagnostic clear.
- Missing, malformed, or ambiguous terminal callback output is withheld as authority, clears stale diagnostics, and emits a schema-bound non-authoritative internal-fault outcome. The callback cannot turn “no answer” into an empty success.
- Accepted document text/version and emitted diagnostic authority are separate frontiers. `textDocument/waitForDiagnostics` is satisfied only by the latter.

Landed bounded diagnostic synchronization:

- `textDocument/waitForDiagnostics` accepts the pinned Lean shape `{ uri, version }` and returns `{}` only after a terminal diagnostic result for at least that version has been emitted.
- Immediate and future-version waits use the same monotone publication frontier. A non-authoritative result fails matching waits with `RequestFailed` instead of claiming diagnostic completion; a later authoritative save at the same version can recover the frontier.
- Pending waits are bounded to 4,096 requests and 4 MiB of retained request-ID/URI metadata. Duplicate outstanding IDs and capacity overflow are typed failures.
- `$/cancelRequest`, document close, and shutdown release every pending wait exactly once and in deterministic registration order.
- Public framed-stdio transcript tests cover lifecycle ordering, Full-sync replay, malformed JSON and UTF-8 recovery, callback spoofing and malformed output, wait success/failure/recovery, cancellation, close, shutdown, and unsupported RPC.

Still incomplete:

- The production CLI callback still uses the compatibility `fln_server::project` entry point rather than `project_with_sources`; the projector has UTF-16/source-aware support, but exact unsaved source is not yet passed through that large CLI bridge. Current file-level engine errors are positioned at `(1, 0)`; broader source-position claims remain open until that call site is migrated.
- `$/lean/plainGoal` / `$/lean/plainTermGoal` do not yet expose cursor-position-aware proof state.
- Hover, completion, and definition currently return no-information `null` responses rather than semantic results.
- Lean RPC sessions/calls are explicitly **not implemented**. `rpc/connect` and `rpc/call` return `RequestFailed`; session-only keepAlive/release notifications are visibly ignored rather than fabricating state.
- Retained source is session-local input state, not the declaration-granular shared elaboration/import environment required by the finished Lantern design.
- The server is synchronous and does not yet implement asupersync regions, cancellation of active elaboration, shared immutable import heaps, stable diagnostic identities, replay bundles, or the full unmodified-vscode-lean4 parity matrix.

The latest Lantern parser, session, callback-authority, and wait changes are **landed**. This status file does not claim they were compiled in the session that wrote it because that execution environment lacked a Rust toolchain and hosted Actions were unavailable.

### Agent-control plane

**Status: executable governance tools now exist, not just prose.**

Landed:

- [`AGENT_FRONTIER_PROTOCOL.md`](AGENT_FRONTIER_PROTOCOL.md): immutable anchors, semantic ownership, typed frontiers, negative evidence and promotion rules.
- read-only frontier capsule auditing and Git-anchor recording.
- deterministic Beads frontier selection with fail-closed handling of malformed tracker graphs and uncertain hard-filter facts.
- deterministic blocker-cycle detection with stable concrete witnesses instead of an empty-ready-set ambiguity.

This is intended to make agent work **accretive**: failed hypotheses and verified frontiers become reusable state rather than being rediscovered from commit prose.

### ABI / runtime / compiler / build / tactics / search / docs / MCP / WASM

**Status: mixed partial implementation.**

These subsystems contain real contract planes, data structures, bounded execution slices, or integration work, but the repository has **not** reached the README's finished-system claims. In particular, full mathlib-compatible elaboration/tactic execution, the complete native `Lean.*` Mirror, full Lake/Ledger behavior, production Iron codegen/JIT, full semantic LSP/RPC, complete MCP orchestration, and release-grade cross-platform distribution remain active program work.

---

## High-priority open proof obligations

1. **Advance `fln-51y8` with real pinned evidence.** Execute the pinned Nat council locally, then continue the exact Prelude first-failure frontier rather than generalizing from fixtures.
2. **Migrate the live CLI server callback to source-aware projection.** Pass the exact unsaved URI/text/version into `project_with_sources` without duplicating or weakening the dispatcher publication frontier.
3. **Keep independent-checker authority boundaries intact.** The checker may veto/observe; it must never become a second admission authority.
4. **Replace LSP no-information scaffolding with truthful semantics one method at a time.** Never fabricate sessions, goals, hover data, completions, or definitions to suppress editor errors.
5. **Promote source retention into real declaration/elaboration state deliberately.** The bounded latest-text cache is enough to make Full-sync lifecycle semantics truthful; it is not a substitute for dependency-aware incremental elaboration, import invalidation, or cursor-position proof state.
6. **Keep the JSON-RPC parser narrow but structurally correct.** Extend its typed extraction vocabulary deliberately; do not reintroduce substring routing or unbounded generic decoding.
7. **Prefer executable frontier evidence over narrative status.** New compatibility claims should name a reproducer, pin/artifact identity, and outcome class.

---

## Local verification commands for the latest frontier

On a host with the pinned Rust and Reference toolchains:

```bash
cargo fmt --all -- --check
cargo test --locked -p fln-server --no-fail-fast
cargo clippy --locked -p fln-server --all-targets -- -D warnings
cargo test --locked -p fln-checker --no-fail-fast
cargo test --locked -p fln-conformance --test pinned_nat_council
python3 scripts/check_pinned_nat_council.py
```

The ordinary `pinned_nat_council` target leaves the real-artifact cell ignored; the Python runner is the explicit non-vacuous invocation.

Project-wide release/gate claims require the repository's broader governed evidence procedures, not just these focused commands.
