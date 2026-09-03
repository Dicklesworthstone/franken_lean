# FrankenLean implementation status

This file is the **current-state companion** to the target-state README and the comprehensive design plan.

- [`README.md`](README.md) intentionally describes the finished 1.0 system in present tense.
- [`COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md`](COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md) is the architecture and execution specification.
- [`CHANGELOG.md`](CHANGELOG.md) records what landed over time.
- **This file answers what is implemented now, what evidence exists now, and what remains open.**

Do not promote a row from implemented to verified merely because code or a test exists. A runnable test that was not executed against the relevant build or artifact remains pending evidence.

## Evidence vocabulary

| State | Meaning |
|---|---|
| **landed** | Code is committed on `main`; no claim is made that the relevant runtime test ran in the same session. |
| **model-verified** | A focused synthetic/model test exists and has previously run, but the claim is not bound to the real pinned artifact. |
| **artifact-bound** | A repository-owned test or runner consumes the real pinned Reference artifact and fails closed when that artifact is absent. |
| **observed** | A concrete run against the real pinned artifact is retained with enough identity to reproduce it. |
| **target** | Architectural or product intent, not current implementation evidence. |

The evidence matrix and Beads tracker remain authoritative where they carry stronger, fresher evidence than this summary.

---

## Current frontier summary

### Crucible / independent checker

**Status: active implementation; substantial bounded ground is live.**

Landed checker ground includes declaration admission, inference and definitional equality, quotient initialization, several fixed and shape-derived inductive families, nonrecursive field-bearing inductives, direct recursive-family machinery, and the independent-veto council path used by the product facade.

Recent critical-path work includes:

- corrected `Init.HEq` recursor reconstruction matching the pinned eliminator's hygienic rebinding;
- corrected direct-recursive `Nat` model evidence and forged-recursion refusal cells;
- a real-artifact Nat council regression that decodes `Nat`, `Nat.zero`, `Nat.succ`, and `Nat.rec` from the pinned `Init.Prelude` companion chain and sends that exact block through the ordinary K1 plus independent-checker admission door;
- `scripts/check_pinned_nat_council.py`, which derives the Reference tag from `SUITE.lock`, requires the complete companion chain, and cannot produce a hollow green when the artifact is absent.

**Current evidence grade for the Nat step: artifact-bound.** The complete `fln-51y8` sequential `Init.Prelude` council remains open; a bounded Nat cell is not evidence that the whole Prelude frontier passed.

### `.olean` / Reference artifact plane

**Status: substantial bounded implementation, still incomplete.**

Landed surfaces include split-artifact parsing, declaration decoding, bounded inspection and diff tooling, reconstruction for several authority units, provenance/chain auditing, standalone checkable snapshots, and the `fln check-olean` council path.

The Reference remains an oracle and fixture source only. No upstream implementation executes as a FrankenLean runtime component.

### Native source pipeline and Golem

**Status: bounded executable vertical slices are live; general Lean elaboration and runtime parity are not complete.**

The repository contains source-to-kernel and source-to-Golem paths for a growing bounded subset, including caller-named definitions, imports, `#check`, Nat/Bool/String operations, and emitted intermediate/artifact forms. This is meaningful executable ground, not full source-language compatibility.

### Lantern / LSP server

**Status: usable bounded transport, Full document synchronization, synchronous diagnostic waiting, and layered client/server transcript evidence; semantic editor and daemon architecture remain incomplete.**

#### Transport, parser, and wire ground

Landed:

- Content-Length-framed stdio with bounded header bytes, field count, and message size; strict duplicate `Content-Length` and `Content-Type` refusal; canonical CRLF framing; UTF-8-only `application/vscode-jsonrpc`; and failure-atomic bounded writes.
- Structural JSON decoding for the supported JSON-RPC/LSP surface. Complete values are validated before dispatch, nesting is bounded, malformed strings/numbers/literals/containers and duplicate selected fields are rejected, and parse errors remain distinct from invalid requests.
- Root envelope fields cannot be impersonated by nested payload content. Document fields are read only from their exact structural containers.
- Request-ID identity is explicit: number lexemes remain exact, strings compare by decoded Unicode value and canonical JSON escaping, and `null` remains `null`.
- Deterministic constructors for lifecycle responses, errors, progress, warnings, diagnostic clearing, and non-authoritative callback faults.

#### Live lifecycle and document authority

Landed:

- `initialize`, `initialized`, `shutdown`, and `exit`, with UTF-16 position encoding advertised and Full text synchronization selected.
- Full-sync `didOpen`, `didChange`, `didSave`, and `didClose`. Ranged/incremental fragments, duplicate opens, unopened changes/saves, non-monotone versions, and malformed transitions fail closed.
- Open-document membership and accepted versions remain authoritative independently of retained source bytes.
- Session-local state is independently bounded to 1,024 open documents, 256 MiB of retained source, and 4 MiB of aggregate URI keys.
- Textless saves recheck the newest retained snapshot. Missing or invalidated text is visible and cannot replay stale source.
- Accounting recovery rebuilds source-byte and URI-key aggregates from surviving documents where possible, otherwise discards retained text while preserving open/version authority.
- Close removes document, source, and publication state, clears push diagnostics, and resolves waits that can no longer complete.

#### Diagnostic publication and wait authority

Landed:

- Checks are bracketed by `$/lean/fileProgress` processing and completion notifications.
- Callback output is structurally parsed before publication. Nested method-looking text, malformed JSON, response-shaped output, duplicate terminal classes, and publications for another URI cannot masquerade as the current document's result.
- One current-document diagnostic publication may coexist with one canonical `$/lean/diagnosticOutcome`.
- Canonical zero-diagnostic success requires the current projection schema, `outcome:"complete"`, `authority:true`, and exact integer `diagnosticCount:0`.
- `inconclusive` and `internal_fault` require `authority:false`; details remain visible, the publication frontier fails, and stale diagnostics are cleared.
- Missing, malformed, or ambiguous terminal callback output cannot become an empty success.
- Accepted document state and diagnostic-publication authority are separate frontiers. `textDocument/waitForDiagnostics` is satisfied only by the latter.
- Immediate and future-version waits use one monotone publication frontier. Non-authoritative processing fails matching waits; a later authoritative save at the same version may recover the frontier.
- Pending waits are bounded to 4,096 requests and 4 MiB of retained request-ID/URI metadata.
- Cancellation, close, and shutdown resolve pending waits exactly once in deterministic order.

#### Client transcript evidence

Landed:

- `fln-lsp-validate` exposes syntax-only, `--client-lifecycle`, and `--client-session` grades.
- `fln.lsp-transcript-validation/2` reports complete framed `wireBytes` separately from JSON `bodyBytes` and remains usable for negative fixtures.
- `fln.lsp-client-lifecycle/1` binds initialize/initialized/shutdown/exit positions plus known method role and parameter-container contracts.
- `fln.lsp-client-session/3` adds Full-sync document semantics, monotone versions, covered-versus-future waits, canonical request-ID uniqueness, and cancellation-target authority.
- Every cancellation target must name an earlier non-null request under the same canonical identity policy; duplicate cancellation of one target fails closed.
- Client request identity is bounded to 262,144 IDs and 32 MiB of canonical ID bytes. Cancellation state is stored on the bounded request record rather than copying each ID into another map.
- Document state remains bounded to 1,024 open documents and 4 MiB of aggregate URI keys. Source text is validated but not emitted in receipts.
- Strict replay preflight occurs before dispatcher execution, expected-stream comparison, stdout emission, or create-new output publication. Default replay remains available for deliberately invalid fixtures.
- `fln-lsp-inspect` emits metadata-only `fln.lsp-frame/2` rows and omits parameter and source contents.

#### Server transcript and bidirectional evidence

Landed:

- `fln-lsp-server-validate` validates notifications and result/error responses independently of a client recording.
- `fln.lsp-server-transcript/3` separates result responses, error responses, diagnostic publications, diagnostic outcomes, file-progress notifications, log messages, and unknown notifications.
- Known notification payloads receive structural validation: nonempty document identities, required arrays and strings, MessageType range, optional diagnostic versions, and the diagnostic outcome/authority/count covenant.
- Server wire bytes, body bytes, decoded method/ID bytes, frame ceiling, and decoded-metadata ceiling are explicit.
- Server-initiated requests remain outside the current bounded profile and are refused rather than misclassified.
- `fln-lsp-correlate CLIENT SERVER` requires a strict client session and strict server transcript, then joins every canonical client request ID to exactly one server response.
- Correlation independently rebuilds request and cancellation indexes and requires their accounting and prior-request facts to agree with the client-session pass.
- Missing, duplicate, unsolicited, and numerically normalized response IDs fail closed. Equivalent JSON string spellings correlate by decoded value.
- Client-request, server-response, and cancellation-target indexes are independently bounded to 262,144 IDs and 32 MiB of canonical ID bytes.
- Correlation schema `fln.lsp-client-server-correlation/5` names `fln.lsp-method-response/1` and validates each response against the current bounded dispatcher's outer method contract:
  - `initialize` returns an object;
  - `shutdown` returns `null`;
  - `waitForDiagnostics` returns an object, `RequestCancelled`, or `RequestFailed`;
  - plain goals, term goals, hover, completion, and definition return the current no-information `null` result;
  - unsupported Lean RPC calls return `RequestFailed`;
  - unknown methods return `MethodNotFound`.
- Method-derived result and error counts must reconcile exactly with the server transcript's validated result/error totals, and every matched response must belong to one method contract class.
- The receipt exposes zero method-contract violations plus separate counters for initialize, shutdown, diagnostic-wait results/errors, no-information query results, unsupported-RPC errors, and unknown-method errors.
- Cancelled targets are also classified independently as `RequestCancelled`, normal result, or another valid error. A normal result is disclosed rather than rejected because cancellation is advisory and separate streams contain no shared event clock.
- Installed-binary tests bind the positive schema-v5 receipt and prove that a response with the correct ID but the wrong method behavior cannot produce a success receipt. In particular, `MethodNotFound` for hover is rejected because the live bounded dispatcher currently returns `null`.
- [`docs/LANTERN_WIRE_REPLAY.md`](docs/LANTERN_WIRE_REPLAY.md) is the operational contract for these evidence tools.

#### Still incomplete

- The production CLI callback now passes the exact unsaved document through `project_with_sources`, and a parse error is reported at its real source position (byte offset → `FileMap::to_position` → LSP UTF-16 column) instead of the file head. **Landed and tested** (`syntax_error_reports_a_real_utf16_source_position`, commit `2bf3a02a`). Remaining: **elaboration/type** errors are still positioned at `(1, 0)` because `NatDefinitionElabError` is message-only — the offending `Syntax` node's `BytePos` must be threaded through the elaborator's refusal type before those can be located (a new-implementation task, not wiring).
- Method-response schema v1 is an outer contract. It does not yet validate the complete initialize capability object or useful semantic payloads for goals, hover, completion, or definition. Successful diagnostic waits are currently classified as object-valued results rather than a deeper inner schema.
- Client and server recordings have no shared event clock. Correlation establishes identity, shape, counts, method classes, and cancellation-response classes, not response ordering or proof that a response followed cancellation.
- Complete document-to-progress-to-publication causality is not yet joined across both streams.
- Plain goals and term goals are not cursor-aware. Hover, completion, and definition still return no-information responses.
- Lean RPC sessions are not implemented. RPC calls fail visibly; keepAlive/release do not fabricate a session.
- Retained source is session-local input state, not a declaration-granular shared elaboration/import environment.
- The server remains synchronous and does not implement asupersync regions, active elaboration cancellation, shared immutable import heaps, stable diagnostic identities, crash isolation, a timestamped bidirectional trace, or full unmodified `vscode-lean4` parity.

The latest method-bound response, cancellation, session, server-stream, correlation, replay, accounting, callback-authority, and wait changes are **landed**. The environment used for this edit did not contain `cargo` or `rustc`, and hosted Actions were intentionally not used, so this status file does not claim a same-session green Rust run.

### Agent-control plane

**Status: executable governance tools exist, not just prose.**

Landed:

- [`AGENT_FRONTIER_PROTOCOL.md`](AGENT_FRONTIER_PROTOCOL.md): immutable anchors, semantic ownership, typed frontiers, negative evidence, and promotion rules.
- Read-only frontier capsule auditing and Git-anchor recording.
- Deterministic Beads frontier selection with fail-closed handling of malformed graphs and uncertain hard-filter facts.
- Deterministic blocker-cycle detection with concrete witnesses rather than empty-ready-set ambiguity.

This is intended to make agent work accretive: failed hypotheses and verified frontiers become reusable state rather than being rediscovered from commit prose.

### ABI / runtime / compiler / build / tactics / search / docs / MCP / WASM

**Status: mixed partial implementation.**

These subsystems contain real contract planes, data structures, bounded execution slices, or integration work, but the repository has not reached the README's finished-system claims. Full mathlib-compatible elaboration and tactics, the complete native `Lean.*` Mirror, full Lake/Ledger behavior, production Iron code generation and JIT, semantic LSP/RPC, complete MCP orchestration, and release-grade cross-platform distribution remain active program work.

---

## High-priority open proof obligations

1. **Advance `fln-51y8` with real pinned evidence.** Execute the pinned Nat council and continue the exact Prelude first-failure frontier rather than generalizing from fixtures.
2. **Give elaboration/type errors real positions.** Parse errors now project at their true UTF-16 position (obligation done, `2bf3a02a`); the remaining work is to capture the offending `Syntax` node's `BytePos` in `NatDefinitionElabError` and thread it through `NatDefinitionFrontendError::Elaborate` so type errors are located too, then reuse the same `primary_source_offset` → `FileMap::to_position` bridge.
3. **Keep independent-checker authority boundaries intact.** The checker may veto or observe; it must never become a second admission authority.
4. **Deepen method-result contracts deliberately.** Bind the exact initialize capability object and exact diagnostic-wait success payload before claiming those inner semantics.
5. **Replace no-information editor scaffolding with truthful semantics one method at a time.** Never fabricate goals, hover data, completions, definitions, or RPC sessions merely to suppress client errors.
6. **Promote retained text into real declaration and import state deliberately.** The latest-text cache supports truthful Full-sync lifecycle semantics; it is not dependency-aware incremental elaboration.
7. **Join client and server causality.** Add a shared event clock or interleaved trace, active-request lifetime, environment/epoch/executable identity, final daemon state, first divergence, and production-callback evidence.
8. **Keep JSON-RPC decoding narrow but structural.** Extend typed extraction deliberately; never reintroduce substring routing or unbounded generic decoding.
9. **Prefer executable frontier evidence over narrative status.** New compatibility claims should name a reproducer, pin or artifact identity, and outcome class.

---

## Focused local verification commands

On a host with the pinned Rust and Reference toolchains:

```bash
cargo fmt --all -- --check
cargo test --locked -p fln-server --all-targets --no-fail-fast
cargo clippy --locked -p fln-server --all-targets -- -D warnings
cargo test --locked -p fln-cli --lib --no-fail-fast
cargo clippy --locked -p fln-cli --lib -- -D warnings
cargo test --locked -p fln-checker --no-fail-fast
cargo test --locked -p fln-conformance --test pinned_nat_council
python3 scripts/check_pinned_nat_council.py
```

The ordinary `pinned_nat_council` target leaves the real-artifact cell ignored; the Python runner is the explicit non-vacuous invocation. Project-wide release claims require the broader governed evidence procedures, not only these focused commands.
