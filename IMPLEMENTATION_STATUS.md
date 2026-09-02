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

**Evidence grade for the Nat step in this document: artifact-bound, not observed in the session that added this status file.** Run:

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

The repository contains source-to-kernel and source-to-Golem paths for a growing bounded subset, including caller-named definitions, imports, `#check`, Nat/Bool/String operations, and emitted intermediate/artifact forms. This is meaningful executable ground, not full source-language compatibility.

### Lantern / LSP server

**Status: usable bounded transport, Full document synchronization, synchronous diagnostic waiting, and layered client/server transcript evidence; semantic editor and daemon architecture remain incomplete.**

#### Transport, parser, and wire ground

Landed:

- Content-Length-framed stdio with bounded header bytes, field count, and message size; strict duplicate `Content-Length` / `Content-Type` refusal; canonical CRLF framing; UTF-8-only `application/vscode-jsonrpc` token and quoted charset support; and write-side failure atomicity for oversized messages.
- A structural JSON decoder for the supported JSON-RPC/LSP surface. It validates the complete value before dispatch, bounds nesting, rejects malformed strings/numbers/literals/containers and duplicate selected fields, and distinguishes parse errors (`-32700`) from structurally invalid requests (`-32600`).
- Root envelope fields cannot be impersonated by nested payload content. Document fields are resolved only from their exact `params`, `params.textDocument`, and one-element Full-sync `params.contentChanges` containers.
- Request-ID identity is explicit: number lexemes remain exact, strings compare by decoded Unicode value and are re-escaped canonically, and `null` remains `null`.
- Deterministic wire constructors for lifecycle responses, errors, progress, warnings, diagnostic clearing, and non-authoritative callback faults. Unit cells round-trip the emitted shapes through the same strict parser used on inbound traffic.

#### Live lifecycle and document authority

Landed:

- LSP lifecycle (`initialize`, `initialized`, `shutdown`, `exit`) with `utf-16` position-encoding advertisement and Full text synchronization.
- Full-sync `didOpen`, `didChange`, `didSave`, and `didClose`. Ranged/incremental fragments, duplicate opens, unopened changes/saves, non-monotone versions, and malformed transitions fail closed rather than silently changing state.
- Open-document membership and accepted versions remain authoritative independently of retained source bytes. Cache pressure cannot implicitly close a document or erase version monotonicity.
- Session-local state is independently bounded to 1,024 open documents, 256 MiB of retained source, and 4 MiB of aggregate document-URI keys. An oversized URI is refused before source-retention accounting or checking begins.
- Textless `didSave` rechecks the newest retained full snapshot; missing or invalidated text is visible and cannot replay stale content.
- Accounting recovery invalidates affected text and rebuilds source-byte and URI-key aggregates from surviving open documents. Impossible or over-budget reconstruction discards retained text while preserving open/version authority.
- `didClose` removes document/source/publication state, releases source and URI accounting, clears push diagnostics, and deterministically fails waits that can no longer complete.

#### Diagnostic publication and wait authority

Landed:

- Document checks are bracketed by `$/lean/fileProgress` processing/complete notifications.
- Callback output is structurally parsed before publication. A nested method-looking string, malformed JSON, response-shaped message, duplicate terminal class, or publication for another URI cannot masquerade as the current document's terminal result.
- Exactly one current-document diagnostic publication class may coexist with one canonical `$/lean/diagnosticOutcome`.
- Canonical zero-diagnostic success is a four-part covenant: current projection schema, `outcome:"complete"`, `authority:true`, and exact unsigned integer `diagnosticCount:0`.
- `inconclusive` and `internal_fault` require `authority:false` and omit the complete-only count. Their details remain visible, but the publication frontier fails and editor diagnostics are cleared.
- Missing, malformed, or ambiguous terminal callback output is withheld as authority, clears stale diagnostics, and emits a schema-bound non-authoritative internal fault.
- Accepted document state and emitted diagnostic authority are separate frontiers. `textDocument/waitForDiagnostics` is satisfied only by the latter.
- Immediate and future-version waits use one monotone publication frontier. A non-authoritative result fails matching waits; a later authoritative save at the same version can recover it.
- Pending waits are bounded to 4,096 requests and 4 MiB of retained request-ID/URI metadata. Duplicate outstanding IDs and capacity overflow are typed failures.
- `$/cancelRequest`, close, and shutdown release pending waits exactly once and in deterministic registration order.

#### Client transcript evidence

Landed:

- `fln-lsp-validate` supports three intentionally different grades: syntax-only, `--client-lifecycle`, and `--client-session`.
- Syntax-only `fln.lsp-transcript-validation/2` remains available for negative fixtures and reports complete `wireBytes` separately from JSON `bodyBytes`.
- `fln.lsp-client-lifecycle/1` binds initialize, initialized, shutdown, and exit frame indices plus known method roles and parameter-container contracts.
- `fln.lsp-client-session/3` adds Full-sync document semantics, open-document membership, monotone versions, covered versus future diagnostic-wait classification, canonical request-ID uniqueness, and cancellation-target authority.
- Strict client-session request IDs are globally unique because a client-only recording lacks server-response timing needed to prove safe reuse.
- Every cancellation target must identify one prior non-null request under the same canonical ID policy; duplicate cancellation targets fail closed. Targets are classified as diagnostic waits or other requests.
- Client request identity is independently bounded to 262,144 IDs and 32 MiB of canonical ID bytes. Cancellation state is stored on the bounded request record rather than retaining a second target-ID map.
- Client document state remains bounded to 1,024 open documents and 4 MiB of aggregate URI keys. The semantic transcript pass does not retain source text after validating each event.
- `fln-lsp-replay --client-lifecycle` and `--client-session` perform preflight before dispatcher execution, expected-stream comparison, stdout emission, or create-new output publication. Default replay remains available for deliberately invalid fixtures.
- `fln-lsp-inspect` emits metadata-only `fln.lsp-frame/2` rows and omits parameter/source contents.

#### Server and bidirectional transcript evidence

Landed:

- `fln-lsp-server-validate` validates notifications and result/error responses independently of the client stream.
- `fln.lsp-server-transcript/3` distinguishes result responses, error responses, diagnostic publications, diagnostic outcomes, file-progress notifications, log messages, and unknown notifications.
- Known notification payloads are structurally validated: nonempty document identities, required arrays/strings, MessageType range, optional diagnostic versions, and the diagnostic outcome/authority/count covenant.
- Server transcript wire bytes, body bytes, decoded method/ID metadata bytes, one-million-frame limit, and 32 MiB decoded-metadata limit are explicit.
- Server-initiated requests remain outside the current bounded profile and are refused rather than misclassified as responses.
- `fln-lsp-correlate CLIENT SERVER` requires a strict client session and strict server transcript, then joins every globally unique canonical client request ID to exactly one server response.
- Correlation independently rebuilds the client request index and requires its count and byte accounting to agree with `fln.lsp-client-session/3` before accepting the join.
- Missing, duplicate, unsolicited, and numerically normalized response IDs fail closed. Equivalent JSON string escape spellings correlate by decoded value.
- Client-request, server-response, and cancellation-target indexes are independently bounded to 262,144 IDs and 32 MiB of canonical ID bytes.
- `fln.lsp-client-server-correlation/4` carries document counts, covered/future waits, cancellation target classes, and eventual response classes for cancelled targets.
- Cancelled-target responses are classified as `RequestCancelled` (`-32800`), normal result, or another valid error. The three counts must cover every cancellation target.
- A normal result for a cancelled target is disclosed, not rejected: cancellation is advisory and separately recorded streams do not establish whether completion raced with cancellation.
- Public installed-binary tests cover successful and failed session validation, cancellation identity, preflight side-effect isolation, server payload refusal, canonical ID joins, and cancelled-target response classification.
- [`docs/LANTERN_WIRE_REPLAY.md`](docs/LANTERN_WIRE_REPLAY.md) is the operational contract for these evidence tools.

#### Still incomplete

- The production CLI callback still uses the compatibility `fln_server::project` entry point rather than `project_with_sources`; the projector has UTF-16/source-aware support, but the exact unsaved snapshot is not yet passed through that large CLI bridge. Current file-level engine failures are predominantly positioned at `(1, 0)`.
- Client/server recordings have no shared event clock. Correlation establishes identity, shape, counts, and cancellation-response classes, not cross-stream timing or proof that a response followed its cancellation.
- Arbitrary method-specific result semantics remain unvalidated. The correlator does not yet prove that initialize, hover, completion, definition, goals, or extension results have the correct inner schema.
- Server notification counts are typed, but complete document-to-progress-to-publication causality across both streams is not yet joined.
- `$/lean/plainGoal` / `$/lean/plainTermGoal` do not expose cursor-aware proof state. Hover, completion, and definition remain no-information responses.
- Lean RPC sessions/calls are explicitly **not implemented**. `rpc/connect` and `rpc/call` fail visibly; keepAlive/release do not fabricate a session.
- Retained source is session-local input state, not the declaration-granular shared elaboration/import environment required by the finished Lantern design.
- The server remains synchronous and does not implement asupersync regions, active elaboration cancellation, shared immutable import heaps, stable diagnostic identities, crash isolation, a timestamped bidirectional trace, or the full unmodified-vscode-lean4 parity matrix.

The latest Lantern session, cancellation, server-stream, correlation, replay, accounting, callback-authority, and wait changes are **landed**. This status file does not claim they were compiled in the same editing session because the available environment lacked `cargo`/`rustc` and hosted Actions were intentionally not used.

### Agent-control plane

**Status: executable governance tools exist, not just prose.**

Landed:

- [`AGENT_FRONTIER_PROTOCOL.md`](AGENT_FRONTIER_PROTOCOL.md): immutable anchors, semantic ownership, typed frontiers, negative evidence, and promotion rules.
- Read-only frontier capsule auditing and Git-anchor recording.
- Deterministic Beads frontier selection with fail-closed handling of malformed graphs and uncertain hard-filter facts.
- Deterministic blocker-cycle detection with stable concrete witnesses rather than empty-ready-set ambiguity.

This is intended to make agent work **accretive**: failed hypotheses and verified frontiers become reusable state rather than being rediscovered from commit prose.

### ABI / runtime / compiler / build / tactics / search / docs / MCP / WASM

**Status: mixed partial implementation.**

These subsystems contain real contract planes, data structures, bounded execution slices, or integration work, but the repository has **not** reached the README's finished-system claims. Full mathlib-compatible elaboration/tactic execution, the complete native `Lean.*` Mirror, full Lake/Ledger behavior, production Iron codegen/JIT, full semantic LSP/RPC, complete MCP orchestration, and release-grade cross-platform distribution remain active program work.

---

## High-priority open proof obligations

1. **Advance `fln-51y8` with real pinned evidence.** Execute the pinned Nat council locally, then continue the exact Prelude first-failure frontier rather than generalizing from fixtures.
2. **Migrate the live CLI callback to source-aware projection.** Pass the exact unsaved URI/text/version into `project_with_sources` without duplicating or weakening dispatcher publication authority.
3. **Keep independent-checker authority boundaries intact.** The checker may veto or observe; it must never become a second admission authority.
4. **Replace no-information editor scaffolding with truthful semantics one method at a time.** Never fabricate goals, hover data, completions, definitions, or RPC sessions merely to suppress editor errors.
5. **Promote source retention into real declaration/elaboration state deliberately.** The bounded latest-text cache supports truthful Full-sync lifecycle semantics; it is not dependency-aware incremental elaboration or import invalidation.
6. **Join document and server-notification causality.** Add a shared event clock or interleaved trace, active-request lifetime, method/result contracts, environment/epoch/executable identity, final daemon state, first divergence, and production-callback evidence. Count correlation alone cannot establish those facts.
7. **Keep the JSON-RPC parser narrow but structurally correct.** Extend typed extraction deliberately; do not reintroduce substring routing or unbounded generic decoding.
8. **Prefer executable frontier evidence over narrative status.** New compatibility claims should name a reproducer, pin/artifact identity, and outcome class.

---

## Local verification commands for the latest frontier

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

The ordinary `pinned_nat_council` target leaves the real-artifact cell ignored; the Python runner is the explicit non-vacuous invocation.

Project-wide release/gate claims require the repository's broader governed evidence procedures, not just these focused commands.
