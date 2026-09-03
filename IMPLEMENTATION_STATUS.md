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
| **model-verified** | A focused synthetic or model test exists and has run, but the claim is not bound to the real pinned artifact. |
| **artifact-bound** | A repository-owned test or runner consumes the real pinned Reference artifact and fails closed when that artifact is absent. |
| **observed** | A concrete run against the relevant real build or pinned artifact is retained with enough identity to reproduce it. |
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

Landed surfaces include split-artifact parsing, declaration decoding, bounded inspection and diff tooling, reconstruction for several authority units, provenance and chain auditing, standalone checkable snapshots, and the `fln check-olean` council path.

The Reference remains an oracle and fixture source only. No upstream implementation executes as a FrankenLean runtime component.

### Native source pipeline and Golem

**Status: bounded executable vertical slices are live; general Lean elaboration and runtime parity are not complete.**

The repository contains source-to-kernel and source-to-Golem paths for a growing bounded subset, including caller-named definitions, imports, `#check`, Nat, Bool, and String operations, and emitted intermediate and artifact forms. This is meaningful executable ground, not full source-language compatibility.

### Lantern / LSP server

**Status: usable bounded transport, Full document synchronization, synchronous diagnostic waiting, source-aware installed entry points, and layered transcript evidence; semantic editor and daemon architecture remain incomplete.**

#### Transport, parser, and wire ground

Landed:

- Content-Length-framed stdio with bounded header bytes, field count, and message size; strict duplicate `Content-Length` and `Content-Type` refusal; canonical CRLF framing; UTF-8-only `application/vscode-jsonrpc`; and failure-atomic bounded writes.
- Structural JSON decoding for the supported JSON-RPC and LSP surface. Complete values are validated before dispatch, nesting is bounded, malformed strings, numbers, literals, and containers plus duplicate selected fields are rejected, and parse errors remain distinct from invalid requests.
- Root envelope fields cannot be impersonated by nested payload content. Document fields are read only from their exact structural containers.
- Request-ID identity is explicit: number lexemes remain exact, strings compare by decoded Unicode value and canonical JSON escaping, and `null` remains `null`.
- Deterministic constructors for lifecycle responses, errors, progress, warnings, diagnostic clearing, and non-authoritative callback faults.

#### Live lifecycle, source, and document authority

Landed:

- `initialize`, `initialized`, `shutdown`, and `exit`, with UTF-16 position encoding advertised and Full text synchronization selected.
- Full-sync `didOpen`, `didChange`, `didSave`, and `didClose`. Ranged or incremental fragments, duplicate opens, unopened changes and saves, non-monotone versions, and malformed transitions fail closed.
- Open-document membership and accepted versions remain authoritative independently of retained source bytes.
- Session-local state is independently bounded to 1,024 open documents, 256 MiB of retained source, and 4 MiB of aggregate URI keys.
- Textless saves recheck the newest retained snapshot. Missing or invalidated text is visible and cannot replay stale source.
- Accounting recovery rebuilds source-byte and URI-key aggregates from surviving documents where possible, otherwise discards retained text while preserving open and version authority.
- Close removes document, source, and publication state, clears push diagnostics, and resolves waits that can no longer complete.
- Both installed entry points, `fln serve-lsp` and `lean --server`, now use one shared binary-side adapter. The adapter checks the exact unsaved source and passes that URI and text snapshot to `project_with_sources`; it does not inspect rendered JSON substrings or create a second diagnostic authority.
- Engine diagnostics retain the exact editor URI, including already percent-encoded file URIs and non-hierarchical schemes. The installed regression forbids the old `%2520` double-encoding split.
- Parser refusal offsets now survive the parser, elaborator facade, engine error, `FileMap`, and source-aware projector. A real installed-binary test places a second-line error after a non-BMP character and observes the correct LSP UTF-16 coordinate.

**Evidence:** the source-aware installed bridge and parser-position path were compiled and exercised by the compiler-equipped session that landed `db4e3058` and `7e22255a`; the focused `fln-cli` LSP test reported 4 of 4 passing there.

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
- Pending waits are bounded to 4,096 requests and 4 MiB of retained request-ID and URI metadata.
- Cancellation, close, and shutdown resolve pending waits exactly once in deterministic order.

#### Client transcript evidence

Landed:

- `fln-lsp-validate` exposes syntax-only, `--client-lifecycle`, and `--client-session` grades.
- `fln.lsp-transcript-validation/2` reports complete framed `wireBytes` separately from JSON `bodyBytes` and remains usable for negative fixtures.
- `fln.lsp-client-lifecycle/1` binds initialize, initialized, shutdown, and exit positions plus known method role and parameter-container contracts.
- `fln.lsp-client-session/3` adds Full-sync document semantics, monotone versions, covered-versus-future waits, canonical request-ID uniqueness, and cancellation-target authority.
- Every cancellation target must name an earlier non-null request under the same canonical identity policy; duplicate cancellation of one target fails closed.
- Client request identity is bounded to 262,144 IDs and 32 MiB of canonical ID bytes. Cancellation state is stored on the bounded request record rather than copying each ID into another map.
- Document state remains bounded to 1,024 open documents and 4 MiB of aggregate URI keys. Source text is validated but not emitted in receipts.
- Strict replay preflight occurs before dispatcher execution, expected-stream comparison, stdout emission, or create-new output publication. Default replay remains available for deliberately invalid fixtures.
- `fln-lsp-inspect` emits metadata-only `fln.lsp-frame/2` rows and omits parameter and source contents.

#### Server, correlation, and interleaved causality evidence

Landed:

- `fln-lsp-server-validate` validates notifications and result or error responses independently of a client recording.
- `fln.lsp-server-transcript/3` separates result responses, error responses, diagnostic publications, diagnostic outcomes, file-progress notifications, log messages, and unknown notifications.
- Known notification payloads receive structural validation: nonempty document identities, required arrays and strings, MessageType range, optional diagnostic versions, and the diagnostic outcome, authority, and count covenant.
- Server wire bytes, body bytes, decoded method and ID bytes, frame ceiling, and decoded-metadata ceiling are explicit.
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
- Method-derived result and error counts must reconcile exactly with the server transcript's validated totals, and every matched response must belong to one method contract class.
- Cancelled targets are classified independently as `RequestCancelled`, normal result, or another valid error. Separate client and server streams disclose that result but cannot prove response order.
- `fln-lsp-timeline TIMELINE` adds a typed interleaved profile rather than guessing order between independent files. Every outer frame carries `fln.lsp-interleaved-event/1`, one direction, and one inner JSON-RPC object.
- The timeline rebuilds bounded client and server projections and subjects them to the existing strict session, server, correlation, cancellation, and method-response validators before making additional claims.
- `fln.lsp-interleaved-timeline/1` names `fln.lsp-cross-stream-causality/1` and proves, under `record-order-v1`, that responses follow their requests, the initialize response precedes `initialized`, the shutdown response precedes `exit`, cancellation precedes the target response, duplicate responses and cancellations are absent, and no event follows exit.
- The complete correlation-v5 receipt is nested inside the timeline receipt. Lifecycle event indices, outer and projected wire bytes, request-ID bytes, cancellation counts, enforced ceilings, and explicit zero-violation fields are retained.
- Timeline resources are bounded to 256 MiB of outer bytes, one million events, 256 MiB of combined projected client and server wire, 262,144 request IDs, and 32 MiB of canonical request-ID bytes.
- Repository-owned unit and installed-binary tests cover positive nested receipts plus response-before-request, initialized-before-response, exit-before-shutdown-response, cancellation-after-response, duplicate cancellation or response, and post-exit refusal. The end-of-options regression now passes a genuinely dash-prefixed relative path rather than an absolute `/tmp` path whose first byte was `/`.
- `scripts/build_lsp_timeline.py` constructs deterministic fixtures from `direction<TAB>raw JSON` lines without reserializing the inner message. Exact number lexemes and string escape spellings therefore survive into the validator input. It validates duplicate-free object JSON, directions, UTF-8, per-event and aggregate limits, and publishes through a complete staging inode plus no-clobber hard link.
- Fixture construction emits `fln.lsp-timeline-fixture-build/1` with input and output hashes, explicit byte counts, `authority:false`, and `purpose:"fixture-generation"`. This receipt identifies a fixture; it is not live-recorder or production causality evidence.
- [`docs/LANTERN_WIRE_REPLAY.md`](docs/LANTERN_WIRE_REPLAY.md) specifies all six transcript tools, and [`docs/LANTERN_TIMELINE_FIXTURES.md`](docs/LANTERN_TIMELINE_FIXTURES.md) specifies deterministic fixture construction.

**Timeline evidence grade:** the Rust timeline target and its Rust tests are landed. The environment that authored them did not contain `cargo` or `rustc`, and hosted Actions were intentionally not used, so this file does not claim the new target compiled or its Rust tests ran in that same session. The independent Python 3.13 fixture-builder regression is **observed** at 4 of 4 passing.

#### Still incomplete

- Parser errors have real UTF-16 positions. Most bounded-source type failures are kernel rejections rather than `NatDefinitionElabError` values, and neither path carries an offending *token* position — but they now carry a **command-level** position: `EngineExecutionError::BatchCommand` gained an `at` offset that the source command loops populate, so a kernel or elaboration failure lands on the failing command's line rather than the file head (`8eb6e859`, tested by `kernel_rejection_reports_the_command_line_not_the_file_head`). Token-level (offending sub-expression) positions remain a larger follow-on.
- Method-response schema v1 is an outer contract. It does not validate the complete initialize capability object or useful semantic payloads for goals, hover, completion, or definition. Successful diagnostic waits are object-valued rather than bound to a deeper inner schema.
- Independent `CLIENT` and `SERVER` recordings still have no shared order. The new `TIMELINE` profile supplies recorder-defined event order, not wall-clock time, duration, scheduler execution, transport flush completion, or active CPU-work intervals.
- No production recorder yet emits and identity-binds the interleaved event format. Fixture or caller-generated timelines must not be promoted to live-daemon evidence by implication.
- Timeline schema v1 does not yet bind a particular `didOpen`, `didChange`, or `didSave` to its progress, terminal publication, diagnostic clearing, and completion episode. Complete document-to-progress-to-publication causality remains open.
- Plain goals and term goals are not cursor-aware. Hover, completion, and definition still return no-information responses.
- Lean RPC sessions are not implemented. RPC calls fail visibly; keepAlive and release do not fabricate a session.
- Retained source is session-local input state, not a declaration-granular shared elaboration and import environment.
- The server remains synchronous and does not implement asupersync regions, active elaboration cancellation, shared immutable import heaps, stable diagnostic identities, crash isolation, or full unmodified `vscode-lean4` parity.

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

These subsystems contain real contract planes, data structures, bounded execution slices, or integration work, but the repository has not reached the README's finished-system claims. Full mathlib-compatible elaboration and tactics, the complete native `Lean.*` Mirror, full Lake and Ledger behavior, production Iron code generation and JIT, semantic LSP and RPC, complete MCP orchestration, and release-grade cross-platform distribution remain active program work.

---

## High-priority open proof obligations

1. **Advance `fln-51y8` with real pinned evidence.** Execute the pinned Nat council and continue the exact Prelude first-failure frontier rather than generalizing from fixtures.
2. **Give command failures token-level source positions (command-level is done).** Parse errors have token-precise positions, and command-level provenance now landed (`8eb6e859`): `EngineExecutionError::BatchCommand` carries an `at` offset the source command loops populate, and `primary_source_offset` falls back to it, so every kernel/elaboration/command failure lands on the correct line. The remaining follow-on is **token-level** precision — the offending sub-expression rather than the command — which needs real source provenance threaded through the elaborator (`NatDefinitionElabError`, 65 sites) and the kernel verdict. A secondary, smaller item: the check-terminal query path and the generic batch helper still pass `at: None` (no per-command offset in scope there), so `fln run`/terminal query failures keep the file-head fallback until those are filled with per-site offset care.
3. **Compile and run the interleaved timeline target at the pinned Rust toolchain.** Exercise its unit and installed-binary tests, clippy with warnings denied, formatting, and workspace check before promoting the new Rust profile beyond landed evidence. Retain the already observed Python fixture-builder regression as a separate claim.
4. **Bind document-check episodes in timeline schema v2.** Join each accepted open, change, save, and close to the exact progress, publication or outcome, clear, and completion sequence, while refusing overlapping or orphaned synchronous episodes.
5. **Add a production timeline recorder with identity.** Bind executable, Git tree, epoch, producer semantics, final daemon state, first divergence, and the exact outer stream; do not synthesize order from independent recordings.
6. **Keep independent-checker authority boundaries intact.** The checker may veto or observe; it must never become a second admission authority.
7. **Deepen method-result contracts deliberately.** Bind the exact initialize capability object and exact diagnostic-wait success payload before claiming those inner semantics.
8. **Replace no-information editor scaffolding with truthful semantics one method at a time.** Never fabricate goals, hover data, completions, definitions, or RPC sessions merely to suppress client errors.
9. **Promote retained text into real declaration and import state deliberately.** The latest-text cache supports truthful Full-sync lifecycle semantics; it is not dependency-aware incremental elaboration.
10. **Keep JSON-RPC decoding narrow but structural.** Extend typed extraction deliberately; never reintroduce substring routing or unbounded generic decoding.
11. **Prefer executable frontier evidence over narrative status.** New compatibility claims should name a reproducer, pin or artifact identity, and outcome class.

---

## Focused local verification commands

On a host with the pinned Rust and Reference toolchains:

```bash
cargo fmt --all -- --check
cargo test --locked -p fln-server --all-targets --no-fail-fast
cargo clippy --locked -p fln-server --all-targets -- -D warnings
cargo test --locked -p fln-cli --all-targets --no-fail-fast
cargo clippy --locked -p fln-cli --all-targets -- -D warnings
cargo check --locked --workspace --all-targets
python3 scripts/test_build_lsp_timeline.py
cargo test --locked -p fln-checker --no-fail-fast
cargo test --locked -p fln-conformance --test pinned_nat_council
python3 scripts/check_pinned_nat_council.py
```

The ordinary `pinned_nat_council` target leaves the real-artifact cell ignored; the Python runner is the explicit non-vacuous invocation. Project-wide release claims require the broader governed evidence procedures, not only these focused commands.
