# Changelog

This is the synthesized, agent-facing changelog for **franken_lean**. It records what has actually landed; the [`README.md`](README.md) intentionally describes the finished 1.0 target state, and [`IMPLEMENTATION_STATUS.md`](IMPLEMENTATION_STATUS.md) is the current evidence-graded status companion.

Scope: project inception on **2026-07-21** through the September 2 Lantern resource/evidence tranche at **[`af668aa6`](https://github.com/Dicklesworthstone/franken_lean/commit/af668aa65e2cf04ddbbf4903401bd6514ab88dc3)**. This changelog refresh follows that implementation snapshot.

No GitHub Releases were published when this file was refreshed on **2026-09-02**. Do not infer or invent a `v0.x` release from commit activity.

Primary sources:

- git history on `main` through the snapshot above;
- the Beads tracker in [`.beads/issues.jsonl`](.beads/issues.jsonl);
- the governing plan and generated contracts;
- repository-owned tests, evidence receipts, and current-state documentation.

Representative commits are examples, not substitutes for the tracker/evidence graph.

---

## Version timeline

| Milestone | Date | Summary |
|---|---|---|
| [`45e3bd2a`](https://github.com/Dicklesworthstone/franken_lean/commit/45e3bd2a79a0ea9cbcbb81ecaaa6ec296ca86e79) | 2026-07-21 | Project, comprehensive plan, README, AGENTS, license, and initial Beads graph. |
| [`3df0543d`](https://github.com/Dicklesworthstone/franken_lean/commit/3df0543d9537b0a930e7e72ba9b779bfa0e49ad5) | 2026-07-22 | §21 Rust workspace, pinned nightly, structural dependency gate. |
| [`9a8860ab`](https://github.com/Dicklesworthstone/franken_lean/commit/9a8860aba1bf88cf68d4c01785126e8dca6d9435) | 2026-08-19 | Bounded native `lean` personality, checker/olean reconstruction, Golem source execution. |
| [`ea891c23`](https://github.com/Dicklesworthstone/franken_lean/commit/ea891c23fb4c44ac4d5020715d9c0121fdc90c32) | 2026-09-01 | Evidence-graded checker frontier, executable agent-control tools, structurally hardened stateful Lantern document synchronization. |
| [`ab417cc9`](https://github.com/Dicklesworthstone/franken_lean/commit/ab417cc985dec40518d3e4318626c3a9bf4f0387) | 2026-09-02 | Modular Lantern dispatcher, structural callback authority, bounded versioned diagnostic waits, and public framed protocol transcripts. |
| [`af668aa6`](https://github.com/Dicklesworthstone/franken_lean/commit/af668aa65e2cf04ddbbf4903401bd6514ab88dc3) | 2026-09-02 | Exact zero-diagnostic authority accounting, full-wire transcript receipts, and bounded open-document URI metadata. |

---

## 1) Inception, crate map, and G0 constitution — 2026-07-21 → 2026-07-22

The repository began as a system design and immediately converted the design into enforceable structure.

### Landed

- Comprehensive design plan, agent conventions, and project license.
- Beads dependency graph projecting the execution plan.
- Rust workspace with the plan §21 crate map, pinned nightly, and structural dependency checks.
- Authoritative `SUITE.lock` and dependency-closure audit.
- Fail-closed evidence harness and the pinned Lean Reference retained strictly as Tribunal/oracle material.

### Representative commits

- [`45e3bd2a`](https://github.com/Dicklesworthstone/franken_lean/commit/45e3bd2a79a0ea9cbcbb81ecaaa6ec296ca86e79) — initial system design and repository.
- [`3df0543d`](https://github.com/Dicklesworthstone/franken_lean/commit/3df0543d9537b0a930e7e72ba9b779bfa0e49ad5) — §21 workspace scaffold.
- [`6c1f089c`](https://github.com/Dicklesworthstone/franken_lean/commit/6c1f089c) — `SUITE.lock` closure audit.
- [`0803079f`](https://github.com/Dicklesworthstone/franken_lean/commit/0803079f) — evidence harness.

---

## 2) Crucible kernel, generated contracts, and Tribunal bootstrap — 2026-07-22 → 2026-07-25

### Landed

- `fln-core` term plane: names, universes, expressions, options, and positions.
- `KERNEL_CONTRACT.md` as an executable/CI-checked judgment specification.
- Crucible K1 bootstrap and soundness cells around proof irrelevance and admission authority.
- Generated ABI and `.olean` contracts rather than hand-transcribed layouts.
- Tribunal/parity-ledger bootstrap.
- Owned bignum ground and kernel literal acceleration.
- Early kernel mutation campaign around recursors, conversion, quotient initialization, and binder handling.

### Representative commits

- [`7ed677c2`](https://github.com/Dicklesworthstone/franken_lean/commit/7ed677c294339e4ce15bca65d90a653493a035a8) — core Lean term-plane types.
- [`8ece0b70`](https://github.com/Dicklesworthstone/franken_lean/commit/8ece0b7086d8dbdadd4a9fe7dc3e5ec35c0e5727) — Crucible bootstrap.
- [`0f21aede`](https://github.com/Dicklesworthstone/franken_lean/commit/0f21aede1109f76719d579994858498721a90591) — generated ABI/olean contracts.
- [`06ba84b2`](https://github.com/Dicklesworthstone/franken_lean/commit/06ba84b2) — Tribunal bootstrap.

---

## 3) Marrow ABI twin, `.olean` codec, and Grimoire environment — 2026-07-22 → 2026-07-26

### Landed

- Marrow `lean_object` compatibility heap, tri-state RC, membrane, and ownership shadows.
- Compacted-region mmap/relocation substrate used by the `.olean` reader.
- Grimoire persistent environment with structural identities, snapshots, and bounded admission surfaces.
- Stack-safe term/level drops and canonical traversal/encoding paths.

### Representative commits

- [`5d6cb2b2`](https://github.com/Dicklesworthstone/franken_lean/commit/5d6cb2b2) — Marrow object/RC core.
- [`1eca4667`](https://github.com/Dicklesworthstone/franken_lean/commit/1eca4667804e0ad717d2c1703040d6f22d1bb083) — compacted-region loading.
- [`94348b02`](https://github.com/Dicklesworthstone/franken_lean/commit/94348b02) — shared region engine beneath `.olean` loading.
- [`156f9ee7`](https://github.com/Dicklesworthstone/franken_lean/commit/156f9ee792812295e44dd0d53540b2a17e0c1ea2) — Grimoire environment.

---

## 4) Vellum syntax/parser substrate and Verdict SAT — 2026-07-24 → 2026-07-25

### Landed

- Vellum naming contract and SourceInfo with byte/scalar/UTF-16 projections.
- Lossless green-tree/source preservation laws.
- Solver-independent Verdict CNF/proof contract, owned checker, and certificate goldens.
- Kernel-checked reflected `bv_decide` publication over the opaque kernel capability.
- Nested-inductive auxiliary translation work.

### Representative commits

- [`e20cded9`](https://github.com/Dicklesworthstone/franken_lean/commit/e20cded9428b85005d67dd5d13978706818a452b) — SourceInfo and lossless syntax ground.
- [`b823faf1`](https://github.com/Dicklesworthstone/franken_lean/commit/b823faf160cf7987ea1ff8e7fa6dae3e01ee5944) — Verdict contract plane.
- [`26eaaafb`](https://github.com/Dicklesworthstone/franken_lean/commit/26eaaafb) — kernel-checked `bv_decide` integration.

---

## 5) Evidence-join and safety hardening — 2026-07-25 → 2026-08-02

This wave made claims harder to overstate rather than merely increasing test counts.

### Landed

- Mandated-mutant rows joined to their named killer tests and retention/cadence evidence.
- Kernel LOC covenant disclosure tied to the enforcing walk.
- D3 SAFETY-note enforcement and named unsafe-boundary governance.
- Evidence rows moved from file-level ambiguity toward exact producer/test identities.
- Resource/cancellation/inconclusive outcomes prevented from collapsing into ordinary rejection.
- Public-surface census and drift machinery across CLI/Lake/LSP-facing contracts.

### Representative commits

- [`cd195a90`](https://github.com/Dicklesworthstone/franken_lean/commit/cd195a90) — mandated-mutant evidence joins.
- [`2f9112f7`](https://github.com/Dicklesworthstone/franken_lean/commit/2f9112f7) — kernel LOC disclosure.
- [`5a4cfd35`](https://github.com/Dicklesworthstone/franken_lean/commit/5a4cfd35) — D3 SAFETY notes/enforcement.

---

## 6) Elaborator seed and Golem VM — 2026-07-31 → 2026-08-01

### Landed

- First source-text → kernel-accepted declaration seam.
- Pin-generated façade stubs over the bounded elaborator surface.
- FIR/FLBC and Golem interpreter substrate.
- Governed ABI value state, inline caches, heartbeat/checkSystem semantics, and early IO/task slices.
- G0-3 parity comparator defining the intended execution verdict.

### Representative commits

- [`7c48295c`](https://github.com/Dicklesworthstone/franken_lean/commit/7c48295c0c58bf78862032ecf7445cdae80be26b) — first source-to-kernel elaboration seam.
- [`be81a269`](https://github.com/Dicklesworthstone/franken_lean/commit/be81a269aa672171df4b3f14472934a1cd783953) — retained FIR/FLBC prototype.
- [`286d1f04`](https://github.com/Dicklesworthstone/franken_lean/commit/286d1f04) — Golem parity comparator.

---

## 7) Independent checker, owned libm, and ABI effects — 2026-08-03 → 2026-08-09

### Landed

- Independent checker admission ground for axioms, definitions/theorems/opaques, mutual blocks, quarantines, inference, defeq, and related KR slices.
- Owned deterministic libm baseline and full-range numerical work.
- Additional Marrow IO/task ABI rows and observable runtime behavior.
- Stronger separation between checker observation/veto and the one kernel admission authority.

### Representative commits

- [`ea3bbbf6`](https://github.com/Dicklesworthstone/franken_lean/commit/ea3bbbf6) — declaration-admission verdict surface.
- [`654edb49`](https://github.com/Dicklesworthstone/franken_lean/commit/654edb49c474f2af123e3a744c569f6d050fb8ed) — owned libm baseline.
- [`dcb65dcf`](https://github.com/Dicklesworthstone/franken_lean/commit/dcb65dcf) — additional IO exports.

---

## 8) Native CLI, source execution, and `.olean` reconstruction — 2026-08-10 → 2026-08-19

### Landed

- `fln run`, `fln flbc run`, `fln check-olean`, bounded olean inspection/diff, and related artifact surfaces.
- Golem execution for a growing closed Nat/Bool/String subset.
- Source-module import/definition partitioning and bounded module-graph execution.
- Independent checker reconstruction of enumeration units, field-bearing inductives, quotient authority units, and related declaration blocks.
- Standalone checkable olean snapshots.
- Iterative stack-safe substitution/WHNF/defeq/runtime-projection paths.
- Bounded native `lean` personality including imports and `#check`.

### Representative commits

- [`0833f781`](https://github.com/Dicklesworthstone/franken_lean/commit/0833f781) — bounded `fln run`.
- [`32820239`](https://github.com/Dicklesworthstone/franken_lean/commit/328202398fc669d7db5d4eb5730aa692129838d0) — `fln check-olean`.
- [`1af9d5b1`](https://github.com/Dicklesworthstone/franken_lean/commit/1af9d5b1) — checked `String.append` through Golem.
- [`f4960d71`](https://github.com/Dicklesworthstone/franken_lean/commit/f4960d713858b770c25f40c60fff41e83a219b83) — quotient initializer admission.
- [`aa0849b0`](https://github.com/Dicklesworthstone/franken_lean/commit/aa0849b01a4dc19f7b9096c45fa6173093d26d9d) — standalone olean snapshots.

---

## 9) Repository hygiene — 2026-08-19

A small janitor wave cleaned repository scratch state. Historical commit subjects should not be treated as stronger evidence than their actual diffs; authoritative planning/contracts remained at their governed paths.

- [`9a8860ab`](https://github.com/Dicklesworthstone/franken_lean/commit/9a8860aba1bf88cf68d4c01785126e8dca6d9435) — janitor cleanup.

---

## 10) Trust surfaces on the native CLI — 2026-08-23

### Landed

- `fln why-trusts` bounded trust closure over decoded artifacts.
- `fln audit --tcb` inventory views.
- compile-time suite identity reporting.
- hash-chained `check-olean --receipts` run receipts.
- durable-publication parent-path repair shared by emitted artifact paths.

These receipts attest runs; they are not proof certificates.

### Representative commit

- `ef78cef4` — trust surfaces: `why-trusts`, TCB audit, identity, and check receipts.

---

## 11) Checker frontier, executable agent control, and Lantern hardening — 2026-08-29 → 2026-09-01

This wave focused on three connected problems: make pinned-artifact checker progress falsifiable, make multi-agent repository state legible, and make the bounded LSP server truthful rather than cosmetically compatible.

### Independent checker / pinned Prelude

- Corrected the `Init.HEq` recursor reconstruction so the reflexive premise applies the motive to the type, the outer hygienic value, and `HEq.refl`, while preserving the distinct rebound heterogeneous value.
- Corrected the synthetic direct-recursive `Init.Nat` successor-minor de Bruijn indices and strengthened forged-recursion refusal cells.
- Added a real-artifact Nat council regression that decodes `Nat`, `Nat.zero`, `Nat.succ`, and `Nat.rec` from the pinned `Init.Prelude.olean` companion chain and submits that exact block through the ordinary K1 + independent-checker facade.
- Made that real-artifact cell explicit/ignored and non-vacuous: an explicit run cannot pass merely because the Reference pin is absent.
- Added a repository-local pinned Nat runner derived from `SUITE.lock`.

**Evidence boundary:** the repository owns the real-artifact reproducer, but this changelog does not promote `fln-51y8` to full Prelude completion. The complete sequential council frontier remains a separate obligation.

Representative commits: [`2ad0eb21`](https://github.com/Dicklesworthstone/franken_lean/commit/2ad0eb21cc16b132407de07158ff39e81c69db2b), [`72502cc3`](https://github.com/Dicklesworthstone/franken_lean/commit/72502cc31f6e9f67c350033e663eef5ef0de63d3), [`f72025e3`](https://github.com/Dicklesworthstone/franken_lean/commit/f72025e381d9d103a6c5845c8b6b1ef9ba51fb0b), [`5ae1b2b4`](https://github.com/Dicklesworthstone/franken_lean/commit/5ae1b2b41153b226fe1a141b82a088c828053127).

### Agent-control plane

- Added [`AGENT_FRONTIER_PROTOCOL.md`](AGENT_FRONTIER_PROTOCOL.md): immutable Git/artifact anchors, semantic ownership, typed first-failure frontiers, negative evidence, one-variable experiments, and evidence envelopes.
- Added read-only frontier capsule auditing and deterministic Git-anchor recording.
- Added deterministic Beads frontier selection using priority, transitive/direct unlocks, context reuse, isolation, evidence cost, collision risk, trusted-surface breadth, and irreducible uncertainty.
- Selector strict mode distinguishes an observational ranking from promotion-authoritative selection when artifact/toolchain/oracle facts are unknown.
- Blocking dependency cycles are graph corruption, not an empty ready set; cycle refusal returns a deterministic concrete witness.

Representative commits: [`fcbe18f2`](https://github.com/Dicklesworthstone/franken_lean/commit/fcbe18f257c957084e6372b631541aff0e845d93), [`7d66a05e`](https://github.com/Dicklesworthstone/franken_lean/commit/7d66a05e2a02a0e6457eafeeabbe6ffb3352fb11), [`69c07154`](https://github.com/Dicklesworthstone/franken_lean/commit/69c07154acc175fbb58f16e8e2db7d345327418f), [`3d7c8300`](https://github.com/Dicklesworthstone/franken_lean/commit/3d7c83002edb71934834cbcd11a079709b4ca2ef).

### Lantern / LSP bounded server

- Replaced permissive JSON string handling with fail-closed escape decoding, UTF-16 surrogate-pair reconstruction, malformed-escape/raw-control refusal, and decoded URI/method/source handling.
- Preserved integer and string JSON-RPC request IDs and gave malformed request IDs a distinct `-32600`/`id:null` outcome instead of silently turning them into notifications.
- Bound JSON-RPC envelope routing to the root object so nested `params.method`/`params.id` cannot hijack routing.
- Replaced fabricated Lean RPC session IDs/null-call success with explicit LSP `RequestFailed` (`-32803`) while the RPC subsystem is absent.
- Replaced broad document-field substring search with exact structural reads from `params.textDocument`, `params.text`, and the one-element Full-sync `params.contentChanges` array.
- Added a bounded session-local latest-source cache (1,024 documents / 256 MiB retained source) so textless saves can re-check the latest valid full document without claiming an unbounded persistent elaboration heap.
- Bound retained source to monotone client document versions. Duplicate/regressing changes cannot overwrite or re-diagnose older source on top of a newer snapshot.
- Malformed/incomplete open/change/save transitions invalidate retained source rather than allowing later textless saves to replay stale content.
- `didClose` evicts retained source and clears push diagnostics for the URI.

**Still not claimed:** cursor-aware proof goals, semantic hover/completion/definition, Lean RPC sessions, declaration-granular import/elaboration state, or the finished shared-heap parallel Lantern architecture.

Representative commits: [`fced6257`](https://github.com/Dicklesworthstone/franken_lean/commit/fced62579ac344aaf008c7fb38f39b2485df463e), [`81d33852`](https://github.com/Dicklesworthstone/franken_lean/commit/81d338529b12dd05a91ae675cb87f94cb2abb4c8), [`9e50fdef`](https://github.com/Dicklesworthstone/franken_lean/commit/9e50fdef012caf7bd2a1f95dda575a353e51631c), [`637176fd`](https://github.com/Dicklesworthstone/franken_lean/commit/637176fd357ce610354aa14695f4841b68e72f68), [`2114cd59`](https://github.com/Dicklesworthstone/franken_lean/commit/2114cd59f7f5385782a4b56667fa60b09f4c30b1), [`60ebc07a`](https://github.com/Dicklesworthstone/franken_lean/commit/60ebc07a8c13286a6e3df293e6db99fe4e0eb073), [`f2af73ff`](https://github.com/Dicklesworthstone/franken_lean/commit/f2af73ff7faf69e10bde112ed4b1b391d57fd55b).

---

## 12) Lantern modularization and diagnostic authority — 2026-09-02

This continuation replaced overlapping protocol implementations with one typed control path, then separated accepted document state from the authority to claim that diagnostics for that state were actually emitted.

### Structural protocol and session architecture

- Split strict JSON parsing, deterministic wire construction, document-session state, and pending diagnostic waits into dedicated modules and made them authoritative from the live dispatcher.
- Validated complete JSON before dispatch, preserving syntactically valid JSON number lexemes, decoded strings, and `null` request IDs without narrowing.
- Hardened Content-Type parsing to accept the specified UTF-8 token and quoted forms while rejecting malformed quotes, escapes, duplicate parameters, unsupported charset values, and non-token inputs.
- Made retained-source accounting recovery conservative: affected text is invalidated, unaffected text survives when an exact in-budget total can be rebuilt, and impossible reconstruction discards all cached text while preserving open/version authority.
- Added deterministic unit round-trips for every emitted JSON-RPC wire shape through the same strict parser used for inbound traffic.

### Diagnostic publication authority

- Stopped treating arbitrary callback bytes or method-looking substrings as terminal diagnostics.
- Callback messages must be valid JSON-RPC 2.0 notifications. `publishDiagnostics` counts for the current check only when `params.uri` exactly matches the checked document; wrong-URI publications remain auxiliary.
- Missing, malformed, response-shaped, or duplicate terminal output is withheld as authority, followed by explicit diagnostic clearing and a schema-bound non-authoritative fault.
- Canonical `$/lean/diagnosticOutcome` authority grades the publication frontier: `authority:true` completes it, while `authority:false` preserves the detailed outcome, clears editor diagnostics, and fails dependent waits.
- The expected empty-diagnostic publication plus one canonical outcome is treated as one coherent terminal result rather than as duplicate success.

### Bounded diagnostic waiting

- Implemented `textDocument/waitForDiagnostics` for the pinned Lean `{ uri, version }` shape and `{}` success result.
- Separated the accepted document/version frontier from the terminal diagnostic-publication frontier. A source change alone cannot satisfy a wait.
- Future-version waits complete in registration order only after an authoritative terminal publication for at least the target version.
- Non-authoritative processing, source invalidation, accounting failure, document close, or server shutdown resolves affected waits with typed failure rather than leaving them hanging or claiming success.
- Added bounded pending-wait storage: at most 4,096 waits and 4 MiB of retained request-ID/URI metadata, with duplicate outstanding-ID refusal.
- Added exact `$/cancelRequest` handling for pending diagnostic waits and visible no-session handling for Lean RPC keepAlive/release notifications.

### Public evidence cells

- Added exported framed-stdio transcripts for lifecycle order, Full-sync open/change/save/close, malformed JSON and invalid UTF-8 recovery, structural callback spoof rejection, malformed callback withholding, authoritative and non-authoritative wait outcomes, same-version recovery, future-version completion/failure, cancellation, close, shutdown, and unsupported RPC.

**Evidence boundary:** these changes are landed with repository-owned unit and public transcript tests. The editing environment did not contain `cargo`/`rustc`, so this changelog does not claim those tests were executed in the same session. The live CLI callback still uses the compatibility source-blind projector; source-aware unsaved-text projection remains explicitly open.

Representative commits: [`57a268bc`](https://github.com/Dicklesworthstone/franken_lean/commit/57a268bcd1a5656b3bf4d983a7630eb709bc819f), [`be2ffcf9`](https://github.com/Dicklesworthstone/franken_lean/commit/be2ffcf91ed60eb7a8fbd3605e101fdbe5d2ba54), [`32713f48`](https://github.com/Dicklesworthstone/franken_lean/commit/32713f480a77e94d8331ba064841bf72ca20377a), [`6ba4ef42`](https://github.com/Dicklesworthstone/franken_lean/commit/6ba4ef42310c9f3d12be0b5d2460c96716dd991c), [`ab417cc9`](https://github.com/Dicklesworthstone/franken_lean/commit/ab417cc985dec40518d3e4318626c3a9bf4f0387).

---

## 13) Diagnostic accounting, transcript receipts, and URI resource bounds — 2026-09-02

This tranche tightened three places where the implementation enforced a policy but did not yet expose or fully bind the corresponding authority fact.

### Exact diagnostic accounting

- A canonical zero-diagnostic completion now requires the current projection schema, `outcome:"complete"`, `authority:true`, and exact unsigned `diagnosticCount:0` as one structural tuple.
- Missing, nonzero, negative, fractional, string, overflowing, or duplicate decoded counts are withheld rather than releasing `waitForDiagnostics` as a false clean result.
- `inconclusive` and `internal_fault` outcomes must remain `authority:false` and may not carry the complete-only count field.
- Exported framed-stdio tests prove malformed accounting clears editor diagnostics, emits a non-authoritative callback fault, and resolves the wait with `RequestFailed`.

### Reproducible transcript resource evidence

- The shared transcript reader already bounded complete Content-Length wire bytes, including extension headers and framing, while separately counting JSON body bytes.
- `TranscriptStats` now publishes both facts, and the validation receipt advances to `fln.lsp-transcript-validation/2` with `wireBytes` and `bodyBytes`.
- Library, validator-binary, empty-stdin, and extension-header tests bind the receipt to the exact complete framed byte length rather than an inferred body-only approximation.

### Open-document metadata budget

- Added a separate 4 MiB aggregate budget for retained open-document URI keys alongside the existing 1,024-document and 256 MiB source limits.
- URI capacity is checked before source retention changes, so a rejected giant URI cannot consume source bytes, lifecycle slots, or checker work.
- Close and invariant recovery rebuild/release source and URI accounting independently while preserving open/version authority.
- A public framed-stdio test sends an over-budget URI and then a normal document in the same session, proving the refusal is isolated and the ordinary document still reaches diagnostics.

**Evidence boundary:** the code and tests are landed, but this session had no Rust toolchain and GitHub Actions were unavailable. This changelog therefore records implementation and executable test ownership, not same-session execution evidence. `franken_lean-v2p` remains open because cursor semantics, source-aware live projection, Lean RPC, shared import state, asynchronous cancellation, and full editor parity are not complete.

Representative commits: [`9a8f2362`](https://github.com/Dicklesworthstone/franken_lean/commit/9a8f2362992d781da04419471475f3a02851d71c), [`9f11cc26`](https://github.com/Dicklesworthstone/franken_lean/commit/9f11cc26ddbf82c911bee326cd2e9f54de50f91c), [`5583c65f`](https://github.com/Dicklesworthstone/franken_lean/commit/5583c65febe88583d6ae2dcb544a39c960342d57), [`b8256034`](https://github.com/Dicklesworthstone/franken_lean/commit/b82560341b9096f36df280a570a2608e6972d645), [`a4807ece`](https://github.com/Dicklesworthstone/franken_lean/commit/a4807ece6042d676d4d43f62f569c34a841062ae), [`af668aa6`](https://github.com/Dicklesworthstone/franken_lean/commit/af668aa65e2cf04ddbbf4903401bd6514ab88dc3).

---

## Notes for agents

- The README is the 1.0 target-state specification; use [`IMPLEMENTATION_STATUS.md`](IMPLEMENTATION_STATUS.md) for present implementation/evidence claims.
- The tracker of record is [`.beads/issues.jsonl`](.beads/issues.jsonl); Beads IDs are not GitHub Issues.
- The Oracle-Only Law remains absolute: the pinned Lean Reference is differential evidence/fixture input, never a FrankenLean runtime component.
- Generated contracts such as `KERNEL_CONTRACT.md`, `ABI_CONTRACT.md`, and `OLEAN_CONTRACT.md` are compatibility authorities; do not hand-copy their facts into implementation code.
- A green synthetic fixture is not a pinned-artifact claim. Long sequential compatibility work reports `last proven -> first non-success -> typed class`.
- Full semantic Lantern/LSP/RPC, mathlib-scale end-to-end closure, and release-grade distribution remain active program work even though substantial bounded slices are live.
