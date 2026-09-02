# Changelog

This is the synthesized, agent-facing changelog for **franken_lean**. It records what has actually landed. [`README.md`](README.md) is intentionally written as the finished 1.0 target, while [`IMPLEMENTATION_STATUS.md`](IMPLEMENTATION_STATUS.md) is the current evidence-graded state ledger.

Scope: project inception on **2026-07-21** through the September 2 method-bound Lantern response tranche rooted at substantive commit [`0dae67c9`](https://github.com/Dicklesworthstone/franken_lean/commit/0dae67c9c800852dbd6af7527e97a9b493a2eac4).

No GitHub Release is implied by this history. Representative commits are navigation aids, not substitutes for the Beads graph, generated contracts, real-artifact receipts, or governed release evidence.

---

## Timeline

| Milestone | Date | Summary |
|---|---|---|
| [`45e3bd2a`](https://github.com/Dicklesworthstone/franken_lean/commit/45e3bd2a79a0ea9cbcbb81ecaaa6ec296ca86e79) | 2026-07-21 | Project, comprehensive plan, README, AGENTS, license, and initial Beads graph. |
| [`3df0543d`](https://github.com/Dicklesworthstone/franken_lean/commit/3df0543d9537b0a930e7e72ba9b779bfa0e49ad5) | 2026-07-22 | Plan §21 Rust workspace, pinned nightly, and structural dependency gate. |
| [`9a8860ab`](https://github.com/Dicklesworthstone/franken_lean/commit/9a8860aba1bf88cf68d4c01785126e8dca6d9435) | 2026-08-19 | Bounded native `lean` personality, checker/olean reconstruction, and Golem source execution. |
| [`ea891c23`](https://github.com/Dicklesworthstone/franken_lean/commit/ea891c23fb4c44ac4d5020715d9c0121fdc90c32) | 2026-09-01 | Evidence-graded checker frontier, executable agent-control plane, and stateful Full-sync Lantern groundwork. |
| [`ab417cc9`](https://github.com/Dicklesworthstone/franken_lean/commit/ab417cc985dec40518d3e4318626c3a9bf4f0387) | 2026-09-02 | Modular Lantern dispatcher, diagnostic publication authority, bounded waits, and public framed transcripts. |
| [`c150fa9e`](https://github.com/Dicklesworthstone/franken_lean/commit/c150fa9e9c690f13303161bd3ab96b718ba125ef) | 2026-09-02 | Strict client lifecycle, method role/params contracts, replay preflight, and metadata-only inspection. |
| [`3cef4983`](https://github.com/Dicklesworthstone/franken_lean/commit/3cef498352964fd6512c79f5d303e3d92fc045a1) | 2026-09-02 | Document-semantic client sessions, structural server transcripts, and initial bidirectional ID correlation. |
| [`88d9970f`](https://github.com/Dicklesworthstone/franken_lean/commit/88d9970f9c8491f2a454516da8e01071a2f0db64) | 2026-09-02 | Cancellation-bound request identity, wait/cancellation evidence, response classification, and bounded ID retention. |
| [`0dae67c9`](https://github.com/Dicklesworthstone/franken_lean/commit/0dae67c9c800852dbd6af7527e97a9b493a2eac4) | 2026-09-02 | Method-bound response validation and exhaustive reconciliation with server result/error totals. |

---

## 1. Foundation and constitution — 2026-07-21 → 2026-07-22

Landed:

- the comprehensive architecture and execution plan;
- repository-wide agent instructions and a Beads dependency graph;
- the plan §21 native-Rust crate map and pinned nightly;
- the closed dependency universe and structural dependency checks;
- `SUITE.lock` as the compatibility epoch and closure authority;
- fail-closed evidence harnesses and the Oracle-Only Law: the pinned Lean Reference is fixture and oracle material, never a FrankenLean runtime component.

Representative commits: [`45e3bd2a`](https://github.com/Dicklesworthstone/franken_lean/commit/45e3bd2a79a0ea9cbcbb81ecaaa6ec296ca86e79), [`3df0543d`](https://github.com/Dicklesworthstone/franken_lean/commit/3df0543d9537b0a930e7e72ba9b779bfa0e49ad5), `6c1f089c`, `0803079f`.

## 2. Core terms, Crucible, generated contracts, and Tribunal — 2026-07-22 → 2026-07-25

Landed:

- names, universes, expressions, options, positions, and bounded outcome types in `fln-core`;
- `KERNEL_CONTRACT.md` as an executable judgment specification;
- Crucible K1 bootstrap and admission authority boundaries;
- mechanically generated ABI and `.olean` contracts;
- Tribunal and parity-ledger bootstrap;
- owned bignum ground and kernel literal acceleration;
- early mutation campaigns around conversion, recursors, quotients, proof irrelevance, and binders.

Representative commits: [`7ed677c2`](https://github.com/Dicklesworthstone/franken_lean/commit/7ed677c294339e4ce15bca65d90a653493a035a8), [`8ece0b70`](https://github.com/Dicklesworthstone/franken_lean/commit/8ece0b7086d8dbdadd4a9fe7dc3e5ec35c0e5727), [`0f21aede`](https://github.com/Dicklesworthstone/franken_lean/commit/0f21aede1109f76719d579994858498721a90591), `06ba84b2`.

## 3. Marrow ABI twin, `.olean` plane, and Grimoire — 2026-07-22 → 2026-07-26

Landed:

- `lean_object` compatibility heap, tri-state RC, membrane, and ownership shadows;
- compacted-region mmap and relocation substrate used by artifact loading;
- persistent environment snapshots and bounded declaration admission;
- stack-safe term/level destruction and deterministic traversal/encoding;
- split `.olean` companion decoding and the beginnings of byte-compatible reconstruction.

Representative commits: `5d6cb2b2`, [`1eca4667`](https://github.com/Dicklesworthstone/franken_lean/commit/1eca4667804e0ad717d2c1703040d6f22d1bb083), `94348b02`, [`156f9ee7`](https://github.com/Dicklesworthstone/franken_lean/commit/156f9ee792812295e44dd0d53540b2a17e0c1ea2).

## 4. Vellum, Verdict, and evidence hardening — 2026-07-24 → 2026-08-02

Landed:

- lossless syntax and source substrate with byte, scalar, and UTF-16 projections;
- solver-independent CNF and proof contracts, owned SAT checking, and reflected `bv_decide` publication;
- exact mutant-to-killer-test evidence joins;
- kernel LOC covenant and named unsafe-boundary enforcement;
- resource, cancellation, and inconclusive outcomes that cannot collapse into ordinary rejection;
- public-surface census and drift machinery.

Representative commits: [`e20cded9`](https://github.com/Dicklesworthstone/franken_lean/commit/e20cded9428b85005d67dd5d13978706818a452b), [`b823faf1`](https://github.com/Dicklesworthstone/franken_lean/commit/b823faf160cf7987ea1ff8e7fa6dae3e01ee5944), `26eaaafb`, `cd195a90`, `2f9112f7`, `5a4cfd35`.

## 5. Elaborator seed, Golem, independent checker, and owned numerics — 2026-07-31 → 2026-08-09

Landed:

- the first source-text to kernel-accepted declaration seam;
- pin-generated facade stubs over the bounded elaborator surface;
- FIR/FLBC and the Golem interpreter substrate;
- governed ABI values, inline caches, heartbeat and check-system behavior, and bounded IO/task slices;
- independent checker admission for axioms, definitions, theorems, opaques, mutual blocks, inference, defeq, and selected inductive/recursor forms;
- owned deterministic libm baseline and additional ABI effects.

Representative commits: [`7c48295c`](https://github.com/Dicklesworthstone/franken_lean/commit/7c48295c0c58bf78862032ecf7445cdae80be26b), `be81a269`, `286d1f04`, `ea3bbbf6`, [`654edb49`](https://github.com/Dicklesworthstone/franken_lean/commit/654edb49c474f2af123e3a744c569f6d050fb8ed).

## 6. Native CLI, source execution, artifact reconstruction, and trust surfaces — 2026-08-10 → 2026-08-23

Landed:

- `fln run`, `fln flbc run`, `fln check-olean`, bounded inspect and diff, and related artifact commands;
- Golem execution for a growing closed Nat/Bool/String subset;
- bounded source-module imports, definitions, and module-graph execution;
- checker reconstruction of enumeration units, field-bearing inductives, quotients, and direct recursive families;
- standalone checkable `.olean` snapshots;
- bounded native `lean` personality including imports and `#check`;
- `why-trusts`, `audit --tcb`, suite identity, hash-chained run receipts, and durable create-new artifact publication.

Representative commits: `0833f781`, [`32820239`](https://github.com/Dicklesworthstone/franken_lean/commit/328202398fc669d7db5d4eb5730aa692129838d0), `1af9d5b1`, [`f4960d71`](https://github.com/Dicklesworthstone/franken_lean/commit/f4960d713858b770c25f40c60fff41e83a219b83), [`aa0849b0`](https://github.com/Dicklesworthstone/franken_lean/commit/aa0849b01a4dc19f7b9096c45fa6173093d26d9d), `ef78cef4`.

## 7. Pinned Prelude frontier and executable agent control — 2026-08-29 → 2026-09-01

Landed:

- corrected `Init.HEq` hygienic recursor reconstruction;
- corrected the direct-recursive `Init.Nat` model and forged-recursion refusal cells;
- a real-artifact Nat council test and explicit non-vacuous runner derived from `SUITE.lock`;
- `AGENT_FRONTIER_PROTOCOL.md` with immutable Git and artifact anchors, semantic ownership, typed first-failure frontiers, negative evidence, and one-variable experiments;
- executable frontier auditing, deterministic Beads selection, and concrete dependency-cycle witnesses.

The full `fln-51y8` sequential `Init.Prelude` council remains open. A bounded Nat cell is not evidence that the complete Prelude frontier passed.

Representative commits: [`2ad0eb21`](https://github.com/Dicklesworthstone/franken_lean/commit/2ad0eb21cc16b132407de07158ff39e81c69db2b), [`72502cc3`](https://github.com/Dicklesworthstone/franken_lean/commit/72502cc31f6e9f67c350033e663eef5ef0de63d3), [`f72025e3`](https://github.com/Dicklesworthstone/franken_lean/commit/f72025e381d9d103a6c5845c8b6b1ef9ba51fb0b), [`fcbe18f2`](https://github.com/Dicklesworthstone/franken_lean/commit/fcbe18f257c957084e6372b631541aff0e845d93), [`69c07154`](https://github.com/Dicklesworthstone/franken_lean/commit/69c07154acc175fbb58f16e8e2db7d345327418f).

## 8. Lantern transport and Full-sync document authority — 2026-09-01

Landed:

- bounded Content-Length framing, header and resource ceilings, strict Content-Type handling, and failure-atomic writes;
- complete structural JSON validation for the supported JSON-RPC surface;
- decoded string escapes and surrogate pairs;
- root-only envelope routing and deterministic integer, string, and null request IDs;
- lifecycle handling for initialize, initialized, shutdown, and exit;
- Full-sync `didOpen`, `didChange`, `didSave`, and `didClose`;
- independent open-document, source-byte, and URI-key authority;
- monotone document versions, stale-source invalidation, textless-save replay, and diagnostic clearing on close;
- explicit refusal of fabricated Lean RPC sessions.

Representative commits: `fced6257`, `81d33852`, `9e50fdef`, `637176fd`, `2114cd59`, `60ebc07a`, `f2af73ff`.

## 9. Diagnostic publication, waits, and resource receipts — 2026-09-02

Landed:

- modular JSON, wire, document-session, and wait implementations;
- structural callback validation and current-document URI binding;
- separate accepted-document and diagnostic-publication frontiers;
- exact complete, authority, and `diagnosticCount:0` accounting;
- non-authoritative outcomes that clear stale diagnostics and cannot release waits;
- bounded `waitForDiagnostics`, exact cancellation, and deterministic close/shutdown completion;
- complete-wire versus body-byte transcript receipts;
- independent open-document URI metadata limits;
- public framed-stdio regression transcripts.

Representative commits: [`57a268bc`](https://github.com/Dicklesworthstone/franken_lean/commit/57a268bcd1a5656b3bf4d983a7630eb709bc819f), [`32713f48`](https://github.com/Dicklesworthstone/franken_lean/commit/32713f480a77e94d8331ba064841bf72ca20377a), [`ab417cc9`](https://github.com/Dicklesworthstone/franken_lean/commit/ab417cc985dec40518d3e4318626c3a9bf4f0387), `9a8f2362`, `5583c65f`, `a4807ece`.

## 10. Strict client, server, replay, and correlation evidence — 2026-09-02

Landed:

- syntax-only, lifecycle, and document-semantic client validation grades;
- known method role and parameter-container contracts;
- side-effect-free strict replay preflight;
- metadata-only frame inspection;
- structural server transcript validation for notifications and result/error responses;
- known server notification payload checks;
- canonical request-ID correlation using exact number lexemes, decoded string identity, and deterministic re-escaping;
- bounded client request, server response, decoded metadata, and correlation indexes;
- exact one-to-one response joins with no missing, duplicate, or unsolicited responses.

Representative commits: [`025c4c86`](https://github.com/Dicklesworthstone/franken_lean/commit/025c4c86018484177a1ba1e02c908373bfd29fa3), [`c150fa9e`](https://github.com/Dicklesworthstone/franken_lean/commit/c150fa9e9c690f13303161bd3ab96b718ba125ef), `a1a4fa8f`, `c633fb62`, `53e2f14d`, `691b6d6b`, `f797d305`, `4c10c660`, `a17ae30e`.

## 11. Cancellation-bound session and response evidence — 2026-09-02

Landed:

- `fln.lsp-client-session/3` with globally unique canonical request IDs and explicit count and byte limits;
- prior-request authority for every non-null cancellation target;
- duplicate cancellation refusal and diagnostic-wait versus other-request classification;
- covered-versus-future diagnostic-wait counts;
- cancellation state stored on the existing bounded request record rather than another copied-ID map;
- independent join-side reconstruction of request and cancellation indexes;
- `fln.lsp-client-server-correlation/4` response classification for every cancelled target as `RequestCancelled`, normal result, or another valid error;
- installed-binary evidence for canonical aliases, numeric-lexeme non-equivalence, cancellation refusal, and joined cancellation outcomes.

A result after cancellation is disclosed rather than rejected because cancellation is advisory and separate recordings do not establish event order.

Representative commits: [`94717cd2`](https://github.com/Dicklesworthstone/franken_lean/commit/94717cd2592885594342b08b809947d3c4dc1cd1), [`71e3fcaf`](https://github.com/Dicklesworthstone/franken_lean/commit/71e3fcaf7a98938fe4908ef05f25c1405a17882f), [`73cdb40d`](https://github.com/Dicklesworthstone/franken_lean/commit/73cdb40d47b4d79a2d9acbd91a47623fba88c076), [`b09f7ea1`](https://github.com/Dicklesworthstone/franken_lean/commit/b09f7ea1ac2e760fb7241f76c7855d74d682d587), [`88d9970f`](https://github.com/Dicklesworthstone/franken_lean/commit/88d9970f9c8491f2a454516da8e01071a2f0db64).

## 12. Method-bound response evidence — 2026-09-02

This tranche closes a different evidentiary gap: a server stream could previously contain exactly one response for every canonical client ID while returning behavior inconsistent with the live bounded dispatcher.

### Landed

- Each independently rebuilt client request entry now carries one fixed-size method contract beside its already bounded canonical ID.
- Correlation schema advances to `fln.lsp-client-server-correlation/5` and names `fln.lsp-method-response/1`.
- The join validates the current outer response behavior:
  - `initialize` requires an object result;
  - `shutdown` requires `null`;
  - diagnostic waits permit an object result, `RequestCancelled`, or `RequestFailed`;
  - plain goals, term goals, hover, completion, and definition require the current no-information `null` result;
  - unsupported Lean RPC requires `RequestFailed`;
  - unknown methods require `MethodNotFound`.
- Every matched response belongs to exactly one method class.
- Method-derived result counts reconcile with validated server result responses.
- Method-derived error counts reconcile with validated server error responses.
- The receipt reports each method class and zero method-contract violations.
- A stale positive CLI fixture that expected `MethodNotFound` for hover was corrected to the live dispatcher's `null` response.
- A new installed-binary negative cell proves that the same wrong hover response now fails without a success receipt.
- Static review caught and corrected an invalid `const fn` string-method classifier before documentation closeout; method classification is runtime-only.

### Representative commits

- [`9c498a51`](https://github.com/Dicklesworthstone/franken_lean/commit/9c498a514593d25b000ffe8032d12235e95f346a) — method-bound response classification and schema v5.
- [`643af6c1`](https://github.com/Dicklesworthstone/franken_lean/commit/643af6c1ceaab860ff3129c502bed3d4dfa9e9ff) — installed help contract.
- [`e61181d5`](https://github.com/Dicklesworthstone/franken_lean/commit/e61181d5479641d26e1408d29198c0c75cfdb7f4) — installed positive and mismatch evidence.
- [`0dae67c9`](https://github.com/Dicklesworthstone/franken_lean/commit/0dae67c9c800852dbd6af7527e97a9b493a2eac4) — compile-level runtime-only classifier correction.

### Evidence boundary

The repository owns focused unit and installed-binary tests for this tranche. The editing environment did not contain `cargo` or `rustc`, and hosted Actions were intentionally not used, so this changelog does not claim a same-session green Rust run.

Method-response schema v1 is intentionally an outer contract. It does not yet prove every initialize capability, the exact inner successful diagnostic-wait object, useful editor semantics, cross-stream timing, active-work cancellation, source-aware production projection, Lean RPC, shared import state, full unmodified-editor parity, or the complete pinned Prelude council.

---

## Notes for agents

- Use [`IMPLEMENTATION_STATUS.md`](IMPLEMENTATION_STATUS.md) for current evidence claims; the README is the 1.0 target-state specification.
- The tracker of record is [`.beads/issues.jsonl`](.beads/issues.jsonl); Beads IDs are not GitHub Issues.
- The Reference is an oracle and fixture source only.
- Generated contracts such as `KERNEL_CONTRACT.md`, `ABI_CONTRACT.md`, and `OLEAN_CONTRACT.md` are compatibility authorities; do not hand-copy their facts into implementation code.
- A green synthetic fixture is not a pinned-artifact claim. Sequential compatibility work reports `last proven -> first non-success -> typed class`.
- ID equality, cancellation classification, and method-bound outer response shape are protocol facts, not proof of inner semantic payloads or event timing.
- Full semantic Lantern and RPC, mathlib-scale closure, and release-grade distribution remain active program work even though substantial bounded slices are live.
