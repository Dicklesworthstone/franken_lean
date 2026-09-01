# Changelog

This is the synthesized, agent-facing changelog for **franken_lean**. It records what has actually landed; the [`README.md`](README.md) intentionally describes the finished 1.0 target state, and [`IMPLEMENTATION_STATUS.md`](IMPLEMENTATION_STATUS.md) is the current evidence-graded status companion.

Scope: project inception on **2026-07-21** through the September 1 implementation/status snapshot at **[`ea891c23`](https://github.com/Dicklesworthstone/franken_lean/commit/ea891c23fb4c44ac4d5020715d9c0121fdc90c32)**. This changelog refresh itself follows that snapshot.

No GitHub Releases were published when this file was refreshed on **2026-09-01**. Do not infer or invent a `v0.x` release from commit activity.

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

## Notes for agents

- The README is the 1.0 target-state specification; use [`IMPLEMENTATION_STATUS.md`](IMPLEMENTATION_STATUS.md) for present implementation/evidence claims.
- The tracker of record is [`.beads/issues.jsonl`](.beads/issues.jsonl); Beads IDs are not GitHub Issues.
- The Oracle-Only Law remains absolute: the pinned Lean Reference is differential evidence/fixture input, never a FrankenLean runtime component.
- Generated contracts such as `KERNEL_CONTRACT.md`, `ABI_CONTRACT.md`, and `OLEAN_CONTRACT.md` are compatibility authorities; do not hand-copy their facts into implementation code.
- A green synthetic fixture is not a pinned-artifact claim. Long sequential compatibility work reports `last proven -> first non-success -> typed class`.
- Full semantic Lantern/LSP/RPC, mathlib-scale end-to-end closure, and release-grade distribution remain active program work even though substantial bounded slices are live.
