# Changelog

This is a synthesized, agent-facing changelog for the full history of **franken_lean**.

Scope window: project inception on **2026-07-21** through unreleased HEAD **[`9a8860ab`](https://github.com/Dicklesworthstone/franken_lean/commit/9a8860aba1bf88cf68d4c01785126e8dca6d9435)** on **2026-08-19**.

**franken_lean** is a native-Rust reimplementation of the Lean 4 toolchain (parser, elaborator, trusted kernel, VM, runtime/ABI twin, build system, LSP). Workspace crate version is still **`0.0.0`**. There are **no git tags** and **no GitHub Releases** as of this writing (`gh release list -R Dicklesworthstone/franken_lean` is empty). Do not invent a `v0.x` release page.

This document was rebuilt from:

- git history on `main` (2,501 commits / 2,495 non-merge; 1,378 in 2026-07, 1,117 in 2026-08)
- tag and GitHub Release metadata (none)
- the Beads tracker in [`.beads/issues.jsonl`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) (~463 issues; 295 closed, 32 epics)
- README / plan / contract files at the pin

It is organized by landed capabilities, not raw diff order. Representative commits use live GitHub URLs. Beads IDs (`fln-…`, `franken_lean-…`) are records in `.beads/issues.jsonl`, not GitHub Issues.

---

## Version Timeline

`Kind` distinguishes a published GitHub Release from a plain git tag. This repository has neither.

| Version | Kind | Date | Summary |
|---------|------|------|---------|
| inception [`45e3bd2a`](https://github.com/Dicklesworthstone/franken_lean/commit/45e3bd2a79a0ea9cbcbb81ecaaa6ec296ca86e79) | unreleased HEAD | 2026-07-21 | Master plan, README, AGENTS, LICENSE; beads graph seeded (96 → 108 issues). |
| workspace [`3df0543d`](https://github.com/Dicklesworthstone/franken_lean/commit/3df0543d9537b0a930e7e72ba9b779bfa0e49ad5) | unreleased HEAD | 2026-07-22 | §21 crate map: 31 stub crates, pinned nightly, structural CI (`fln-8mj`). |
| current HEAD [`9a8860ab`](https://github.com/Dicklesworthstone/franken_lean/commit/9a8860aba1bf88cf68d4c01785126e8dca6d9435) | unreleased HEAD | 2026-08-19 | Bounded native `lean` personality, independent checker/olean reconstruction, Golem source execution. Workspace still `0.0.0`. |

---

## 1) Inception, crate map, and G0 constitution (2026-07-21 → 2026-07-22)

The repository starts as a plan, not a compiler. The first two days stand up the workspace that every later subsystem is gated against.

### Delivered capability

- Comprehensive design plan, agent conventions, and MIT + OpenAI/Anthropic Rider license.
- Beads task graph projecting the plan (96 issues, then 105, then 108 after an adversarial coverage pass).
- §21 cargo workspace: 31 stub crates, pinned nightly, structure-guard, `SUITE.lock` dependency-closure audit (G0-10).
- Fail-closed evidence harness (`scripts/evidence.py`, `check.sh`) and vendored Lean Reference tree used only as the differential oracle.

### Closed workstreams

- [`fln-8mj`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) W1 workspace scaffolding.
- [`franken_lean-xwf`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) G0-10 `SUITE.lock` audit.
- [`franken_lean-rur`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) CI wiring `check.sh` as the test step.

### Representative commits

- [`45e3bd2a`](https://github.com/Dicklesworthstone/franken_lean/commit/45e3bd2a79a0ea9cbcbb81ecaaa6ec296ca86e79) Initial commit: comprehensive plan, README, AGENTS, LICENSE.
- [`d7443ac5`](https://github.com/Dicklesworthstone/franken_lean/commit/d7443ac5) Add beads task graph: 96 issues projecting the comprehensive plan.
- [`3df0543d`](https://github.com/Dicklesworthstone/franken_lean/commit/3df0543d9537b0a930e7e72ba9b779bfa0e49ad5) Scaffold the §21 workspace — 31 stub crates, pinned nightly, structural CI gate.
- [`6c1f089c`](https://github.com/Dicklesworthstone/franken_lean/commit/6c1f089c) G0-10 dependency-closure audit + authoritative `SUITE.lock`.
- [`9a0011f1`](https://github.com/Dicklesworthstone/franken_lean/commit/9a0011f1) Vendor the exact Lean Reference tree.
- [`0803079f`](https://github.com/Dicklesworthstone/franken_lean/commit/0803079f) `scripts/evidence.py` — fail-closed evidence harness for the shell gates.

---

## 2) Crucible kernel, generated contracts, Tribunal bootstrap (2026-07-22 → 2026-07-25)

This is the first real compiler surface: a kernel that judges, contracts extracted from the pin rather than remembered, and a Tribunal that can disagree with the Reference.

### Delivered capability

- `fln-core` term plane: names, levels, `Expr` inventory, options, positions.
- `KERNEL_CONTRACT.md` as a CI-checked Judgment Specification (schema-pinned expr/level).
- Crucible K1 bootstrap: the kernel exists and judges; TCB soundness tests confine proof irrelevance to `Prop`.
- Generated ABI and `.olean` format contracts at the pin (`ABI_CONTRACT.md`, `OLEAN_CONTRACT.md`) plus extern/builtin censuses.
- Tribunal bootstrap: epoch lab, Reference-vs-Reference differential, Parity Ledger schema.
- Owned `fln-bignum` arithmetic core with loss-free `NatLit` interop; KR-313/KR-314 literal acceleration replays `Init.Prelude` 1755/1755.
- Kernel mutation campaign covering recursor dispatch, defeq binder domains, quotient init, and K-conversion.

### Closed workstreams

- [`franken_lean-p8a`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) `fln-core`.
- [`franken_lean-79k`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) kernel judgment contract.
- [`franken_lean-zht`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) Crucible K1 bootstrap.
- [`franken_lean-53v`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) canonical contract extraction.
- [`fln-euo`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) Tribunal bootstrap (closed epic).
- [`franken_lean-npl`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) `fln-bignum`.

### Representative commits

- [`7ed677c2`](https://github.com/Dicklesworthstone/franken_lean/commit/7ed677c294339e4ce15bca65d90a653493a035a8) `fln-core` Reference-observable Lean kernel term-plane types.
- [`f85c9af6`](https://github.com/Dicklesworthstone/franken_lean/commit/f85c9af696c076f7d1b83e3d4820e565ab7e6360) Normative kernel judgment contract with schema-pinned expr/level.
- [`f775674d`](https://github.com/Dicklesworthstone/franken_lean/commit/f775674d) `KERNEL_CONTRACT.md` — the Judgment Specification, CI-checked like code.
- [`8ece0b70`](https://github.com/Dicklesworthstone/franken_lean/commit/8ece0b7086d8dbdadd4a9fe7dc3e5ec35c0e5727) Crucible K1 bootstrap — the kernel exists and judges.
- [`0f21aede`](https://github.com/Dicklesworthstone/franken_lean/commit/0f21aede1109f76719d579994858498721a90591) Generated ABI and `.olean` format contracts at the pin + TCB soundness tests.
- [`06ba84b2`](https://github.com/Dicklesworthstone/franken_lean/commit/06ba84b2) Tribunal bootstrap — epoch lab, Reference-vs-Reference differential, Parity Ledger.
- [`ee425e82`](https://github.com/Dicklesworthstone/franken_lean/commit/ee425e82) KR-313/KR-314 literal acceleration — `Init.Prelude` replays 1755/1755.
- [`74092564`](https://github.com/Dicklesworthstone/franken_lean/commit/74092564) G0-2 kernel spike — the kernel checks real modules from oleans.

---

## 3) Marrow ABI twin, olean codec, Grimoire environment (2026-07-22 → 2026-07-26)

Runtime and persistence land in parallel with the kernel: the `lean_object` C ABI twin, compacted olean loading, and a persistent environment with O(1) snapshots.

### Delivered capability

- Marrow CompatHeap: object model, tri-state RC, membrane, shadows; stage0 code executes on Marrow.
- Compacted regions: mmap primitives, relocation engine, live olean loading; one region engine under the olean reader.
- Grimoire (`fln-env`): persistent HAMT, O(1) snapshots, extension contracts, dual roots; declaration-tag identity; bounded admission.
- Stack-safe Drop/encode/decode for deep `Expr`/`Level` trees (canon overflow class).

### Closed workstreams

- [`fln-lld`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) / [`franken_lean-83r`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) Marrow membrane; stage0 executes.
- [`fln-wgp`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) compacted-region olean loading.
- [`fln-amv`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) Grimoire environment (parent still open; many child slices closed).
- [`franken_lean-fnj`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) / [`franken_lean-canon-stack-safe-drop-6gy`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) stack-safe canon.

### Representative commits

- [`5d6cb2b2`](https://github.com/Dicklesworthstone/franken_lean/commit/5d6cb2b2) Marrow CompatHeap core — object model, tri-state RC, membrane, shadows.
- [`1e4b7387`](https://github.com/Dicklesworthstone/franken_lean/commit/1e4b7387) Apply membrane + once cells — stage0 code executes on Marrow.
- [`1eca4667`](https://github.com/Dicklesworthstone/franken_lean/commit/1eca4667804e0ad717d2c1703040d6f22d1bb083) Compacted regions: mmap primitives, relocation engine, real-olean live loading.
- [`94348b02`](https://github.com/Dicklesworthstone/franken_lean/commit/94348b02) The codec seam — one region engine under the olean reader.
- [`156f9ee7`](https://github.com/Dicklesworthstone/franken_lean/commit/156f9ee792812295e44dd0d53540b2a17e0c1ea2) Grimoire environment — persistent HAMT, O(1) snapshots, extension contracts, dual roots.
- [`f18b2f4e`](https://github.com/Dicklesworthstone/franken_lean/commit/f18b2f4e) Stack-safe Drop & rendering for the term plane.

---

## 4) Vellum parser and Verdict SAT (2026-07-24 → 2026-07-25)

The parser/macro subsystem is named **Vellum** (Quill is reserved for Frankensearch). The owned CDCL solver **Verdict** replaces the external CaDiCaL TCB for `bv_decide`.

### Delivered capability

- Vellum naming contract; SourceInfo with byte/scalar/UTF-16 projections; lossless green-tree law.
- Solver-independent Verdict contract plane; versioned CNF/proof schema; independent streaming proof checker; frozen certificate goldens.
- Kernel-checked `bv_decide` integration over an opaque checked-declaration capability.
- Nested-inductive auxiliary translation under the full Lean.Syntax ruleset.

### Closed workstreams

- [`fln-7gr6`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) Vellum naming contract.
- [`fln-7li`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) W4 Vellum engine (closed epic).
- [`fln-23cz`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) Syntax/SourceInfo lossless green tree.
- [`franken_lean-lu5`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) Verdict owned CDCL (closed epic).
- [`franken_lean-o5rt`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) versioned CNF and proof schema.
- [`franken_lean-apgi`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) independent streaming proof checker.

### Representative commits

- [`76893060`](https://github.com/Dicklesworthstone/franken_lean/commit/76893060447154a1272fe26d521825b32be823fd) Reserve Quill for Frankensearch; FrankenLean parser/macro subsystem is Vellum.
- [`e20cded9`](https://github.com/Dicklesworthstone/franken_lean/commit/e20cded9428b85005d67dd5d13978706818a452b) Vellum slice 1 — SourceInfo, byte/scalar/UTF-16 projections, lossless law.
- [`b823faf1`](https://github.com/Dicklesworthstone/franken_lean/commit/b823faf160cf7987ea1ff8e7fa6dae3e01ee5944) The solver-independent contract plane (plan §12.5).
- [`ece924a5`](https://github.com/Dicklesworthstone/franken_lean/commit/ece924a5) Close reflected-theorem publication over the opaque kernel capability.
- [`26eaaafb`](https://github.com/Dicklesworthstone/franken_lean/commit/26eaaafb) Integrate kernel-checked `bv_decide`.
- [`c8422920`](https://github.com/Dicklesworthstone/franken_lean/commit/c8422920) Freeze Verdict certificate goldens.

---

## 5) Evidence-join hardening (2026-07-25 → 2026-08-02)

A large fraction of late-July commits bind claims to producers: mandated-mutant joins, kernel-LOC covenant disclosure, D3 SAFETY-note enforcement, UBS timeout-must-not-become-rejection, and granularity of coverage rows (file vs target vs function). This is Tribunal machinery, not a substitute for compiler work; later waves still had to land the elaborator and VM.

### Delivered capability

- Mandated-mutant markers joined to the tests that kill them, with expiring receipts.
- Kernel LOC covenant disclosed from the same walk that enforces it.
- D3 SAFETY notes written and enforced on `fln-unsafe-abi`; crate-root `forbid(unsafe)` attribute as FLN-STRUCT-011.
- Evidence rows cite exact test functions rather than files; ignored-producer class closed.
- UBS scanner timeout is not promoted to a quality-gate rejection (FL-INV-07).

### Closed workstreams

- [`fln-mandated-mutant-join-unwatched-uagk`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl)
- [`franken_lean-kernel-loc-covenant-not-disclosed-t0g7`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl)
- [`franken_lean-d3-safety-note-unenforced-cdbg`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl)
- [`fln-ubs-timeout-promoted-to-rejection-pekl`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl)
- [`fln-wwvr`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) pinned option / CLI / Lake / LSP wire census.

### Representative commits

- [`cd195a90`](https://github.com/Dicklesworthstone/franken_lean/commit/cd195a90) Join §18's mandated mutants to the tests that kill them.
- [`2f9112f7`](https://github.com/Dicklesworthstone/franken_lean/commit/2f9112f7) Kernel LOC covenant disclosure.
- [`5a4cfd35`](https://github.com/Dicklesworthstone/franken_lean/commit/5a4cfd35) Write the 28 SAFETY notes and enforce D3's note half in `fln-unsafe-abi`.
- [`609064e5`](https://github.com/Dicklesworthstone/franken_lean/commit/609064e5) Gate promoted a scanner's non-answer to a rejection, in a run declaring FL-INV-07.
- [`e38b173a`](https://github.com/Dicklesworthstone/franken_lean/commit/e38b173a) D3 crate-root attribute — FLN-STRUCT-011.

---

## 6) Elaborator seed and Golem VM (2026-07-31 → 2026-08-01)

The product's critical path was a 6-line `fln-elab` stub. This wave closes the first source-text → kernel-accepted-constant seam and stands up Golem (FIR / FLBC interpreter).

### Delivered capability

- Elaborator seed: source text elaborates to a kernel-accepted constant.
- Facade stubs generated from the pin — 170/170 elaborate.
- Golem: retained FIR/FLBC prototype, governed ABI value state, semantic inline caches, heartbeat IO intrinsics.
- G0-3 parity comparator: the verdict Golem is held to.

### Closed workstreams

- [`fln-5720`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) seed the elaborator (closed). Parent epic [`franken_lean-7jr`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) (Athanor/Synod/Mirror) remains open.
- [`fln-52k`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) Golem epic remains open; FIR/FLBC prototype landed as a slice.

### Representative commits

- [`7c48295c`](https://github.com/Dicklesworthstone/franken_lean/commit/7c48295c0c58bf78862032ecf7445cdae80be26b) Elab: the seam closes — source text to a kernel-accepted constant.
- [`a34e7074`](https://github.com/Dicklesworthstone/franken_lean/commit/a34e7074245606b3da7d9693277ed43c96d69299) Close first source-to-kernel seam.
- [`f99721d1`](https://github.com/Dicklesworthstone/franken_lean/commit/f99721d1) Facade stubs generated from the pin — 170/170 elaborate.
- [`be81a269`](https://github.com/Dicklesworthstone/franken_lean/commit/be81a269aa672171df4b3f14472934a1cd783953) Integrate retained FIR FLBC prototype.
- [`286d1f04`](https://github.com/Dicklesworthstone/franken_lean/commit/286d1f04) G0-3 parity comparator — the verdict Golem is held to.
- [`3be88f54`](https://github.com/Dicklesworthstone/franken_lean/commit/3be88f54) Add semantic inline caches.

---

## 7) Independent checker, owned libm, ABI effects (2026-08-03 → 2026-08-09)

`fln-checker` starts admitting real declaration kinds (the Independent Judge path). Owned `fln-libm` replaces platform libm for deterministic `Float`. Marrow grows IO/Task ABI exports.

### Delivered capability

- Checker admission for KR-109..KR-978 family (lets, literals, projections, axioms, definitions/theorems/opaques, unsafe/partial quarantines, mutual blocks).
- Owned deterministic libm baseline: trig reduction, hyperbolic paths, ULP harness; a reported `atanh` defect was the std oracle's, not `fln-libm`'s.
- ABI: `lean_io_allocprof` / `lean_io_timeit`, panic/dbg streams, backtrace through the panic arm chooser.

### Closed workstreams

- [`franken_lean-gii.20` … `gii.28`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) W3 `fln-checker` KR slices.
- Parent epic [`franken_lean-9pg`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) Crucible & Bignum remains open.

### Representative commits

- [`ea3bbbf6`](https://github.com/Dicklesworthstone/franken_lean/commit/ea3bbbf6) KR-970..973 declaration admission — the checker can now say VERDICT.
- [`654edb49`](https://github.com/Dicklesworthstone/franken_lean/commit/654edb49c474f2af123e3a744c569f6d050fb8ed) `fln-libm`: add owned deterministic baseline.
- [`77db82ef`](https://github.com/Dicklesworthstone/franken_lean/commit/77db82ef) `fln-libm`: add full-range trig reduction.
- [`eec4a67f`](https://github.com/Dicklesworthstone/franken_lean/commit/eec4a67f) CORRECT the ulp harness — the atanh "defect" was the std oracle's.
- [`dcb65dcf`](https://github.com/Dicklesworthstone/franken_lean/commit/dcb65dcf) Export `lean_io_allocprof` and `lean_io_timeit`.
- [`ec2651ab`](https://github.com/Dicklesworthstone/franken_lean/commit/ec2651ab) Publish checked `bv_decide` engine successors.

---

## 8) Native CLI, source execution through Golem, olean reconstruction (2026-08-10 → 2026-08-19)

`fln` becomes a tool you can run: inspect oleans, execute closed Nat/Bool/String source, check oleans, reconstruct bounded inductive/quot units, and drive a bounded native `lean` personality with imports and `#check`.

### Delivered capability

- CLI: `fln run` for closed Nat definitions and dependent source batches; `fln check-olean`; bounded olean inspection and semantic olean diff; pinned ilean audit; `fln flbc run`.
- Golem executes generated Nat (div/mod/gcd/pred/bitwise/power/shift), Bool comparison, and `String.append` / length rows; FLBC schema admits `OwnedOrScalar` for Nat results.
- Source pipeline partitions Lean modules into imports and `def` commands; closed caller-named import graphs; refuses import-only products.
- Independent checker + olean reconstruction: enumeration units, nonrecursive field-bearing inductives, four-row Quot authority envelope, acyclic mutual metadata; standalone checkable olean snapshots.
- Heap-stack walks for kernel defeq/WHNF/instantiate and runtime Name/Level/Expr projection — the 256/2048-frame host-stack caps are gone.
- Native `lean` personality: local imports, silent function definitions, dual-checked `#check` across a planned module graph, silent imported `#check`.

### Closed workstreams

- Checker KR admission continues through [`f4960d71`](https://github.com/Dicklesworthstone/franken_lean/commit/f4960d713858b770c25f40c60fff41e83a219b83) (quot initializer) and [`a1975219`](https://github.com/Dicklesworthstone/franken_lean/commit/a1975219) (field-bearing inductives).
- Distribution epic [`fln-86m`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl) remains open; this is not a release.

### Representative commits

- [`0833f781`](https://github.com/Dicklesworthstone/franken_lean/commit/0833f781) Add bounded `fln run` for closed Nat definitions.
- [`32820239`](https://github.com/Dicklesworthstone/franken_lean/commit/328202398fc669d7db5d4eb5730aa692129838d0) Add `fln check-olean` with structured success and dispositioned errors.
- [`518c453b`](https://github.com/Dicklesworthstone/franken_lean/commit/518c453b) Execute Nat arithmetic over scalar and mpz values.
- [`1af9d5b1`](https://github.com/Dicklesworthstone/franken_lean/commit/1af9d5b1) Execute checked `String.append` through Golem.
- [`3c3cbecd`](https://github.com/Dicklesworthstone/franken_lean/commit/3c3cbecd) Partition Lean source modules into imports and def commands.
- [`f4960d71`](https://github.com/Dicklesworthstone/franken_lean/commit/f4960d713858b770c25f40c60fff41e83a219b83) Admit the four-row quotient initializer (KR-950..954).
- [`aa0849b0`](https://github.com/Dicklesworthstone/franken_lean/commit/aa0849b01a4dc19f7b9096c45fa6173093d26d9d) Emit checkable standalone olean snapshots.
- [`7762ddb8`](https://github.com/Dicklesworthstone/franken_lean/commit/7762ddb8c6463e60b1aeaa42c3b6f190412909c9) Run terminal `#check` across a planned Lean module graph.
- [`7ff2616a`](https://github.com/Dicklesworthstone/franken_lean/commit/7ff2616a) Accept silent imported `#check` on the native lean path.
- [`269126dc`](https://github.com/Dicklesworthstone/franken_lean/commit/269126dc) Substitute loose bvars iteratively, not under a 2048-frame cap.

---

## 9) Aug 19 2026 repo-janitor docs-reorg

A small hygiene wave. The commit subject claims that root planning docs moved into `docs/planning/`; the landed diff is **`.gitignore` only** (skill-loop scratch untracked). `COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md` and the generated contracts (`KERNEL_CONTRACT.md`, `ABI_CONTRACT.md`, `OLEAN_CONTRACT.md`, …) remain at repo root, and README links still point there.

### Representative commits

- [`9a8860ab`](https://github.com/Dicklesworthstone/franken_lean/commit/9a8860aba1bf88cf68d4c01785126e8dca6d9435) `chore(janitor): untrack skill-loop scratch; move root planning docs into docs/planning/`.

---

## 10) Trust surfaces on the native CLI (2026-08-23)

Four promised `fln` verbs became real, all answering from decoded pinned-format
artifacts with no new engines: `why-trusts` (bounded axiom closure over a closed
import set — types plus definition/theorem/opaque bodies; recursor rules,
instance selections, and rewrite provenance explicitly out of scope), `audit
--tcb` (per-module axiom inventory plus unsafe/partial definition counts),
`identity` (compile-time-baked SUITE.lock pins via a ledgered `fln-cli`
build.rs, never probed at runtime), and `check-olean --receipts` (hash-chained
JSONL run receipts under fln-hash's `TransparencyLeaf` domain with
`ArtifactClosureComponent` module roots; no clock values, so an identical set
reproduces the file byte-for-byte; no-clobber publication). Receipts attest a
run; they are not proof certificates.

Root-cause fix en route: durable publication in `fln-rt/src/region.rs` opened
the empty parent of bare relative filenames (`Path::parent()` answers
`Some("")`, so the `"."` fallback never fired) and failed ENOENT after a
successful link on `--emit-flbc` / `--emit-sidecar` /
`--emit-olean-snapshot`; normalized across all four sites via
`parent_or_dot`. Kernel covenant re-measured by the enforcing tool:
9,777 / 12,000 LOC (81.4%).

### Delivered capability

- `fln why-trusts answer snap.olean` → `axioms: Nat, Nat.add` over a real
  checked snapshot emitted by `fln run --emit-olean-snapshot`.
- `fln audit --tcb` inventories 22 seed axioms over that snapshot in one pass.
- `fln check-olean --receipts rc.jsonl <closed-set-dir>` writes a chained
  receipt set whose row hash chain verifies line-by-line.

### Closed workstreams

 Advances the W3 Independent Judge CLI surface (`fln-fur`, `fln-dcv` scope);
 no gate is claimed.

### Representative commits

- `ef78cef4` `feat(cli): trust surfaces — why-trusts, audit --tcb, identity,
  check-olean --receipts`.

---

## Notes for Agents

- Start with the version timeline if you need chronology. There is no `v0.x` tag and no GitHub Release; HEAD is the only published artifact.
- The README is written in present tense as the 1.0 *target* state (G0→G6 in the plan). This changelog is what has actually landed. Golem, Lake, LSP daemon, mathlib-scale corpus, and distribution are still open epics.
- Oracle-Only Law: the vendored Lean Reference is a differential oracle, not a linked component. Do not "win" a bench by calling upstream Lean.
- Tracker of record is [`.beads/issues.jsonl`](https://github.com/Dicklesworthstone/franken_lean/blob/main/.beads/issues.jsonl). Use `br show <id>`; do not open GitHub Issues for these IDs.
- Kernel judgment inventory is `KERNEL_CONTRACT.md` (CI-checked). ABI/olean layouts are generated from the pin (`ABI_CONTRACT.md`, `OLEAN_CONTRACT.md`); do not hand-copy constants.
- A large late-July commit mass is evidence-join / gate integrity. That is real work, but it is not a substitute for the elaborator/VM/checker capability waves above.
- `origin/master` exists only as a legacy-URL mirror of `main`.
