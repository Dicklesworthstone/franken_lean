# franken_lean

<div align="center">

[![License: MIT + Rider](https://img.shields.io/badge/License-MIT_+_OpenAI/Anthropic_Rider-blue.svg)](./LICENSE)
[![Rust Edition](https://img.shields.io/badge/Rust-2024_Edition-orange.svg)](https://doc.rust-lang.org/edition-guide/rust-2024/)
[![toolchain: pinned nightly](https://img.shields.io/badge/toolchain-pinned_nightly-purple.svg)](./SUITE.lock)
[![unsafe: forbidden*](https://img.shields.io/badge/unsafe-forbidden*-success.svg)](https://github.com/rust-secure-code/safety-dance/)
[![language: Lean 4 (drop--in)](https://img.shields.io/badge/language-Lean_4_drop--in-teal.svg)](https://github.com/leanprover/lean4)
[![kernel: ≤12 KLOC, dual engine](https://img.shields.io/badge/kernel-%E2%89%A412_KLOC_dual--engine-red.svg)](./COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md)
[![deps: closed universe](https://img.shields.io/badge/deps-closed_universe-black.svg)](./COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md)

**A ground-up, native-Rust reimplementation of the entire Lean 4 toolchain — parser, macro engine, elaborator, trusted kernel, metaprogram compiler and VM, runtime/ABI twin, build system, and language server — that is a drop-in replacement at the binary surfaces (`.olean`, the `lean_object` C ABI, the LSP wire dialect, the `lean`/`leanc`/`lake` CLIs) and deliberately better underneath: deterministic under parallelism, declaration-granular incremental, memory-shared, provenance-transparent, with a ≤ 12 KLOC dual-engine kernel that ships receipts.**

</div>

> **A note on tense (read this first).** This README is written in the **present tense, as if the entire design in [`COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md`](./COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md) is fully realized**: the 1.0 target state where every performance gate is green and every subsystem is live. This is a deliberate choice. It lets the document describe the *finished* system so it gets **trued-up in place as milestones land** (§22's gates G0→G6) rather than rewritten from scratch later. Where the plan itself stages something as genuinely future work or a frontier lane, the README says so plainly. Everything else below is the spec of the system this repository builds.

---

## TL;DR

**The problem.** Lean 4 is one of the most important software artifacts of the decade. Its *ideas* are superb: a small trusted kernel over a rich dependent type theory, an elaborator written in the language itself, hygienic user-extensible syntax all the way down, a metaprogramming model where `simp` and `grind` are just library code, and a 1.5-million-line mathematical corpus (mathlib: 115,000+ definitions, 232,000+ theorems) no other prover ecosystem can match. Its *substrate* is an accident of history: a C++ kernel and runtime nobody has verified, GMP under every literal, a vendored libuv, an external CaDiCaL binary behind `bv_decide`, a mandatory C compiler behind every executable, a bootstrap whose stage0 is megabytes of checked-in generated C, a pointer-dump object format, a process-per-file server that pays ~60 seconds and gigabytes of RSS to import mathlib *per worker*, file-granular invalidation that turns a one-line leaf edit into an afternoon, and an async elaboration mode documented to *change results depending on the schedule*. Both the mathematical community (the build treadmill) and the 2026 AI-for-math research program (per-branch import taxes, no cheap proof-state snapshots) are blocked on the substrate.

**The solution.** `franken_lean` replaces the substrate and keeps every idea. Native Rust end to end — no C++, no GMP, no libuv, no CaDiCaL, no stage0, no C compiler on the sovereign path — buildable by `cargo` from a cold checkout with no prior Lean in the universe. The upstream implementation never executes as a component: it is pinned inside the conformance apparatus as the **differential oracle** it deserves to be (the Oracle-Only Law). Mathlib's tactics run **unmodified** on our own VM against a natively-implemented `Lean.*` surface, and the Tribunal proves, symbol by symbol, that they cannot tell.

**Why `franken_lean`:**

| | `franken_lean` |
|---|---|
| Compatibility | Drop-in at six binary surfaces: source language, `.olean` (read *and* byte-compatible write), the `lean_object` C ABI (`lean.h` twin — existing native plugins load), `.ilean`/artifact chain, the `Lean.*` Meta API, and LSP + `$/lean/*` (vscode-lean4 connects unmodified). |
| Kernel | ≤ 12 KLOC `forbid(unsafe)` dual-engine checker (certified small-step + NbE accelerator, cross-checked), plus an independent in-repo checker and foreign witnesses. Disagreement halts; it never outvotes. |
| Receipts | Every checked declaration can emit a compressed proof certificate; attested checks append to a transparency log; `fln check-olean` re-checks all of mathlib in minutes on a kernel sharing no code with the thing it checks. |
| Determinism | Same input closure ⇒ same environment, same diagnostics, same artifacts, at any thread count — an invariant, tested at {1, 8, 32} threads on every commit **over the Prelude**; the corpus-scale matrix is not built yet, so corpus schedule-independence is inferred rather than measured (beads `fln-8zsq`, `franken_lean-2ki4`). `--reproducible` yields bit-identical artifacts across the certified platform matrix. |
| Incrementality | The environment is a Merkle DAG of content-addressed declarations. A leaf edit re-elaborates its *true dependency cone* (seconds), not its file cone (hours). Whitespace, comments, and reordering invalidate nothing. |
| Server | One daemon, one shared immutable import heap. The ≈60 s × N workers × GBs × N multiplication becomes once-per-daemon; warm attach ≤ 2 s; thousands of O(1) proof-state forks per daemon. |
| Metaprogramming | The entire tactic ecosystem (mathlib, aesop, downstream) runs unmodified on Golem, our register VM whose values *are* ABI objects — one calling convention across interpreted code, JIT'd code, Reference-built plugins, and native builtins. |
| Decision procedures | `bv_decide` runs on Verdict, an owned CDCL solver with owned proof logging and an owned checker. The external-solver TCB is gone. |
| Numerics | Owned kernel-grade bignum (no GMP) and owned deterministic `Float` transcendentals (no platform libm): `#eval` and `native_decide`-class results replay bit-identically across platforms — which upstream cannot promise even to itself. |
| Agent-native | MCP tools over O(1) proof-state snapshots, semantic library search over the live environment, structured machine-readable goals, replayable elaboration traces. The substrate 2026's proof-search papers hand-roll per paper. |
| Provenance | Every declaration, instance selection, simp firing, and kernel verdict is a node in a typed causal graph: impact cones, semantic blame slices, semantic diff, `fln why-trusts`, and conflict-aware semantic merge that re-checks through the kernel. |
| Evidence | Compatibility is never a percentage: per-surface evidence levels L0–L4, per-release levels R0–R5, a machine-checked claim matrix, and documentation CI that rejects wording stronger than the evidence permits. |
| Safety | `forbid(unsafe_code)` everywhere except three named, ledgered boundary crates. The kernel crate contains zero project-authored unsafe. |
| Dependencies | **Closed universe.** `std` + the pinned nightly + the FrankenSuite (asupersync, frankensqlite, franken_networkx, frankensearch, frankentui, franken_markdown, fastmcp_rust, atp). No serde, no tokio, no LLVM, no gmp-sys. Ever. |

---

## Quick example

```bash
# It's a drop-in: your project, your editor, your lakefile, unchanged.
cd my-mathlib-project        # lakefile.lean, lean-toolchain, everything as-is
lake build                   # decl-granular incremental over a content-addressed store
code .                       # vscode-lean4 connects to the daemon and cannot tell

# The Independent Judge: re-check every mathlib olean on a foreign-blooded kernel
fln check-olean ~/.elan/toolchains/*/lib/lean4/library --all --receipts
#   → minutes, with proof certificates and a transparency-logged receipt set

# What does this theorem actually trust?
fln why-trusts Mathlib.Analysis.SpecialFunctions.Log.Basic.log_pos
#   → axioms: propext, Classical.choice · native_decide: none · plugins: none

# Why did that rebuild?
fln build explain Mathlib/Order/Basic.lean
#   → reference decision vs. native decision, changed inputs, cache outcomes

# The proof panel where your agents actually live (tmux/SSH)
fln goals MyFile.lean:142

# Semantic, not textual, diff of a change
fln diff --level interface HEAD~1
#   → "proof-only change" is a checkable claim, not a reviewer's guess

# Serve the prover to agents over MCP: snapshots, tactics, search, budgets
fln serve-mcp --listen 127.0.0.1:8931
```

---

## The eight bets

No single trick makes this a leapfrog. The **composition** of eight bets does, each at or beyond the current frontier, each feasible only because the foundation libraries already exist.

| Bet | One-line statement |
|---|---|
| **B1 · The Ledger** | The environment is a Merkle DAG of content-addressed declarations; builds are memoized queries over it; a one-line leaf edit re-elaborates its true dependency cone (seconds), not its file cone (hours); the "cloud cache" is native CAS sync over atp, not a bolted-on download script. |
| **B2 · The Native Mirror** | The entire `Lean.*`/`Init`/`Std` builtin surface is served *natively*: toolchain-API symbols are Rust implementations registered under upstream names behind a census-generated façade; pure library code is upstream-authored *source* elaborated by our own toolchain; user metaprograms run on our VM and cannot tell. |
| **B3 · Kernel with receipts** | A ≤ 12 KLOC dual-engine trusted checker, deterministic fuel parity, compressed proof-certificate export by default, consensus receipts with an independent checker plus external witnesses, and CI-grade differential checking against foreign kernels — disagreement halts, never outvotes. |
| **B4 · Deterministic parallel elaboration** | Declaration-granular dataflow parallelism with speculative execution and deterministic merge: results are schedule-independent by construction, so parallelism is free to be aggressive. |
| **B5 · Rewriting at machine speed** | simp-compatible rewriting on compiled discrimination automata shipped as per-library indexes, an e-graph saturation lane with kernel-checked proof extraction, and owned decision procedures (Verdict CDCL) replacing the external-solver TCB. |
| **B6 · Agent-native by construction** | An MCP surface, semantic library search, structured machine-readable proof states, O(1) proof-state snapshots for search trees, and replayable elaboration traces — purpose-built for the 2026 reality in which frontier labs benchmark their reasoning models *inside Lean*. |
| **B7 · The causal proof graph** | Every declaration, instance selection, simp firing, macro expansion, capability use, kernel verdict, and build product is a node in a typed provenance graph with completeness classes; impact cones, semantic blame, semantic diff, fragility signals, and conflict-aware **semantic merge** become queries. |
| **B8 · Evidence-native engineering** | Every public claim is a row in a machine-checked claim matrix with an evidence state, a freshness bound, and a reproduction command; documentation CI rejects wording stronger than the matrix permits; compatibility is reported per-surface (L0–L4) and per-release (R0–R5), never as one percentage. |

---

## Design philosophy

These are the constitutional, non-negotiable constraints the whole system is built under. They read like restrictions; they are the moat.

1. **The Oracle-Only Law.** No upstream implementation code executes as a component of FrankenLean, ever — not the C++ kernel, not the self-hosted `Lean.*` elaborator sources, not stage0. The Reference (`leanprover/lean4` at the pinned epoch tag) appears in exactly one place: inside the Tribunal, as the differential oracle, fixture generator, and census-extraction source. The only Lean code FrankenLean ever *executes* is user code — because executing user metaprograms is what the Lean language *is*.
2. **The dependency universe is closed.** Allowed: `std`, the pinned Rust nightly, and the Dicklesworthstone-owned FrankenSuite: [`asupersync`](https://github.com/Dicklesworthstone/asupersync) (runtime, lab, RaptorQ, networking, capabilities), [`frankensqlite`](https://github.com/Dicklesworthstone/frankensqlite) (durable store), [`franken_networkx`](https://github.com/Dicklesworthstone/franken_networkx) (graph algorithms + the CGSE determinism doctrine), [`frankensearch`](https://github.com/Dicklesworthstone/frankensearch), [`frankentui`](https://github.com/Dicklesworthstone/frankentui), [`franken_markdown`](https://github.com/Dicklesworthstone/franken_markdown), [`fastmcp_rust`](https://github.com/Dicklesworthstone/fastmcp_rust), and [`atp`](https://github.com/Dicklesworthstone/atp). Everything else — bignum, allocator, region codec, Pratt engine, unifier, instance engine, IR pipeline, interpreter, JIT, discrimination automata, e-graph core, SAT solver and its proof checker, certificate formats, libm — is built in-house.
3. **Zero mandatory external tools.** Two optional tools, both inherited from the Reference's own contract: a system C compiler *only* for `--backend c` (the native Iron backend needs none) and system `git` *only* for Lake-compatible dependency fetching. No GMP, no libuv, no CaDiCaL, no LaTeX, no vendored C of any kind, ever.
4. **Memory safety is structural.** `#![forbid(unsafe_code)]` in every authoritative crate; project-authored `unsafe` lives only in three named boundary crates (`fln-unsafe-abi`, `fln-unsafe-region`, `fln-unsafe-jit`) with a ledger row per site. The kernel crate is `forbid(unsafe_code)` — the TCB contains zero project-authored unsafe. No unsafe crate can call into the kernel or export anything launderable into a checked declaration; CI proves both structurally.
5. **Determinism as a contract, not a hope.** Same input closure ⇒ same environment, same diagnostics, same artifacts, at any thread count, on any schedule. Wherever an order is semantically free, a registered CGSE policy pins it, and the pinned choice is part of the reproducibility closure.
6. **The kernel answers to no one — and shows receipts.** One authority: `check : Environment × Declaration → Verdict`. Nothing outside `fln-kernel` can admit a constant. Every performance engine is untrusted by construction; every checked declaration can emit a certificate; kernel disagreement with the Reference is release-blocking (with exactly one carve-out: logical soundness outranks bug-parity).
7. **Prohibited shortcuts are constitutional.** No MVP, no "phase where we shell out to real `lean` temporarily", no hosted C++ kernel, no upstream elaborator sources running on our VM as a stand-in, no hand-transcribed ABI constants (every layout is mechanically extracted from the pin), no benchmark claim without its corpus, machine, and claim state.

---

## How it works

`franken_lean` is eleven named subsystems plus four leapfrog surfaces, one mode system, and a conformance apparatus with the Reference sealed inside it.

```
                ┌──────────────────────── front doors ─────────────────────────┐
                │  lean / lake CLIs   ·   Rust API (fln)   ·   lean_* C ABI    │
                └───────┬───────────────────┬───────────────────┬──────────────┘
                        ▼                   ▼                   ▼
      ┌── LANTERN: the server daemon ──┐  ┌── LEDGER: build fabric ──────────┐
      │ LSP + $/lean/* · sessions ·    │  │ decl-granular CAS · Lake surface │
      │ shared import heap · widgets   │  │ frankensqlite store · atp sync   │
      └──────────────┬─────────────────┘  └──────────────┬───────────────────┘
                     ▼                                    ▼
      ┌────────────────── the elaboration pipeline ─────────────────────────┐
      │  VELLUM: parser & macros →  ATHANOR: elaborator (Synod instances)   │
      │                │                    │            ▲                  │
      │                │                    ▼            │ tactics          │
      │                │            GOLEM: user-metaprogram    ⇄  ANVIL:    │
      │                │            compiler & VM (Mirror façade   rewrite &│
      │                │            dispatches to native services) decision │
      │                └────────────┬───────┘            (Verdict CDCL)     │
      └─────────────────────────────┼────────────────────────────────────────┘
                                    ▼
                     CRUCIBLE: the trusted kernel (dual-engine, receipts)
                                    ▼
      ┌── GRIMOIRE: environment & module codec (.olean ⇄ olean-next) ───────┐
      └── MARROW: runtime & ABI twin (lean_object · regions · allocator) ──┘
      ─────────────────────────────────────────────────────────────────────
      PALIMPSEST: provenance, traces, time-travel (observes everything)
      TRIBUNAL (fln-conformance): ledger · differential rigs · gates
      Leapfrog surfaces: BLOODHOUND (search·repair) · FOLIO (docs) · ENVOY (MCP) · WASM Judge
```

- **Marrow** (`fln-rt`, `fln-unsafe-abi`): the runtime and ABI twin. The Reference's object model — headers, tags, scalar packing, tagged-pointer `Nat`s, tri-state reference counting, compacted regions — implemented exactly, with layout constants *mechanically extracted* from the pinned `lean.h` into generated contract tables. Reference-built native plugins `dlopen` into FrankenLean and vice versa; the strongest standing rig compiles upstream's own stage0-generated C against Marrow's exports and runs the upstream runtime suite through the membrane.
- **Grimoire** (`fln-env`, `fln-olean`): the environment (persistent maps with O(1) snapshots — the primitive under speculative parallelism, per-request server views, and agent search trees) and the module codec: byte-compatible `.olean` read *and write*, `.ilean`, plus **olean-next**, a content-addressed, mergeable, diffable frontier format with inline certificates.
- **Crucible** (`fln-kernel`, `fln-bignum`): the trusted kernel. Engine K1 is the certified evaluator a skeptical logician reads in an afternoon; K2 is the NbE accelerator that makes `decide` and mathlib's defeq-heavy corners fast; both implement the same judgment inventory (written down first as `KERNEL_CONTRACT.md`, rule-anchored to Reference source lines), continuously cross-checked, joined by `fln-checker` — a deliberately *different* second implementation on its own decoder — under a consensus policy where disagreement halts. Owned bignum replaces GMP; typed resource budgets make exhaustion a value (`Inconclusive`), never a hang and never a rejection.
- **Vellum** (`fln-parse`, `fln-syntax`): the extensible Pratt parser and hygiene-exact macro engine, preserving the parse/elaborate interleaving (commands install syntax used three lines later), byte-exact positions, and macro-scope observables — with lossless trees, grammar epochs for precise incremental reparse, and error recovery that never changes acceptance.
- **Athanor** (`fln-elab`, with **Synod**, the instance engine): the elaborator — the monadic tower's semantics, the unifier's exact approximation ladder (implemented against golden decision traces mined from an instrumented oracle at Corpus scale), match compilation, the native tactic framework, and the deterministic dataflow scheduler: speculative parallel elaboration with canonical-order commit, so the result is the sequential result, bit-for-bit, at any thread count.
- **Golem** (`fln-comp`, `fln-vm`, `fln-unsafe-jit`): the metaprogram compiler and VM. Elaborated terms → FIR (LCNF-class IR with borrow inference and constructor reuse) → FLBC, a register bytecode whose values *are* Marrow ABI objects — so interpreted code, Iron-JIT'd code, Reference-built plugins, and native builtins share one calling convention with zero conversion. `lakefile.lean`, `#eval`, and every user tactic run here.
- **Anvil** (`fln-anvil`) & **Verdict** (`fln-verdict`): simp with compiled per-library rewrite indexes, an e-graph lane with kernel-checked extraction, `norm_num`/`omega` cores, native `grind` machinery, and an owned CDCL SAT solver with owned proof logging and an owned checker behind `bv_decide`. Every engine is untrusted; every output enters the environment through a kernel-checked artifact.
- **Ledger** (`fln-ledger`, `fln-lake`): the build fabric. Content-addressed declaration records over frankensqlite, the true-cone invalidation law with early cutoff and a published, perturbation-validated invalidation matrix, the bit-compatible Lake surface, cache federation over atp, and epoch-stable caching so the monthly toolchain treadmill stops meaning "the world from zero."
- **Lantern** (`fln-server`): the language server — the identical wire dialect from a single daemon with one shared immutable import heap, snapshot-precise incrementality, structurally race-free diagnostics publication, replayable session bundles, and a machine session API: fork a proof state, apply a tactic, read goals — O(1) per branch, thousands of branches per daemon.
- **Palimpsest** (`fln-trace`): always-on structured provenance and the causal proof graph — typed edges with completeness classes (only Complete/Conservative edges may drive invalidation, welding provenance to soundness), minimal-disagreement unification forensics, instance "why not" trees, semantic diff and merge, fragility signals, time-travel replay, and repro bundles.
- **Tribunal** (`fln-conformance`): the verification apparatus and the program's second-largest subsystem. The Parity Ledger (row-per-symbol, evidence-leveled), differential elaboration at Corpus scale, the instrumented oracle's golden decision traces, codec round-trips, the ABI cross-load matrix, protocol rigs, mutation campaigns, fault drills, fuzzing, metamorphic laws, and the thread-matrix determinism closure.
- **The leapfrog surfaces:** **Bloodhound** (in-toolchain hybrid search, premise retrieval, proof repair, counterfactual analysis — every candidate untrusted until the kernel accepts it), **Folio** (doc-gen4-compatible native HTML/PDF documentation with native mathematics, as an incremental build facet), **Envoy** (the MCP door: budgeted, capability-scoped, receipt-carrying tools over proof-state snapshots), and the **WASM Judge** (the certified kernel in a browser tab: drag a sealed capsule, watch it re-check — zero-install third-party verification).

The full specification lives in [`COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md`](./COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md): the Reference anatomy, the foundation audit, the doctrine, every subsystem at full strength, the Tribunal, the performance gates, the workstreams, the risk register, and the normative appendices.

## How it compares

Honest framing. FrankenLean is not the first project to re-check Lean's kernel; it is the first program to rebuild the *entire toolchain* — elaborator, VM, ABI, formats, build system, server — as one native, deterministic, drop-in system.

| | `franken_lean` | Lean 4 (Reference) | lean4lean / lean4checker | nanoda-class kernels |
|---|---|---|---|---|
| Scope | Full toolchain: parser → elaborator → kernel → VM → build → server | Full toolchain | Kernel re-check only | Kernel re-check only |
| Implementation | Native Rust, `cargo build` from cold checkout | C++ + self-hosted Lean + stage0 generated C | Lean (verified rules) / Lean | Rust |
| Bootstrap | **None** | stage0 treadmill, updated near-nightly | rides the Reference | n/a |
| Kernel TCB | ≤ 12 KLOC forbid-unsafe Rust + owned bignum, dual-engine + independent checker + receipts | ~300 KB C++ + GMP + libm | verified rules (kernel only) | small Rust (kernel only) |
| Runs mathlib's tactics | ✓ unmodified, on our VM | ✓ | ✗ | ✗ |
| `.olean` write / ABI / LSP | ✓ / ✓ / ✓ (byte-compatible) | ✓ / ✓ / ✓ | ✗ | ✗ |
| Deterministic parallel elaboration | ✓ invariant, tested per commit | ✗ (`Elab.async` is schedule-sensitive) | n/a | n/a |
| Incremental granularity | Declaration (true dependency cone) | File (import cone) | n/a | n/a |
| Server import cost | Once per daemon, shared pages | ≈60 s + GBs *per worker* | n/a | n/a |
| External tools | 0 mandatory (cc/git optional) | cc mandatory for executables; git; CaDiCaL for `bv_decide` | — | — |
| Proof certificates / transparency log | ✓ by default | ✗ | export formats exist | partial |

## The `fln` CLI

> `lean`, `leanc`, and `lake` are flag-, exit-code-, and `--json`-compatible with the pin. The new capability lives under the `fln` multiplexer; robot output is versioned and pipeable.

```bash
# Drop-in personalities (flags, exit codes, --json shapes pinned to the Reference)
lean MyFile.lean
lake build && lake test
lean --server                      # the daemon behind the standard wire dialect

# The Independent Judge
fln check-olean <path|project> --receipts    # re-check oleans on the foreign kernel
fln verify-capsule proof.flnpack             # verify a sealed capsule (also: browser/WASM)

# Trust & provenance
fln audit --tcb                    # axioms, native_decide sites, plugins, façade classes
fln why-trusts Mathlib.Data.Real.Basic.add_comm
fln diff --level proof HEAD~1      # source/syntax/interface/proof/reduction/extension levels

# Build forensics
fln build explain Mathlib/Order/Basic.lean
fln doctor --sql                   # SQL REPL over the build database
fln replay MyFile.lean:203         # deterministic re-elaboration of one declaration

# Cache & modules
fln cache get                      # community-cache muscle memory, native CAS underneath
fln olean diff A.olean B.olean     # human-readable module diffs (un-opaqued at last)

# Interactive & agent surfaces
fln goals MyFile.lean:142          # terminal InfoView over the same RPC the editor uses
fln serve-mcp                      # Envoy: snapshots, tactics, search, eval — budgeted
fln identity --json                # implementation commit, epoch, profile, TCB hash
```

## Installation

**1. Install script — *not yet available*.** The planned script detects your platform, fetches the signed release binaries (`lean`, `leanc`, `lake`, `fln`), and installs an elan-compatible toolchain. It is deliberately not shown as a runnable command here: `scripts/install.sh` does not exist yet, and there are no release binaries for it to install. This section becomes a command again when distribution ships one (bead `franken_lean-readme-install-oneliner-wao6`).

Because the release layout is elan-compatible, a project's `lean-toolchain` file can simply name a FrankenLean toolchain and everything downstream — `lake`, the editor extension, CI — just works.

**2. From source** (requires only the pinned nightly, which `rust-toolchain.toml` auto-selects — no prior Lean anywhere):

```bash
git clone https://github.com/Dicklesworthstone/franken_lean
cd franken_lean
cargo build --release        # the whole toolchain, no stage0, no C compiler
```

**3. Embedded, as a Rust library:**

```toml
# Cargo.toml
[dependencies]
fln = { git = "https://github.com/Dicklesworthstone/franken_lean" }
```

```rust
use fln::{Engine, Cx};

fn main() -> fln::Result<()> {
    // Capability-first: the embedder hands the engine a Cx and gets
    // determinism, cancellation, and budget enforcement structurally.
    let engine = Engine::builder().toolchain_epoch("v4.32.0").build()?;
    let env = engine.elaborate_project(&Cx::ambient(), "path/to/project")?;

    let verdict = engine.check(&env, "MyProject.my_theorem")?;
    println!("{}", verdict.receipt().to_json());
    Ok(())
}
```

## Quick start

```bash
# 1. Point an existing Lean project at FrankenLean (one line in lean-toolchain)
echo "dicklesworthstone/franken_lean:v4.32.0" > lean-toolchain

# 2. Build it — declaration-granular, content-addressed, deterministic
lake build

# 3. Edit a leaf file, rebuild: the true cone, in seconds, not the afternoon
$EDITOR MyProject/Lemmas.lean && lake build

# 4. Re-check everything independently and keep the receipts
fln check-olean . --receipts

# 5. Open the editor (vscode-lean4, unmodified) or the terminal InfoView
fln goals MyProject/Main.lean:37

# 6. Let your agents at it
fln serve-mcp --listen 127.0.0.1:8931
```

## Performance

Numbers below are the provisional CI **gates** (§19 of the plan) — the targets the design is built to hit, each ratified or amended against the measured Reference baseline published in W1 before any gate number is finalized. Every ratio is same-machine, same-thread-count, cache states declared; every published figure carries its claim state (`OBSERVED` on a named corpus and machine, or it is `TARGETED` — the README can never say "2× faster than Lean" off one warm-cache kernel loop, and documentation CI enforces that).

| Gate | Requirement |
|---|---|
| PG-1 · The Judge | Kernel-recheck of the full mathlib olean set: ≤ 5 min on the 32-core profile; ≤ 25 min single-thread |
| PG-2 · Cold Corpus | Full mathlib elaboration wall-clock ≤ 0.5× Reference at G4, ≤ 0.35× at G6 |
| PG-3 · The Cone | Leaf-edit incremental rebuild = true-cone only; representative leaf edits p50 ≤ 15 s, p95 ≤ 90 s from a warm Ledger |
| PG-4 · Attach | Daemon warm attach of a mathlib file ≤ 2 s p50; cold first-attach ≤ 1.2× Reference worker import |
| PG-5 · Determinism | Bit-identical environments/diagnostics/artifacts across {1, 8, 32} threads per commit — Prelude-scope today, corpus-scale matrix unbuilt (`franken_lean-2ki4`); {96}+ weekly; certified matrix under `--reproducible` |
| PG-6 · Memory | Daemon steady RSS serving ≥ 8 open mathlib files ≤ 1.3× one Reference worker; zero leaks over a 4 h soak |
| PG-7 · Golem | Interpreter ≥ 3× Reference interpreter on the tactic micro-corpus; Iron-JIT ≥ 0.5× Reference-precompiled |
| PG-8 · Codec | olean read ≥ Reference load throughput; write round-trip bit-stable at 100% of the Corpus set |
| PG-9 · Verdict | `bv_decide` corpus: 100% agreement; wall ≤ 2× Reference-with-CaDiCaL at G5, ratcheting |
| PG-K · Bignum | Kernel-reduction operation mix ≤ 1.15× the GMP-backed Reference kernel |
| PG-10 · Cache | Corpus CAS hydration ≥ 2× `lake exe cache get` on the lossy-path fixture (atp), ≥ 1× clean path |
| PG-L · Latency | Edit-ack + stale-cancel ≤ 25 ms p95; syntax diagnostics ≤ 60 ms p95; verified first-goal after a mid-proof edit ≤ 100 ms p50 |
| PG-1b · Consensus tax | Checker sampling ≤ 3% end-to-end overhead; full-closure release checking ≤ 10%; receipts ≤ 1 ms/decl amortized |
| PG-M · The Mirror | The metaprogram corpus (real ecosystem tactic code) ≤ 1.25× Reference wall at G4, ≤ 0.9× at G6 |

Every gate has a bench binary, a committed baseline, a variance budget, and a flame artifact on regression; regressions gate on tails as well as medians.

## Determinism, trust & verification

- **The Tribunal.** The Reference runs *inside the harness* as the standing differential oracle: upstream's own test suite imported at the pin, differential elaboration over all of mathlib, an instrumented-oracle fixture mine (golden traces of unifier/instance/macro decisions at Corpus scale, which the native engines are implemented *against*), codec round-trips, the ABI cross-load matrix both directions, recorded-session protocol rigs, mutation campaigns, fault drills, fuzzing, and metamorphic laws — all feeding a row-per-symbol Parity Ledger with per-row evidence levels.
- **Consensus with receipts.** Two kernel engines cross-checked continuously, an independent checker on its own decoder, and foreign witnesses (lean4checker, lean4lean-class checkers via the export format) as optional council members. Disagreement between any two engines blocks publication with both traces attached; there is no quorum that can vote a wrong judgment through. Attested receipts append to a Merkle transparency log — "checked" stops being a verb someone had to witness and becomes an artifact anyone can audit.
- **The WASM Judge.** The certified engine compiled to a single WASM artifact: sealed-capsule verification in a browser tab, no filesystem, no network, no platform libm — the strongest possible demonstration that the trusted core needs nothing from a host.
- **Determinism closure.** `--reproducible` builds are bit-identical across the certified platform matrix from the content-hashed input closure; release binaries are built twice in isolated builders and compared; the stdlib closes a double-elaboration fixpoint — the native-world descendant of the classic triple bootstrap.
- **Capability-scoped metaprogramming.** Tactics, macros, plugins, and build scripts run under typed authority and budgets; a `--pure-elab` audit mode denies ambient filesystem/network/clock and reports exactly which declarations demanded them. "This tactic phoned home" becomes structurally impossible to miss.

## Limitations

A few honest boundaries:

- **The type theory is immutable, forever.** FrankenLean proves the *same theorems* under the *same axioms* (`propext`, `Quot.sound`, `Classical.choice`) with the same kernel judgments, or it is not Lean. Language design is out of scope for 1.0; anything new lives behind `frontier` mode and never leaks into `faithful`/`sound` artifacts.
- **Compatibility is staged by evidence, not asserted.** 1.0 means **R4 (drop-in epoch replacement)** for the pinned epoch on the declared platform matrix. Until a surface's rows reach L4, its level is published — never rounded up. Track G0→G6 in §22 of the plan: G1 ships the Independent Judge before FrankenLean has elaborated a single file; G4 is full-mathlib elaboration; G6 is the sovereign toolchain.
- **The epoch lags upstream deliberately.** Lean releases monthly; FrankenLean advances its pin by a mechanical ratchet (regenerate censuses, diff surfaces, close every divergence) with the lag publicly visible. Target: a new stable release reaches R3 within four weeks, R4 the following cycle. Latest-nightly parity is never implied.
- **`native_decide` still names a trust surface.** Supported with upstream's semantics and its caveat stated louder; provenance marks every dependent theorem, and the staged repair (replay receipts → trace-guided kernel replay → verified evaluator) is tiered honestly, with each build's tier recorded in the trust ledger.
- **Outbound ABI is the harder direction.** Reference-built plugins load into FrankenLean at G2; FrankenLean-built plugins loading into the Reference is staged to G5, per-platform, in the Parity Ledger.
- **Windows bit-certification is a separate declared decision.** Windows is functional from W1; joining the certified `--reproducible` matrix is its own gate.

## FAQ

**Is this production-ready today?** The README describes the 1.0 target state (see the note at the top). Track the convergence gates in [§22 of the plan](./COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md): G0 "The Laws of the Machine" (ten de-risking spikes), G1 "The Independent Judge", G2 "The Golem Wakes", G3 "The Mirror Holds", G4 "The Corpus Whole", G5 "The Daemon", G6 "Sovereign & Beyond".

**Why reimplement the whole toolchain instead of just writing a better kernel checker?** Kernel checkers exist (lean4lean, lean4checker, nanoda) and none of them moves the ecosystem's actual bottlenecks: the build treadmill, the per-worker import tax, schedule-dependent elaboration, the interpreter tax, the bootstrap. Those are *toolchain* problems. The kernel-only path also can't run a single mathlib tactic. FrankenLean ships the independent checker *first* (G1) — and then keeps going.

**How can mathlib's tactics run unmodified if you didn't port the elaborator's Lean sources?** The Native Mirror (Bet B2). The builtin surface is mechanically partitioned by a census: toolchain-API symbols (`Lean.Meta.whnf`, `synthInstance`, the tactic framework…) are native Rust registered under upstream names behind a generated façade; pure library code (`List.map`, lemmas) is upstream *source* elaborated by our own toolchain; user metaprograms run on Golem against that surface. When a mathlib tactic calls `Lean.Meta.whnf`, it executes our unifier — and the Tribunal's metaprogram-corpus rig proves, nightly, that it cannot tell.

**Why should I trust a brand-new kernel?** You shouldn't — you should check it, and FrankenLean is built to make that cheap. The kernel is ≤ 12 KLOC of forbid-unsafe Rust written against a rule-by-rule judgment specification anchored to Reference source lines; two in-house engines cross-check continuously; an independent checker with its own decoder joins every attested run; foreign checkers join via the export format; and every declaration can ship a certificate a simpler verifier replays. Two implementations agreeing is evidence; two *foreign* implementations agreeing is the strongest evidence this ecosystem can currently buy.

**Does building or running it require Lean to be installed?** No. `cargo build` from a cold checkout produces the whole toolchain; there is no stage0 and no bootstrap. The pinned Reference exists only inside the conformance apparatus as the differential oracle, and a release-CI check proves shipped binaries contain no path by which it could be located, spawned, or linked.

**What happens when Lean releases a new version?** The epoch ratchet (§22.5): fetch and hash the release, regenerate every extracted census, machine-diff the surfaces, mine new behavior into fixtures, close or classify every divergence (unclassified blocks the claim), then move the pin. Epoch toolchains install side by side and are selected by `lean-toolchain` exactly as users expect. The Ledger's epoch bridges keep provably-unaffected cache entries alive across bumps, so the monthly migration stops meaning "rebuild the world."

**Is `sound` mode really the same language?** Same grammar, same elaboration semantics, same accept/reject verdicts, same kernel — the divergences are things like "diagnostics are richer", "builds skip work upstream repeats", and "parallelism cannot change your results", each one a numbered Behavior Note with migration guidance. When you need bug-for-bug observational parity (CI farms, migration audits), `faithful` mode replicates the pin down to heartbeat-timeout behavior.

**What's in it for AI/agent workflows?** The things the 2026 proof-search literature keeps paying for: no ~60 s import per search branch (one daemon, shared heap), O(1) proof-state forks instead of 18–735 s re-elaboration, structured goals instead of scraped pretty-printing, budgeted MCP tools with receipts, semantic premise search over the live environment, and deterministic replay of anything. The prover as an agent-legible service, not a process to be screen-scraped.

## About Contributions

Please don't take this the wrong way, but I do not accept outside contributions for any of my projects. I simply don't have the mental bandwidth to review anything, and it's my name on the thing, so I'm responsible for any problems it causes; thus, the risk-reward is highly asymmetric from my perspective. I'd also have to worry about other "stakeholders," which seems unwise for tools I mostly make for myself for free. Feel free to submit issues, and even PRs if you want to illustrate a proposed fix, but know I won't merge them directly. Instead, I'll have Claude or Codex review submissions via `gh` and independently decide whether and how to address them. Bug reports in particular are welcome. Sorry if this offends, but I want to avoid wasted time and hurt feelings. I understand this isn't in sync with the prevailing open-source ethos that seeks community contributions, but it's the only way I can move at this velocity and keep my sanity.

## License

The `franken_lean` source code is licensed under the **MIT License with an OpenAI/Anthropic Rider**, Copyright (c) 2026 Jeffrey Emanuel (see [`LICENSE`](./LICENSE)). The rider withholds all rights from OpenAI, Anthropic, their affiliates, and anyone acting on their behalf, including any use of the software or derivative works in a machine-learning dataset, training corpus, evaluation harness, or pipeline. In any conflict between the rider and the rest of the license, the rider controls. (Vendored upstream Lean sources under `vendor/` remain under their own Apache-2.0 license with NOTICE files carried, per Rule D5 of the plan.)

## See also

- [`COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md`](./COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md), the master plan: the eight bets, the Reference anatomy and weakness census, the foundation audit, the dependency & safety doctrine, the four-surface/three-mode product contract, the Native Mirror, every subsystem (Marrow, Grimoire, Crucible, Vellum, Athanor/Synod, Golem, Anvil/Verdict, Ledger, Lantern, Palimpsest, Bloodhound, Folio, Envoy, the WASM Judge), the Tribunal, the performance gates, the workstreams and convergence gates, the risk register, and the normative appendices.
- [`AGENTS.md`](./AGENTS.md), conventions for human and AI agents working in this codebase, including the engineering doctrine and the testing policy.
