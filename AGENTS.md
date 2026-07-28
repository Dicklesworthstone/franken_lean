# AGENTS.md — franken_lean

> Guidelines for AI coding agents working in this Rust codebase.

---

## RULE 0 — THE FUNDAMENTAL OVERRIDE PREROGATIVE

If I tell you to do something, even if it goes against what follows below, YOU MUST LISTEN TO ME. I AM IN CHARGE, NOT YOU.

---

## RULE NUMBER 1: NO FILE DELETION

**YOU ARE NEVER ALLOWED TO DELETE A FILE WITHOUT EXPRESS PERMISSION.** Even a new file that you yourself created, such as a test code file. You have a horrible track record of deleting critically important files or otherwise throwing away tons of expensive work. As a result, you have permanently lost any and all rights to determine that a file or folder should be deleted.

**YOU MUST ALWAYS ASK AND RECEIVE CLEAR, WRITTEN PERMISSION BEFORE EVER DELETING A FILE OR FOLDER OF ANY KIND.**

---

## Irreversible Git & Filesystem Actions — DO NOT EVER BREAK GLASS

1. **Absolutely forbidden commands:** `git reset --hard`, `git clean -fd`, `rm -rf`, or any command that can delete or overwrite code/data must never be run unless the user explicitly provides the exact command and states, in the same message, that they understand and want the irreversible consequences.
2. **No guessing:** If there is any uncertainty about what a command might delete or overwrite, stop immediately and ask the user for specific approval. "I think it's safe" is never acceptable.
3. **Safer alternatives first:** When cleanup or rollbacks are needed, request permission to use non-destructive options (`git status`, `git diff`, `git stash`, copying to backups) before ever considering a destructive command.
4. **Mandatory explicit plan:** Even after explicit user authorization, restate the command verbatim, list exactly what will be affected, and wait for a confirmation that your understanding is correct. Only then may you execute it.
5. **Document the confirmation:** When running any approved destructive command, record (in the session notes / final response) the exact user text that authorized it, the command actually run, and the execution time.

---

## Branch Policy

- Primary branch is `main`.
- Do not reference `master` in docs/scripts.
- If release instructions require sync, push `main:master` after `main`.

---

## Project Mission

`franken_lean` (**FrankenLean**, crate prefix `fln-`) is a **ground-up, native-Rust reimplementation of the entire Lean 4 toolchain** — parser, macro engine, elaborator, unifier, instance engine, tactic framework, simp and the decision procedures, trusted kernel, compiler, VM, runtime/ABI twin, module codec, build system, and language server — that is a **drop-in replacement at the binary surfaces**: the source language, the `.olean` object format (read *and* write), the `lean_object` C ABI (`lean.h` twin), the LSP wire protocol with the `$/lean/*` extensions, and the `lean`/`leanc`/`lake` CLI surfaces. Under those familiar surfaces it is deliberately better where better is sound: deterministic under parallelism, declaration-granular incremental, memory-shared, provenance-transparent.

**The Oracle-Only Law (D8) is constitutional:** no upstream implementation code ever executes as a component of FrankenLean — not the C++ kernel, not the self-hosted `Lean.*` elaborator sources, not stage0. The Reference toolchain (`leanprover/lean4` at the pinned epoch tag) appears in exactly one place: inside the **Tribunal**, as the differential oracle, fixture generator, and census-extraction source. The only Lean code FrankenLean ever *executes* is user code (mathlib's tactics, downstream libraries, lakefiles, `#eval`) on our own VM (Golem) against a natively-implemented `Lean.*` surface (the Native Mirror).

The leapfrog is not one trick; it is the *composition* of eight bets, each at or beyond the current frontier, made feasible only because the foundation libraries already exist:

- **B1 — The Ledger.** The environment is a Merkle DAG of content-addressed declarations; builds are memoized queries over it; a one-line leaf edit re-elaborates its true dependency cone (seconds), not its file cone (hours); the cloud cache is native CAS sync over atp.
- **B2 — The Native Mirror.** The entire `Lean.*`/`Init`/`Std` builtin surface is served *natively*: toolchain-API symbols are Rust implementations registered under upstream names behind a census-generated façade; pure library code is upstream-authored *source* elaborated by our own toolchain; user metaprograms run on our VM and cannot tell.
- **B3 — Kernel with receipts.** A ≤ 12 KLOC dual-engine trusted checker (certified small-step + NbE accelerator, cross-checked), deterministic fuel parity, proof-certificate export by default, consensus receipts with an independent in-repo checker plus external witnesses — disagreement halts, never outvotes.
- **B4 — Deterministic parallel elaboration.** Declaration-granular dataflow parallelism with speculative execution and deterministic merge: results are schedule-independent by construction (FL-INV-01), tested at {1, 8, 32} threads on every commit — **today that per-commit matrix's input is the Prelude**; the corpus-scale matrix now exists but runs on demand, so corpus schedule-independence is one recorded observation, not a measured invariant (bead `fln-corpus-thread-matrix-93te`).
- **B5 — Rewriting at machine speed.** simp-compatible rewriting on compiled discrimination automata shipped as per-library indexes, an e-graph saturation lane with kernel-checked proof extraction, and owned decision procedures (Verdict CDCL) replacing the external-solver TCB.
- **B6 — Agent-native by construction.** MCP surface (fastmcp_rust), semantic library search (frankensearch), structured proof states, O(1) proof-state snapshots for search trees, replayable elaboration traces.
- **B7 — The causal proof graph.** Every declaration, instance selection, simp firing, macro expansion, and kernel verdict is a node in a typed provenance graph with completeness classes; impact cones, semantic blame, semantic diff, and conflict-aware semantic merge become queries.
- **B8 — Evidence-native engineering.** Every public claim is a row in a machine-checked claim matrix (OBSERVED/TARGETED/HYPOTHESIS/PROVEN/BLOCKED); documentation CI rejects wording stronger than the matrix permits; compatibility is reported per-surface at evidence levels L0–L4 and per-release at R0–R5, never as one percentage.

**The single source of truth for what we are building and why is [`COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md`](COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md).** Read it before writing any subsystem.

### What we stand on (the closed dependency universe)

- `/dp/asupersync` — the operating system: structured-concurrency runtime (regions, obligations, `Cx` capability contexts, three-lane scheduler), the **lab runtime** (virtual time, DPOR, chaos, crashpacks), RaptorQ, the full networking stack, macaroons, region heaps. Elaboration of one declaration *is* a region; FrankenLean is a prover written in the asupersync programming model.
- `/dp/frankensqlite` — the durable store, linked directly as an embedded database: the Ledger's CAS metadata, the build-event journal, the Tribunal's evidence store, Bloodhound's index shards, Palimpsest's trace archives.
- `/dp/franken_networkx` — the graph brain (dependency DAGs, dominators for invalidation cones, SCCs for mutual blocks) and the **CGSE determinism doctrine** (registered tie-break policies, witness ledgers), generalized here to elaboration itself.
- `/dp/frankensearch` — two-tier hybrid lexical+semantic search powering Bloodhound (library search, premise retrieval, the MCP `search_lemmas` tool). Bundled embedder; no network, no Python.
- `/dp/frankentui` — build progress, the terminal InfoView (`fln goals`), Tribunal dashboards.
- `/dp/franken_markdown` (+ `fmd-font`, `fmd-math`) — Folio's document plane: native HTML/PDF docs with native TeX-math layout.
- `/dp/fastmcp_rust` — Envoy's MCP server framework.
- `/dp/atp` — fountain-coded CAS cache federation for the Ledger.
- Optional tier, feature-gated, never on the critical path: `frankentorch` (learned ranking), `franken_node` (widget JS host).

**The Reference** (`leanprover/lean4` at the pinned tag in `SUITE.lock`) and **the Corpus** (`mathlib4` at the compatible commit) are oracle and specification, never runtime components.

---

## Product Shape

The project must be all three at once:
1. A **toolchain**: `lean`, `leanc`, `lake` drop-in binaries plus the `fln` multiplexer with the new verbs (`check-olean`, `audit`, `replay`, `doctor`, `cache`, `olean`, `goals`, `serve-mcp`, `why-trusts`, `diff`, `build explain`, `verify-capsule`). elan-compatible layout so a `lean-toolchain` line can name a FrankenLean toolchain.
2. An **embeddable Rust library** (`fln`): parse/elaborate/check/query with the same engine and guarantees; capability-first API (the embedder hands the engine a `Cx`).
3. An **MCP server** (Envoy): goal inspection, tactic application against O(1) forked snapshots, premise search, budgeted `#eval`, certificate retrieval, Ledger and trace queries.

One type theory, one kernel, always — the same theorems under the same axioms (`propext`, `Quot.sound`, `Classical.choice`). Three modes govern everything around it: **`faithful`** (bug-for-bug observational parity with the pin, including fuel parity), **`sound`** (default: same accept/reject verdicts, documented improvements, every divergence a Behavior Note), **`frontier`** (olean-next, e-graph lanes, Iron-JIT, MCP write-tools — never leaking into faithful/sound artifacts).

---

## Spec-First Workflow

Implementation follows the plan, not ad-hoc invention. Read in this order:
1. [`COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md`](COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md) — the Reference anatomy (§1), the doctrine (§3), the product contract and Native Mirror partition (§4), every subsystem (Marrow, Grimoire, Crucible, Vellum, Athanor/Synod, Golem, Anvil/Verdict, Ledger, Lantern, Palimpsest, the leapfrog surfaces), the Tribunal (§18), the performance gates (§19), the crate map (§21), the workstreams and gates (§22), the risk register (§23), and the normative appendices (kernel judgment inventory, ABI/olean extraction law, builtin census method).
2. **The invariants (Rule D7)** — FL-INV-01 (schedule independence) … FL-INV-07 (inconclusive-is-not-rejected), each with its claim type and enforcement mechanism. No subsystem ships against an unenforced invariant.
3. **The generated contracts** — `ABI_CONTRACT.md`, `OLEAN_CONTRACT.md`, and the builtin census are *extracted mechanically from the pin* with checked-in scripts (D5/D9); layout constants are never hand-copied. If your work touches the ABI, olean codec, or a `Lean.*` façade row, regenerate and diff the contract first.

**Hard rule: no gate passes with a load-bearing unknown unresolved.** G0's ten spikes (§22.1) exist so that no later workstream freezes an interface on top of an unpriced bet.

---

## The FrankenLean Engineering Doctrine (READ THIS BEFORE WRITING CODE)

These are the constitutional, non-negotiable rules from §3 of the plan. Violating any of them is a revert.

1. **The dependency universe is closed (D1).** Allowed: `std`, the pinned Rust nightly, and the Dicklesworthstone-owned FrankenSuite (asupersync, frankensqlite, franken_networkx, frankensearch, frankentui, franken_markdown, fastmcp_rust, atp). The complete transitive closure is pinned, allowlisted, and audited. **No serde, no tokio, no rocksdb, no LLVM, no cranelift, no gmp-sys, no external SAT solver. Ever.** What §21.2 does not list as built-in-house is not in the program.

2. **Two inherited external tools, both optional (D2).** A system C compiler *only* for `--backend c` (as upstream `leanc`), system `git` *only* for Lake-compatible dependency fetching (as upstream Lake) — both under the full subprocess protocol, both absent from `--reproducible` artifact sets. Nothing else is ever spawned: no cc at check time, no CaDiCaL, no curl, no LaTeX. The Reference toolchain is *not* a third tool.

3. **The unsafe posture (D3).** `#![forbid(unsafe_code)]` in every authoritative crate. Project-authored `unsafe` exists only in three named boundary crates — `fln-unsafe-abi`, `fln-unsafe-region`, `fln-unsafe-jit` — with `deny(unsafe_code)` at the root and narrowly scoped, ledgered `allow` sites. `fln-kernel` is `forbid(unsafe_code)`: the TCB contains zero project-authored unsafe. Two structural laws: no `fln-unsafe-*` crate may depend on `fln-kernel`/`fln-checker`, and no unsafe crate exports any function whose return type can be laundered into a checked declaration.

**CI walks the first mechanically; the second is *part walked, part declared-and-reviewed*, and this sentence has now been wrong in both directions** (bead `fln-boundary-api-no-admission-argument-discarded-ez07`, audited at `c7a23f02`, repaired in the same commit as this sentence). It first claimed CI walked both, which was false; the correction said the export law was walked *nowhere*, which is no longer true. The **dependency** law is real and *derived*: the edge set comes from the actual `Cargo.toml` files (`checks.rs:1842`), `FLN-STRUCT-008` (`checks.rs:1999`) walks it transitively for every crate matching the `fln-unsafe-*` **pattern** — so a new boundary crate is covered without editing the rule, and a laundering path whose every hop is rank-legal still fails (`seeded.rs:253` plants exactly that, since `fln-unsafe-jit` is rank 12 and `fln-kernel` rank 6, so layering alone would permit it) — and `FLN-STRUCT-024` (`checks.rs:1591`) pins the prohibition itself, so deleting the line fails too. It runs under plain `cargo test` (`real_workspace.rs:51`, not `#[ignore]`d), not only in a lane.

The **export** law is weaker than it reads. What CI enforces is an *inventory*: every bare-`pub` item needs a reviewed `ci/BOUNDARY_API.txt` row, and undeclared items, stale rows, unclassifiable shapes, macro-synthesised exports and stray `export_name`/`no_mangle` sites all fail. **Launderability itself is nowhere expressed in code.** The row grammar's last three fields — surface type, evidence, and the argument for why the item cannot launder into kernel admission — are checked non-empty (`boundary_api.rs:109`) and then **discarded**: `ApiRow` (`boundary_api.rs:16-26` (historical)) kept only `id`, `path`, `kind`, `name`. The file's own doc-comment calls it "the no-admission export covenant's type-aware half" and the parser retains no type. Of the 66 rows at `c7a23f02`, 31 argue from the discarded surface type, 24 describe behaviour without arguing admission at all, and 14 of the 15 rows returning an opaque handle rest entirely on one row plus a **comment** at `BOUNDARY_API.txt:13` that is stripped before parsing.

**Two of those holes are now closed, and naming which two is the whole point**. Field 4 is retained and compared against the item's real signature, so a row can no longer declare `() -> bool` for a function returning something else — that is the **rot** hole, and it is what makes the 31 type-level arguments falsifiable rather than merely present. Separately, a `pub fn` in a boundary crate whose return type names a **caller-chosen type parameter** is refused outright, row or no row, because no reviewed row can argue that away: the caller instantiates it at a checked declaration and receives one. Both fire under plain `cargo test` (`seeded.rs`, tests `boundary_api_surface_type_is_bound_to_the_signature` and `a_caller_chosen_return_type_is_refused_even_with_a_reviewed_row`); five mutants were planted against the second and each dies at a **different** cell, including one that reddens the *green* control.

**Those cells are a fixture, and a fixture is not the production path** — the `TempWs` builds its own crate tree and its own `ci/BOUNDARY_API.txt`, so passing them proves the check *fires*, not that the real workspace refuses anything. Re-measured at `ad2b9207` (recorded in `bead-comment:fln-boundary-api-no-admission-argument-discarded-ez07:1378`, landed at `8a93993b`) with the real `structure-guard` binary at `--root`, exit code read from the process and not through a pipe, scoring only findings absent from the run's own baseline — which at that commit was one foreign `FLN-STRUCT-005`, `aa452b85`'s unacknowledged `fln-verdict -> fln-hash` edge. A laundering export planted in the real `crates/fln-unsafe-abi/src/lib.rs` with a **truthful** row in the real `ci/BOUNDARY_API.txt` is **refused**; a generic `fn` with a concrete return stays **clean**, so the rule is not a blanket ban on generics; and against a binary built from that same HEAD with **only** the laundering block deleted — one variable, not a checkout of `773cc9c5^`, which would also move `boundary_api.rs` and `ledger.rs` — the same export passes **clean**. That third cell is the one that matters: without it the repair would rest on a check that demonstrably fires and no evidence anything was ever open. **What runs per commit is the *check*, over the real root, via `real_workspace_is_structurally_clean`; the *plant* does not.** Nothing would notice if the production path stopped refusing while the fixture cells kept passing — one measurement at one commit on one host, class `bounded_model`, and item 7's shape exactly.

**The sentence this paragraph used to end with was wrong, and it is the fourth AGENTS.md claim measured false in two days.** It said "today it is the *dependency* law that actually carries it, since a boundary crate that cannot depend on the kernel cannot name a kernel type." True of laundering **by naming**, and exactly backwards for the sharpest case: `pub fn forge<T>() -> T` names no kernel type at all, so `FLN-STRUCT-008` permits it, the admission-token tripwire sees nothing, and the *caller* supplies the type. The one vector the dependency law cannot reach was the one the prose credited it with covering. Measured before the repair, with a truthful row so the inventory dimension passed: **zero findings**.

**What is still only reviewed, stated so nobody re-derives the old sentence.** Field 5 (evidence) and field 6 (the no-admission argument itself) are still checked non-empty and never read, for all 66 rows — a row whose argument reads `banana` still passes. Launderability is expressed in code for the generic-return vector *only*: an opaque handle, a raw pointer, a `repr`-compatible struct or a `From` impl elsewhere are all outside it. And nothing binds `BOUNDARY_API.txt` to `FLN-STRUCT-008`, so relaxing the prohibition still falsifies 15 rows without that file changing a byte. State law (b) as **partly walked**: the declared type can no longer lie, and a caller-chosen return can no longer be declared away — the argument resting on that type is still prose nobody checks.

4. **The Oracle-Only Law (D8).** The Reference participates in exactly three capacities: differential oracle inside the Tribunal; fixture/census mine via checked-in extraction scripts; and *source input* (`Init`/`Std` `.lean` files as data our toolchain elaborates). There is no "run the upstream definition instead" switch in any release binary; the development-only lockstep harness poisons everything it touches with `ORACLE_FALLBACK`, satisfies no gate, and is compiled out of releases — with a CI check proving its absence.

5. **The kernel answers to no one (D6, FL-INV-02).** `fln-kernel` is ≤ 12 KLOC, dependency-closure-on-one-page, exporting exactly one authority: `check : Environment × Declaration → Verdict`. Nothing else can admit a constant. Kernel disagreement with the Reference at the pin is release-blocking, with one carve-out: soundness beats bug-parity (D23). CI counts lines and walks the graph; growth requires amending the plan first.

6. **Determinism is a contract (FL-INV-01).** Same input closure ⇒ same environment, same diagnostics, same artifacts, at any thread count. Wherever an order is semantically free, a registered CGSE policy pins it. Every operation carries a determinism class (D0 mathematical … D4 external); cache keys, receipts, and the Parity Ledger carry the class.

7. **Engines are untrusted (FL-INV-06).** No Anvil engine's output enters an environment without a kernel-checked artifact. Certificates must be simpler than recomputation, reject unknown versions, and fall back to recomputation — an accelerator, never a wider TCB.

8. **Inconclusive is not rejected (FL-INV-07).** Resource exhaustion, cancellation, and internal faults yield typed `Inconclusive`/`InternalFault` outcomes, never rendered as, cached as, or promoted to acceptance *or* rejection. Panics are invariant failures, never user diagnostics; malformed source, artifacts, protocol messages, and plugin output must not panic.

9. **Claims have types (D7).** Every load-bearing statement is `invariant` | `proof` | `bounded_model` | `statistical` | `slo` | `benchmark`. A weaker class may never enforce or justify a stronger one. Headline percentages are never accepted as evidence; the Parity Ledger is row-per-symbol or it is marketing.

10. **Prohibited shortcuts (constitutional).** No "shell out to real `lean` temporarily"; no hosted C++ kernel; no `Lean.Elab` sources on our VM standing in for an elaborator we haven't written; no hand-transcribed ABI constants; no fallback that silently substitutes an external tool; no benchmark claim without corpus, machine, and claim state. Early code may implement a *subset* of a final abstraction — never a substitute for it.

11. **Correctness outranks speed, always.** The Tribunal and the differential rigs come first; performance work follows profile → remove one cost → re-verify determinism and fidelity → commit with evidence. A faster path that drifts a verdict, a diagnostic, or a byte of a faithful artifact is reverted, not landed.

---

## Code Editing Discipline

### No Script-Based Changes
**NEVER** run a script that mass-edits code files. Brittle regex transforms create more problems than they solve. Make code changes manually (use parallel subagents for many simple changes; do subtle/complex changes methodically yourself). The one sanctioned exception: the *checked-in extraction scripts* of Appendix B/C, which generate contracts and façade stubs into their designated generated-code homes.

### No File Proliferation
Revise existing files in place. **NEVER** create `elabV2.rs` / `kernel_improved.rs` / `unifier_enhanced.rs`. New files are reserved for genuinely new functionality; the bar is incredibly high.

---

## Backwards Compatibility

We are in early development with **no users**. Do things the **RIGHT** way with **NO TECH DEBT**. Never create compatibility shims or wrappers for deprecated *internal* APIs — just fix the code directly. (The externally-facing compatibility surfaces of §4.1 — source language, `.olean`, ABI, `.ilean`, Meta API, wire/CLI — are the opposite: they are the product, versioned per epoch, and never broken casually.)

---

## Toolchain

- Rust 2024 edition. Exact pinned nightly recorded in `SUITE.lock` (no "or later"); `rust-toolchain.toml` auto-selects it.
- `#![forbid(unsafe_code)]` at every ordinary crate root — and `forbid` can never be lowered, so `unsafe` lives **only** in the three named `fln-unsafe-*` boundary crates, whose roots use `#![deny(unsafe_code)]` plus narrowly scoped, ledgered `#[allow(unsafe_code)]` sites, each carrying a `// SAFETY:` note and a ledger row (path, invariant, evidence, safe fallback, no-claim boundary). CI rejects an unledgered site.
- Cargo only, with the cycle-free crate map of §21 (fln-core → fln-rt/fln-unsafe-abi → fln-env/fln-olean → fln-kernel/fln-checker → fln-parse/fln-syntax → fln-elab → fln-comp/fln-vm → fln-anvil/fln-verdict → fln-ledger/fln-lake → fln-server → fln-trace → surfaces → fln-conformance). Dependency edges point strictly downward; Palimpsest and Tribunal observe everything and control nothing.
- `SUITE.lock` governs the suite commits, the Reference pin, and the Corpus pin with one ceremony; CI builds only from the lock.

---

## Mandatory Checks After Substantive Changes

```bash
cargo fmt --check
cargo check --all-targets
cargo clippy --all-targets -- -D warnings
cargo test
ubs $(git diff --name-only)
```

If any check fails, fix root causes before handing off.

### The `cargo test` gate (green-bar requirement)

`cargo test` is a **hard gate**: it MUST exit `0` before any change is handed off or a bead is closed. When `scripts/check.sh` exists, it runs the four commands above in order and stops on the first failure; wire it as the CI test step rather than duplicating the commands.

Beyond the bare gate, **every Tribunal rig in §18 is a permanent CI obligation once it exists** — the Parity Ledger regression check, the differential elaboration tiers, the codec round-trips (FL-INV-04), the thread-matrix determinism runs (PG-5), the mutation campaigns, the fault drills, and the performance gates of §19.2. Gates add obligations and never retire them. A release may bypass a gate only with a public, expiring waiver.

### Where a green bar may be taken from — a linked worktree cannot host the evidence surface

The standing advice, correct and unchanged, is: when another pane's in-flight edit reddens the shared tree, verify in a **pinned git worktree at HEAD plus your patch** rather than waiting or touching their files. That is sound for **cargo suites at package or target scope** — `cargo test -p …`, `clippy`, `fmt`, individual test targets — and it is how the guard in `9a6f7941` was verified. Among the mandated four the one real exclusion is `cargo test --workspace`, which carries two environmental reds there; `ubs` works provided you `cd` into the tree holding the files first. Both are in the table, and neither goes anywhere near `run_git`.

**It is void for the evidence surface, and the failure does not say so.** `scripts/evidence.py`'s `run_git` `lstat`s `ROOT/.git` and refuses unless it is a real **directory** (it refuses a symlink too). In a linked worktree `.git` is a **file** holding a `gitdir:` pointer, so every trusted path reaching `run_git` refuses there. Measured at `115ef2fd`, each against a main-tree positive control (bead `franken_lean-worktree-gitdir-refusal-hugg`):

| runs in a linked worktree? | |
|---|---|
| `cargo test` / `clippy` / `fmt`, **one package or one target** | **yes, with one measured exception** — this is the sanctioned escape hatch and it is not unconditional. A suite whose **anti-vacuity floor requires generated output to be present** reds there for the environment rather than for your patch. Measured at `984a1555`: `--test evidence_finalization` is **31 ok / 1 red** in a fresh worktree, on `every_rust_side_launch_of_a_trusted_script_is_sealed`, whose floor demands that at least one path `.gitignore` declares as generated output exist on disk — and a fresh worktree has **none**: no `target/` (a per-pane `CARGO_TARGET_DIR` puts it outside the tree), no census, no `crashpacks`, `ledger-store`, `sim-traces`, `scripts/e2e/artifacts`. The guard is behaving **correctly**; it refuses a vacuous exclusion instead of reporting one, which is this file's own rule about empty scans. Confirmed by moving **one** variable: `mkdir sim-traces` in the worktree turns it green. So the affected class is not "tests that read the census" but *any* guard floored on generated output, and a fresh worktree is the emptiest tree there is. And note the trap in diagnosing it: a worktree and the main tree differ in `.git` **form** *and* in whatever orphaned WIP the main tree carries, so blaming the `.git` pointer without moving one thing at a time is this very table's recorded mistake, two rows down |
| `cargo test --workspace --no-fail-fast` | **two suites red** — all `structure-guard`, all depending on the four **untracked** census shards in `contracts/` (`builtin_environment.tsv`, `.001`, `.002`, `builtin_partition.tsv`; bead `fln-census-out-of-git-2ya9`): a fresh checkout has no copy, and the symlink shim people install to compensate is refused as `handoff_output_ambiguous`. **Two figures in this row were wrong; both re-measured at `9d86aac2`.** The size read **53 MB**, which is `builtin_environment.tsv` *alone* — the four shards are **242,966,844 bytes (231.7 MiB)**, so this understated the storage problem **4.4×** while the bead's own 231 MB was right all along. And the scope read `contracts/*.tsv` "untracked", which is **false**: that glob matches five files and `contracts/extern_census.tsv` (185,758 bytes) is **tracked**. A size transcribed from one member of a set, and a glob asserted to have a property one member lacks — `a025c3cb`'s lesson with a number in place of a line. Measured `7ebbddea`: **138 ok, 2 red** — `--lib`'s `contract_handoff_no_mock_e2e`, and `--test real_workspace`'s `real_workspace_is_structurally_clean` and `robot_real_workspace_binds_complete_authority_evidence` (bead `fln-census-empty-referent-no-mock-krb0`). **That tally no longer describes HEAD and has not been re-run:** `8278181a` made `contract_handoff_no_mock_e2e` take a typed skip on an absent shard rather than panicking, so it should no longer be among the reds; the two `real_workspace` tests still go red through `FLN-STRUCT-036`. Derived from the change, not re-measured in a worktree — treat the 138/2 as historical |
| `cargo test --workspace` **without** `--no-fail-fast` | **do not report a tally from it** — cargo stops at the first failing *target*. The same tree, same commit, reports "101 ok, 1 red": it hides 37 suites and the second failing suite entirely. A test name absent from that output means *did not run*, never *passed*. I published the 101/1 figure before re-running with the flag; this row is that correction |
| `ubs <paths>` — the fourth mandated check | **yes — `cd` into the tree first and pass RELATIVE paths.** `ubs` stages a shadow workspace rooted at **cwd** and cannot stage a path resolving outside it; the trigger is the argument, not the checkout. Measured as a 2×2 at `14638e4c`, same file, worktree `.git` a 59-byte pointer file: cwd=main+relative **0**, cwd=worktree+relative **0**, cwd=main+absolute-into-worktree **1**, cwd=worktree+absolute-into-main **1** (cc_3, reproduced by cc_2). A worktree `ubs` delta at a pinned commit is therefore still available, and is the cleanest attributable baseline while the shared tree is dirty. **But never compare counts across two trees**: a worktree at a clean commit and a main tree carrying WIP hold different bytes, so the gap reads as a tool inconsistency when it is a content difference (56 vs 34 on one file, measured 2026-07-26). Hold the path and the cwd fixed and vary **only** the content — `git show <sha>:<path> > <path>`, scan, restore — which is the same one-variable rule that this row's own first version broke |
| `evidence.py hash-tree --root R --path P` | yes, exit 0 |
| `evidence.py hash-tree … **--vendor-path V**` | **no** — exit 2 |
| `evidence.py ubs-inventory`, `evidence.py vendor-binding` | **no** — exit 2 |
| `scripts/check.sh`, the evidence self-test, `scripts/verify_vendor_tree.sh` | **no** — exit 2 |
| any `fln.e2e/2` lane — **8 declared fln.e2e/2 lanes**, of which **7 refuse on a measured invocation shape** and **1 whose verdict is unmeasured** | **no**, and this row's *scope* is now derived per commit rather than listed (`the_worktree_refusal_scope_is_derived_from_the_lane_population`), which is the half this table left open. The verdict survives measurement; the reason this row used to give does not. It said `hash-tree --vendor-path` is the first governed step of any such lane. Seven lanes do refuse, and the witness for all seven is `vendor-binding`, measured to refuse unconditionally. The eighth, `unsafe_note_clippy.sh`, carries no `--vendor-path` anywhere; it would reach `run_git`, if it does, through `emit --governed-path` / `--producer-binding-root` and `manifest --input-root` — six subcommands in shapes nobody has measured — so it is typed **indeterminate and named here**, not counted as refusing. Note also that the 21 scripts in `scripts/e2e/` and the 8 declared lanes are different sets. Static reachability cannot settle the eighth and is used only to prove a *negative*: 15 of the 42 subcommands reach `run_git`, yet `hash-tree` is one of them and exits 0 without `--vendor-path`, so a handler that never reaches it cannot refuse, while one that does may still succeed |

So the evidence surface runs in the **main tree only**. Two consequences worth stating separately, because each has already cost something:

1. **Every one of those failures blames something else.** `check.sh` says `cannot inventory UBS inputs`, so you go looking for `ubs`. `closure_audit.sh` says `cannot hash governed inputs`, so you go looking for a dirty tree. Seven lanes say `cannot verify the pinned Reference tree`, so you go looking for `vendor/`. The true line — `requires a real repository .git directory` — is printed once on stderr, *above* the lane's own louder and wrong summary. Nobody misread anything; the artifact asserts the wrong cause. **`run_git` now names the worktree condition itself, so this paragraph no longer does a job an error message should do** — landed at `cc9ecf0f` on 2026-07-26, verified in a real linked worktree rather than in a fixture at `e4219404`, and held per commit as of `cd3e203e`: the refusal reads `is a gitdir pointer, so this is a LINKED GIT WORKTREE`, while an absent `.git` still says something different. **What that does not retire is this row**, because the message repairs the *worktree* misdirection only: `structure-guard`'s `handoff_output_ambiguous` and `ubs`'s `Failed to prepare files workspace` still assert wrong causes, and the exit code still discriminates nothing — both failures exit 2. Doctrine a message could replace is doctrine that rots, so the half a message *did* replace is retired here and the half it did not is kept. **The sentence that stood here asked for a repair that had already landed the day before**, and it is the reason this correction is written as a correction rather than a deletion. The rows measured on 2026-07-26 sharpen this, one of them the hard way. `structure-guard` says `handoff_output_ambiguous`, which reads as a corrupt handoff; the cause is an untracked input. `ubs` says `Failed to prepare files workspace`, which reads as a broken scanner — and I published a row here blaming the worktree, because I compared a worktree path against a main-tree path **from the same cwd** and so varied two things at once. cc_3 ran the 2×2; the cause is cwd. **So the misdirection is not `run_git`'s defect**: a message naming neither candidate lets every reader supply whichever cause they arrived with, and a wrong one written down here travels faster than the measurement that corrects it — this one reached five panes before it was two hours old. Fixing `run_git`'s message, still the right repair, will shorten this section by one row rather than retire it. **Vary one thing per probe, and say which one.**
2. **Reachability is not execution.** Twelve `evidence.py` subcommands reach `run_git`; deriving the affected set from the call graph is wrong in both directions, because `hash-tree` is on that list and succeeds without `--vendor-path`. Measure the exit code with a main-tree control; never infer it, and never read it through a pipe (`… | tail` reports `tail`'s status).

If you have reported a bead verified against `check.sh`, the evidence self-test, or an e2e lane **from a worktree**, that claim is hollow — say so and re-verify in the main tree under `flock`, rather than carrying it.

#### The refusal is POLICY, not an implementation accident — decided here because a Python string is not where anyone looks

Everything above records *that* the evidence surface refuses a linked worktree. It never said whether that is deliberate, and a refusal nobody has decided on is one the next reader relaxes. This is `hugg` candidate 2, and the bead asked for a decision rather than a lean. **The decision: a linked worktree is not admissible to the trusted evidence surface, and the obvious way to admit one is the thing that makes it unsafe.**

It needed a measurement, because the refusal *looks* removable: `run_git` passes `--git-dir=<root>/.git` explicitly, so the question is only what git does with each `.git` shape under exactly that invocation. Five cells at `60b2e176`, git 2.54.0, each exit code read from the process, decision rule fixed before running:

| cell | `.git` at the root | measured |
|---|---|---|
| main tree — the control | a directory | exit 0, correct HEAD, 13,280 tracked paths |
| a real linked worktree, pointer file handed **straight** to `--git-dir` | `gitdir:` file | **exit 0 — git resolves the pointer itself**, the worktree's own HEAD, 13,280 paths |
| the same pointer resolved by hand first | a directory | exit 0, identical |
| **a root whose pointer names an unrelated repository** | `gitdir:` file | **exit 0, answering for the FOREIGN repository** — its HEAD, and `ls-files` returns a file existing only there |
| the same shape pointed back at this repository — the control that separates the row above from a broken probe | `gitdir:` file | exit 0, this repository |

**Two things follow, and the second is the decision.** First, the refusal is *not* a technical necessity: git accepts a gitdir pointer as `--git-dir` and resolves it, so relaxing the `lstat` would leave every trusted path working — which is exactly why this needed deciding rather than leaving to whoever next reads the check as vestigial. Second, **git discriminates nothing here**. A linked worktree and a foreign-repository indirection are the *same byte shape*: a regular file beginning `gitdir:`. So the relaxation the bead itself names — *resolve the gitdir pointer* — is precisely what makes the foreign cell succeed, and `run_git`'s `lstat` is the only thing standing between a governed evidence run and a silent attribution to a repository nobody named, at **exit 0**, carrying that repository's files. Admission is therefore strictly larger than deleting a check: it requires binding the resolved gitdir to *this* repository's identity, which is the half of candidate 2 that reads like garnish and is in fact the entire safety property.

A second and independent ground is already in the table above: a fresh worktree holds no generated output, so any suite floored on its presence reds there for the environment rather than for your patch. That one is about whether the evidence is honest; this one is about **which repository answered**.

**What this does not earn.** One host, one git version, one instant, class `bounded_model` — and `--git-dir` handling is a property of a tool outside this repository, so a version bump moves the first two rows silently. These cells measure **git**, not `run_git`: they establish what the check is holding back, never that the trusted path still refuses, which is the guard's job below. Nothing here shows admission *could not* be built safely — only that the named relaxation is unsafe alone. And no cell plants the foreign-pointer shape at the trusted surface itself: both landed probes use a pointer into *this* repository or a nonexistent one, so **the foreign-repository case is measured against git and is not yet held by any test** — named here rather than left for someone to discover, because that is the one direction where a future relaxation would fail silently.

`crates/fln-conformance/tests/evidence_finalization.rs::the_evidence_surface_refuses_a_gitdir_pointer_root` holds this table to the code: it builds a root whose `.git` is a file and asserts the real refusal, and it fails if this section stops naming the surfaces that refuse. Neither half can drift silently without the other failing.

#### The wrong **host** — an RCH green is about the worker's tree, and nothing in the command says so

Everything above is about taking a green from the wrong **tree**, which you at least choose. This is the wrong **host**, and it is the one shape nobody chooses: RCH's PreToolUse hook offloads a bare `cargo test`/`clippy`/`build` to a remote worker automatically, with nothing in the command saying so (bead `fln-yihl`; the classifier numbers are in the RCH section below).

**Measured by cc_1 on 2026-07-26 against worker hz2, and the first answer was wrong in the interesting direction.** A sentinel flipped mid-flight appeared in a job dispatched *before* the flip — which looks exactly like one job clobbering another's source. It is not: checking *when* each root synced refutes it, and a corrected protocol showed each job seeing exactly what it synced. **The clobber this bead is named for is not confirmed.** What did reproduce is sufficient on its own and changes the rule: RCH's default-mode sync is **not atomic**. One ordinary job's 34 roots were synced across a **22-second spread**, the full sequence took **~75 seconds** before execution began, and the remote path is the caller's own absolute path — `/data/projects/franken_lean`, the one directory all six panes work in. So a job does not compile a snapshot; it compiles whatever each root held when that root's turn came. A job was observed reporting **exit 0** over a mixture of two tree states that never existed locally at any single instant. You do not need a second RCH job to get a torn build — you need any pane to touch any file during your ~75-second window, which with six panes on one tree is the normal case.

The default mode also reports **no content digest**: `rch exec -j` emitted zero JSON objects across 246 lines, and the one hash it prints is a project/path identity, constant across runs and identical for every pane. So the caller cannot tell which tree state produced their result.

> **An RCH default-mode green is evidence about the worker's tree, not yours, and may never close a bead.** Treat a default-mode red as unattributed until reproduced locally, and a default-mode green as unattributed always.

**The attributable form exists, was tested in both directions, and fails typed rather than silently.** `rch exec --base "$(git rev-parse HEAD)" --clean-overlay --overlay-path <every path you changed> -- cargo test -p <crate>` ships a git baseline plus your named paths (`1 root`, not 34), computes a sha256 over the overlay at admission, re-checks it before execution, and on a mid-flight edit refuses naming **both** digests — then declines to fall back locally, so nobody is handed an unattributed green by accident. The control matters as much: with the tree left quiet the same invocation returns exit 0, so it admits a still tree and refuses a moving one. Two footguns, both new rather than inherited: pass an explicit sha, never the literal `HEAD`, which is a moving target between dispatches; and name **every** changed path, because one you forget is simply *absent* from the build, giving you a green for the baseline rather than for your work — derive the list from `git status --porcelain`. What this buys beyond attribution is that five other panes' uncommitted edits are excluded **by construction**.

**And the evidence surface refuses on a worker outright, for a fourth `.git` shape.** A worker checkout is synced without `.git` (bead `franken_lean-rch-clean-overlay-has-no-git-dir-46pw`), so `run_git` raises `requires an explicit repository .git directory` — a **different** sentence from the linked-worktree pointer above, and the distinction is load-bearing because a worker is not a worktree and a message that said so would send the reader hunting a checkout they are not in. Measured at `ef389785`, both the committed and the working-tree copy of `scripts/evidence.py` agreeing: absent `.git` exits **2**, and a real `.git` directory *also* exits 2 with no refusal, because there git runs and fails on its own terms. **The exit code discriminates nothing; only the message does.** `the_evidence_surface_refuses_a_worker_checkout_with_no_git_at_all` holds that shape to the code and this section to that rule, in both directions.

**What none of this earns.** RCH lives outside this repository, so no test here can hold its classifier, its sync behaviour or its version — those figures are `bounded_model`, measured at one host at one instant, and the `--clean-overlay` result is one pair of runs on one worker. The original symptom this bead was filed for — the remote holding content *older* than the caller's tree both before and after dispatch — is **not** explained by non-atomic sync, which produces mixtures rather than staleness; a cached root rsync did not refresh is the obvious candidate and remains untested. The bead stays open on its own terms.

---

## A block is a claim, and it expires — re-test it before you wait on it, and before you act on it

Everything above concerns a **green** taken from the wrong tree, the wrong host, or from a run that never happened. The mirror image is unwritten and has cost more: a **red** — a block, a refusal, a price — measured once and then carried by everyone who reads it afterwards. A block is a measurement of the world at an instant, so it decays exactly as a green does. It decays *invisibly*, though, because the run that would falsify it is the one run nobody has a reason to make: the usual reward for re-testing a block is learning that the block is still there.

> **Re-test a block before you wait on it, and before you act on it — and say what you tested.**

**Apply it to instructions and not only to your own reports, which is the half that costs.** On 2026-07-27 cc_1 was twice told to commit pending items, re-tested first, and twice found none — a peer's commit had already carried the work, and the second attempt printed `no changes added to commit`. Acting on the unverified premise would have produced a confusing empty commit against a state that had already lapsed. Verify the premise, then act, whoever handed it to you.

**The sharpest form is a cost cited as a reason to decline a measurement, because a decline leaves no artifact behind for anyone to check.** Recorded on bead `franken_lean-j8h`: a clean-checkout production run was declined on the ground that a separate `CARGO_TARGET_DIR` is "multi-GB against 63G free at 94 percent". Both halves were false and re-measuring cost one command. 94% is *used of a 906 G disk*; the scratch target directories that measurement needed run 13 M – 3.8 G, and the scoped ones — one package or one target, which is the shape it wanted — 116 M – 648 M, a worst case of about 6% of free space and a typical scoped one under 1%. **The abstention itself still stands; only its stated reason was false**, and that is exactly why the shape survives review: the decision reads as sound, so nobody re-derives the number underneath it. Note the free figure at each telling — 63 G when the reason was written, 60 G when `0f2ae0ba` corrected it, **58 G at `4e168918`** when this section was. A quantity that moves every session may never be cited from memory. **Never offer a percentage-used as scarcity; give the absolute cost of the thing you are declining against the absolute headroom, and re-measure both.**

**Re-measuring is necessary and it is not sufficient, because the quantity is BURSTY and one sample supports no projection in either direction.** The rule directly above says re-measure rather than cite from memory. Two people obeyed it on 2026-07-27 and still got the answer wrong, because they projected a *trend* from a *sample*. Both directions, same day, same host. Downward: a 30-second sample of a falling figure read about **1 G/hour** against a true rate nearer **60 G/hour**, and a headroom deadline was extrapolated from a four-minute delta that turned out to span one build's intermediates. Upward: free space went **21 G to 65 G in about a minute** when that build finished and released them. The decline being tracked was never a trend at all; it was the falling edge of a burst.

**The two instances that make this a rule rather than an anecdote are a false freeze and a declined measurement, and the second is the one already recorded in the paragraph above.** At 10:00Z a swarm-wide freeze was called on **1.7 G** free, which recovered unaided within **four minutes** — the freeze was false, and it stopped six panes. And `j8h`'s decline is this same shape one step earlier: a measurement refused on a stated cost that re-measuring falsified in one command. The magnitude gap is the part worth carrying: on a later run that same day the scratch root a perturbation measurement actually needed was **512 K**, against 64 G free.

**The instant of measurement cannot tell you which case you are in, and that is the whole finding.** At 16:44Z a shortage did **not** recover. Set beside 10:00Z's it is *indistinguishable*: same kind of number, same direction, same apparent urgency. Nothing about either sample separates them, because what separates them is the trend — and **a trend is not a property a sample has.**

> **A bursty resource figure supports no projection from one sample, in either direction. Take a second sample before you act, and a third before you tell anyone else.**

The escalation is deliberate: publishing a freeze to five other panes is a far larger action than pausing yourself, so it earns a higher bar. And a caution issued from one sample is a **block**, expiring exactly as every other block in this section does — one was issued and withdrawn inside twelve minutes on this same day, and withdrawing it cost one command.

**The direction this rule is really aimed at is the pessimistic one, which is the half that gets skipped.** Read casually it says *do not be over-optimistic about headroom* — the error nobody makes. Declining to spend a resource *feels* free, so that is the direction people actually err in, and it is not free: it froze a swarm for nothing, and in `j8h` it cost a measurement outright while leaving no artifact behind for anyone to check. **A pessimistic projection from one sample is as forbidden as an optimistic one.**

**What this does not earn.** Two instances at one host on one day, class `bounded_model`, and nothing mechanises any of it — no check samples anything or refuses a projection. Every rate and every absolute figure here is a property of *this* machine on *that* day and must never be carried forward; what is durable is the shape, never the numbers. It also gives no bound on how long a burst lasts, so "take a second sample" does not say how long to wait, and two samples that agree can still both sit inside one burst.

**A red attributed to a documented cause needs its CAUSE re-checked, not merely its existence — and the wrong cause is now supplied by this file rather than by a tool.** Measured at `f5359c22`: `structure-guard`'s `real_workspace_is_structurally_clean` and `robot_real_workspace_binds_complete_authority_evidence` were failing, which is exactly what the green-bar table above declares for those two names, through `FLN-STRUCT-036` and the untracked census shards. **The declared cause was not firing.** The run reported *exactly one* finding, and it was `FLN-STRUCT-011` — a missing crate-root `#![forbid(unsafe_code)]` in a test crate added four commits earlier, a live D3 violation reddening every pane's `cargo test`, sitting undetected inside a channel this document had pre-declared red. Nobody misread anything: a documented red is the cheapest available explanation for a red, and the reader arrives already holding it. So `hugg`'s lesson extends one step. There, the *artifact* asserts a wrong cause loudly; here the artifact says nothing wrong at all — the reader supplies the wrong cause from this file, and a matching test *name* confirms it. **When a test this document declares red fails, read the finding code before matching the name.** A red channel is a claim with an expiry exactly as a green one is, and the thing that expires is not whether it is red but *which defect is making it so*.

**What this does not earn.** It is a practice and not a mechanism: nothing here re-runs a block for you, and that gap is measured rather than assumed — `fln-ysvo` priced four candidate joins between a bead's mutable summary and the immutable comment log beneath it and found every one of them fails, because the predicate that matters is semantic while the lexical proxy is saturated at 87% by this project's own house style of writing corrections into comments. Whether a recorded block still holds is a predicate of that same kind. The instances above are `bounded_model`, one host and one commit each; what is durable in the disk figures is the range and the fraction of free space, never the three numbers.

---

## Testing Policy — the Tribunal (plan §18)

This is the second-largest subsystem in the program, not a QA appendix. The Reference runs *inside the harness*, as the differential oracle, forever. From cheapest to strongest:

- **Differential rigs.** Corpus files elaborated by both implementations, compared at tiers (T2: acceptance + diagnostics + statement-level environment identity; T3: term-level identity up to registered normalization). Kernel verdicts diffed against the Reference kernel, lean4checker, and lean4lean. Any pairwise disagreement is a finding; kernel divergence blocks release.
- **The instrumented oracle.** A build-time-only, test-only patched Reference dumps golden decision traces (unifier approximations, instance-search orders, macro expansions, simp firings, heartbeat consumption) at Corpus scale. Athanor, Synod, and Anvil are implemented *against these traces*, with trace-replay rigs running continuously.
- **The Mirror conformance rig.** The ecosystem's real tactic/metaprogram code executed on Golem against the native façade; environments, InfoTrees, diagnostics, and generated names diffed against the oracle's runs. Every façade row's L-level is earned here, nightly.
- **Codec rigs.** olean read/write byte round-trips (FL-INV-04), mixed-producer builds both directions, corrupted-input fuzzing under resource budgets.
- **The stage0 ABI gauntlet.** The Reference's own stage0-generated C compiled against Marrow's exports and run through the upstream runtime suite — if the membrane is wrong anywhere, upstream's own code says so.
- **Mutation campaigns.** Seeded defects (skipped positivity check, inverted universe condition, leaked transaction assignment, dropped retain, stale cache hit accepted) must each be *killed* by a named test; a surviving critical mutant blocks the gate.
- **Fault & recovery drills.** kill -9 at every CAS promotion step, corrupted caches, disk-full mid-build, plugin crashes — each with an expected final state; "the process restarted" is not a pass.
- **Metamorphic laws.** Comment/whitespace churn, independent-decl reordering, alpha-renaming must preserve environments and — for the Ledger — invalidate nothing.
- **Determinism closure.** Thread counts {1, 8, 32} per commit — over kernel-authored declarations everywhere (`fln-kernel`'s `thread_matrix_determinism`, no pin needed, bead `fln-q944`) and **over the Prelude wherever the pin is installed**, which is not every machine. The corpus differential itself still scores verdicts at one explicitly pinned width; the corpus-scale {1, 8, 32} comparison is a separate on-demand lane (`present_olean_corpus_thread_matrix_compares_stream_digests`), `#[ignore]`d for cost and typed-SKIP without the pin. It has been run at the pin (whole present-olean corpus, every per-module verdict stream and its exact consumption identical at 1, 8 and 32 threads) — corpus matrix observations recorded: 1, latest observed 2026-07-26 — which earns **one observation** at that corpus revision, pin and host — class `bounded_model`, not the invariant FL-INV-01 states. PG-5 asks for {1, 8, 32} **per commit**; an on-demand lane is a documented shortfall against that gate, not compliance with it (beads `fln-8zsq`, `fln-corpus-thread-matrix-93te`). **The PG-5 waiver, stated publicly because that is the only way a gate may be bypassed:** per-commit corpus width coverage is waived on the measured cost — one run is 1,926,656 ms (32.1 min) on a 64-way host, three quarters of it in the sequential column. **That is now the waiver's only reason, because the second one was false.** It read "and because CI installs no Reference toolchain, so the lane cannot execute there at all", and `.github/workflows/contract-drift.yml` disproves it — on a weekly `cron: "17 5 * * 1"` with a `timeout-minutes: 180` budget, that workflow installs pinned elan, parses the Reference tag out of `SUITE.lock`, and stands the pinned toolchain up. Measured at `8aa1a0ed` for bead `franken_lean-p6x1`. The sentence was true when written and was falsified by a workflow that landed later in the same repository, with nothing joining the two — this session's dominant defect, a claim whose producer was never re-checked, sitting in the passage that grants an exemption. **A waiver resting on a false premise is worse than one resting on a narrow premise**, because a reader cannot tell which of two stated reasons is load-bearing; here only the cost ever was. **What removing it does NOT establish, said in the direction against the finding:** a weekly 180-minute window is not per-commit coverage, so PG-5's shortfall may be *smaller* than this passage declared but is **not closed**, and nothing here measures it. The 32.1 min is a 64-way figure; a hosted runner is not one, so the lane's wall time there is **unmeasured** — three quarters of the run sitting in the sequential column is a reason it might fit, never evidence that it does — and the corpus must be present too. Whether the lane should take a dispatcher is a decision with an unmade measurement attached, not a conclusion of this correction. **That run is not a unilateral action: it needs the Reference pin and 32 minutes of a host every pane shares, so it is launched through whoever sequences the swarm, never off the back of a red.** Withdrawing the claim is the option that needs no permission, and it is why the red is never extortion. The standing evidence is the retained receipt at `crates/fln-conformance/evidence/corpus_thread_matrix/<pin>.jsonl`, which binds each run to the pin, the corpus revision and the host. **The waiver expires when the Reference pin moves**, and it expires *mechanically*: the receipt path is keyed by pin, so advancing `SUITE.lock` makes `the_corpus_matrix_observation_is_retained_and_bound_to_the_current_pin` fail with the re-run command, its measured cost, and the cheaper honest alternative of withdrawing the claim (bead `franken_lean-p6x1`). Bit-identical artifacts across the certified platform matrix under `--reproducible`; release binaries built twice in isolated builders and compared; the stdlib double-elaboration fixpoint.
- **Torture (asupersync lab).** The daemon and build fabric under virtual time with cancellation storms, fault injection, crash-recovery of the frankensqlite stores, seed-replay of every failure.
- **No-mock lanes.** Release-level claims close only against the real thing: real Reference binaries, real filesystems, real editor clients, real corruption. Mocked boundaries are fine for unit tests and rejected by the evidence gate.

---

## Agent Ergonomics Requirements

CLI robot surfaces must be: stable versioned schema, deterministic where possible, explicit exit codes, line-oriented output, easy to pipe. Do not mix human decoration with machine output. `--json` shapes are conformance surface (pinned to the Reference where the flag exists there; versioned under `--fln-*` where new). Robot responses from Envoy carry schema/epoch/profile versions, request and snapshot ids, resource facts, data grade (provisional/verified), and evidence links. Dogfood `fln doctor --sql`: the build database is the observability surface.

---

## Committing in a shared checkout — `git commit -o <paths>`, never the index

The live panes all work in the **same** checkout, so there is exactly one `.git/index` and `git add` writes to all of it. Staging is **shared mutable state between agents**, and the ordinary two-step `git add … && git commit` is a read-modify-write on it with no lock — and, more to the point, with no verification that survives the gap between the two commands. (Linked worktrees each hold their own index, which is the one dimension in which a worktree is *safer*; the green-bar table above governs every other dimension and mostly says no.)

**This file already carried the casualty and filed it under the wrong cause.** The projection-guard section below records four agents landing a stale projection on 2026-07-24/25, one of whom "had not touched beads at all: an incidental `git add` swept the JSONL into their commit." That is not a beads mistake, and reading it as one is why it kept happening. It is the index — and it is one event seen from one side only: the same `git add` swept that agent's own file into somebody else's commit.

**Measured at `7c950ac6`, git 2.54.0, six purpose-built real repositories, one variable per cell:**

| cell | measured |
|---|---|
| index-based commit; a peer stages between my verify and my commit | I verified my staged set was **exactly `[mine.txt]`**, and committed **`[mine.txt, peer.txt]`** |
| the identical race, but `git commit -o mine.txt` | commit is `[mine.txt]`; the peer's staging **survives** and their worktree is untouched |
| `-o` with nothing of mine staged at all | still commits the named path — `-o` reads the **worktree**, so staging is not a precondition for it |
| `-o` on a path whose index and worktree differ | the **worktree** version lands, and the index is updated to match — `-o` does not read a peer's staging of your path |
| `-o` with a directory pathspec (`-o sub/`) | commits every changed file beneath it; a peer's staged file outside it is untouched |

> **`git commit -o <paths>` only. Then `git show --stat HEAD` and read what actually landed.**

The first cell is [the block-expiry rule](#a-block-is-a-claim-and-it-expires--re-test-it-before-you-wait-on-it-and-before-you-act-on-it) one layer down, in the direction that section does not cover: a staged set is a measurement of **shared** state at an instant, true when you read it and false when you act on it. Verifying harder does not help, because no verification holds across the gap — which is why the repair is to stop depending on the index at all rather than to check it more carefully.

**The residual, and it is live in this tree right now.** `-o` bounds a commit to the paths you **name**; it does not establish that you **authored** them. The fifth cell: `-o` on a path a peer had edited and I had not commits *their* uncommitted work under my name. Not hypothetical here — two orphaned working-tree files stand at HEAD, and this is exactly why the `9teu` patch was ruled accepted-on-the-merits but **not landable** on 2026-07-27, since landing it meant committing 543 uncommitted lines of a dead pane's under the committer's own authorship. Derive your path list from what you changed (`git status --porcelain`), and name nothing you did not write.

**The second residual is the mirror of the first, and it is the one this section's own table already measured without anyone drawing it: `-o` does not establish that your copy is CURRENT.** Cells three and four say it plainly — `-o` reads the **worktree**, and the worktree version lands. So a file you generated or exported *before* a peer's commit landed is now **older** than `HEAD`, and naming it in `-o` writes your stale copy over their landed record. There is no conflict and no warning, because there is no merge: `-o` takes what is on disk. Measured on 2026-07-27 — between a `br sync --flush-only` and the `git commit -o .beads/issues.jsonl` that would have carried it, `b285aed0` landed one comment on a peer's own bead. The export predated the commit by minutes. Caught before it landed, so this row is a near miss rather than a casualty, and it is recorded at that strength.

**The two checks a careful pane already makes both pass while the revert is live, and one of them passes *because it is precise*.** [The projection guard's own section below](#the-projection-guard-bead-franken_lean-projection-republish-mechanical-voz4) states its scope — "status, comment and closure edits leave the projection valid and commit normally" — offered there as a virtue, and it is one; the predicate is stated once, there, and deliberately not restated here. The atomicity habit for beads asks about **status transitions**. A comment-only edit moves neither, so a clean answer from both is fully compatible with reverting a peer. Neither check is wrong; they answer different questions, and *whose record would I overwrite* is a third question nothing here asks.

This is [the block-expiry rule](#a-block-is-a-claim-and-it-expires--re-test-it-before-you-wait-on-it-and-before-you-act-on-it) in the direction that section reaches last: not a green, not a red, but an **artifact you produced** — a measurement of shared state at an instant, true when generated and false when committed. `HEAD` moved eight times in one hour on 2026-07-27 and twice under one pane inside a single task. So immediately before committing any generated or exported file — `.beads/issues.jsonl`, `ci/KERNEL_CONTRACT_OWNERSHIP.jsonl`, a census, a contract — re-read `git rev-parse HEAD` and diff your working copy against **that** `HEAD`, record by record, requiring the delta to be exactly your own additions:

> **Ask the question neither guard asks — *which records would I revert?* — and require the answer to be empty.**

When it is not, regenerate or re-export rather than reconciling by hand: the shared producer usually already holds the peer's write, which is why the near miss above resolved in one command. **What this does not earn:** it is a rule and not a mechanism, nothing runs it for you, and it is one near miss at one commit on one host, class `bounded_model`. It also says nothing about a peer's *uncommitted* work, which is the first residual's question, one paragraph up.

**The third residual is the one the instruction directly above creates, and it was measured against a pane while they were obeying it.** The second residual says your copy may be **stale**. This one says your **verification of that copy expires before the commit does** — and what lands may be *newer* than what you checked, carrying a peer's record you never inspected. The check prescribed above is right, and it does not **gate** anything: it prints an answer, and the commit is a separate command. Measured on 2026-07-27 at `23f80f44` — the record-by-record diff ran, printed its refusal, and the commit executed anyway, because the two sat in one shell block. What it had refused was real: a peer's `franken_lean-6tqy` had moved `open` to `in_progress` and gained a comment about a minute earlier, and that record landed under a commit message asserting that zero existing records had changed.

**The mechanism is the index race one layer over, and everything above covers the index half only.** `.beads/issues.jsonl` is a **shared file in a shared worktree**, and a peer's ordinary `br` command auto-flushes the tracker into *your* working copy without either of you deciding anything. `git commit -o` reads the worktree. So the window between verifying and committing is exactly as unsafe as staging is, for the same reason, with no `git add` anywhere in it — and unlike the index there is no second place to look afterwards that would say so. Note which direction was observed: the peer's write was carried **forward** and nothing was lost, which is the safe half. The reverting direction is not excluded by this measurement, merely unobserved in it.

> **Gate the commit on the check — `verify && commit`, never `verify; commit`. A verification that does not gate the action it verifies is decoration.**

**It caught a peer on its first real outing, which is the argument for it.** Hours after this rule landed, the gated form ran before a routine beads commit and refused: between the flush and the commit a peer had created a **new bead**, moving the id set and staling the ownership projection, and had regenerated that projection in the shared worktree mid-assembly of their own three-part commit. Committing would have carried their unfinished bead under another pane's name — and been refused by the coverage guard anyway, since it had no row yet. The ungated form prints that and commits regardless. Nothing was lost, and the only reason is that the check *gated*.

**What this does not earn.** Still a rule and not a mechanism: nothing runs the diff, and making it gate is a shell habit rather than a guard. One instance at one commit on one host, class `bounded_model`. It gives no bound on the window either — the observed gap was about a minute, which is one sample — and a peer's write landing between a gated check and git's own read of the worktree is narrowed by none of this.

**The gate can be defeated by SHELL PARSING while the chain still reads as correct, which is the sharpest form of the sentence directly above.** "A shell habit rather than a guard" understates it: the habit has a failure mode that looks exactly like compliance. Inlining a heredoc into the chain — `python3 - <<'PY' && \` followed by the script body — silently degrades `verify && commit` into `verify; commit`. The `&& \` continues the *command line*, so the first line of the intended heredoc body is parsed as shell and joins the `&&` chain instead; the heredoc then starts one line late, the script dies on its missing first statement, and the `git commit` after the closing delimiter is a **separate statement** that runs unconditionally. Measured on 2026-07-27: a beads delta-check died with `NameError`, its `import` line having been eaten, and the commit landed anyway. You will look at your own command, see the `&&`, and be wrong.

**Nothing was lost, and the reason is an audit rather than the gate** — `1dbf8095` against its parent is 406 records on both sides, 0 added, 0 removed, exactly one record changed and it is the committing pane's own bead, with no peer status transition riding along. The identical check had passed in the immediately preceding command at the same `HEAD`. That distinction is the whole point: an audit after the fact is not the gate doing its job, and it only exists because somebody went looking.

> **Put the gate in its own file and invoke it — `python3 -I -S <check-script> && git commit -o …`. Never write a `\` line-continuation between a heredoc's redirect and its body. Then audit what landed against its parent, because that audit is what separates a disclosed near miss from an undetected one.**

**The prohibition this blockquote first carried was broader than the measurement behind it, and it is corrected here by its own author — before anyone acted on it, and after it had already been broadcast to every pane.** It read "never inline a heredoc into an `&&` chain", which is a **wall against a correct practice**: this file's own recurring error shape, arriving in the repair for a defect about rules that fail when followed. Four cells at `2eb09ba6`, one variable each, **re-run in both shells at `08dbb11c` — bash 5.2.37 and zsh 5.9 agree on all four**, which closes the "bash was not tested" gap the first telling disclosed rather than leaving it to rot. A gate returning **false**, with `&& \` continuations and an inert-data body, ran **nothing** — exit 1, the gate held. The same with **true** emitted the body's first line intact and then the trailing command. `python3 - <<'PY' &&` with **no** continuation ran its program correctly, first line intact, *even though the body is a program*. Only `python3 - <<'PY' && \` followed by the body reproduced the defect.

So the trigger is neither the heredoc nor the `&&`: it is a **`\` continuation standing between the redirect and the body**. The shell reads the next physical line as command text, and the heredoc body therefore begins one line late. Two consequences that make it hard to read back. The eaten line is **executed** — `import sys` became ImageMagick's `import`, so the failure can surface as an unrelated tool's error about an X server rather than as anything resembling a gate problem. And the command following the heredoc terminator is then a **separate statement**: measured directly, the gate exited 1 and the trailing command still ran. The body being a program is what makes the damage *silent* rather than what causes it, since a program missing its first line usually fails in a way that reads like a genuine finding.

**The cross-shell run needed a control of its own, and the first attempt was contaminated by its own apparatus.** Wrapping each cell in `$( )` to capture its output made **bash** raise a *syntax error* on the two safe cells — which the verdict logic then scored as "gate held", a **false pass reached for the wrong reason**, produced by the harness rather than by the subject. Re-run unwrapped, bash and zsh agree on all four. A measuring apparatus that changes the answer is this file's own broken-scan rule arriving in the control instead of in the thing controlled, and the only reason it was caught is that the cell's *stderr* was read rather than just its verdict.

**The general rule this is really evidence for: when you write a rule down, write down how it FAILS WHEN FOLLOWED.** Three rules were defeated inside two hours on 2026-07-27 by the *mechanism* of applying them rather than by anyone forgetting them — argv-only holder classification, which fired on a foreign checkout's `scripts/check.sh` and froze a pane for twenty minutes on a repository nothing was holding; the routing-store listing, which finds only files whose *name* targets you, so a route addressed in its body is invisible to the prescribed command; and this chain. In all three the reader was following the rule as written, and in all three the failure was indistinguishable from compliance from the inside. A rule's failure modes are part of the rule. The ones worth writing down are not the ways it gets ignored — those are visible — but the ways it gets *obeyed* and still does nothing.

**The fourth residual is not about a peer at all — it is your own record appearing to be absent, and the producer that says so is telling the truth.** Every residual above concerns a write you did not make. This one concerns a write you *did* make, reported as nothing. Measured on 2026-07-27 at `ceb69219`, in the commit that landed as `e1d3da2e`: `br sync --flush-only` printed `Nothing to export (no dirty issues)` while `.beads/issues.jsonl` differed from `HEAD` by one line — the pane's own comment and notes edit, already on disk. Nothing was wrong with the flush. `br comments add` and `br update` had **already** auto-flushed that record when they ran, so by the time the explicit flush executed there was genuinely nothing left to export. The sentence is *true*, and it answers **did I flush anything just now**. The reader is standing there asking **is there anything to commit**. Two different questions with the same words, and the report answers the one nobody needs.

> **A flush's self-report is not a commit predicate. Diff `.beads/issues.jsonl` against `HEAD` regardless of what the flush says.**

The failure it produces is silent in every channel a careful pane checks: no error, no refusal, a zero exit, and a clean-looking flush line immediately above the decision. A pane that treats it as the commit predicate concludes there is nothing to commit and drops its own record — the work stays in the shared database, so nothing looks lost until the export is next carried by somebody else's commit under their name. This is [the block-expiry rule](#a-block-is-a-claim-and-it-expires--re-test-it-before-you-wait-on-it-and-before-you-act-on-it) in its cheapest form: a status line is a claim about an instant, and this one is a claim about the *flush*, not about the *file*.

**Note which rule caught it, because that is the argument for the one directly above.** The gated diff does not consult the flush, so it ran regardless and reported 406 records to 406, no peer status transition, no peer field change, no comment removed and nothing owed in disclosure — and the commit carried exactly the one intended record. That is `verify && commit` earning its keep for the **second time on the day it landed, on a mechanism it was not written for** — the rule is `9b6a7dfa` at 15:25:38, this catch at 16:31:11, with the first outing recorded above falling between them: the third residual is about a peer's write arriving inside your window; this is your own write appearing not to exist. A rule that fires only on the case it was designed for is a special case. One that fires on a case nobody anticipated is a habit worth its cost.

**What this does not earn.** One instance at one commit on one host, class `bounded_model`. It is a property of a tool that lives **outside this repository**, so `br`'s flush accounting can change with a version and nothing here would notice — the same limit the rch and UBS sections record about their own figures. It does not establish that the report is ever *wrong*: it is accurate about what it measures, which is exactly why it misleads. And only the safe direction was observed — the record was already in the working copy, so the diff found it. Whether a flush can print that same sentence while the record is genuinely **absent** from the file is not excluded by this measurement, merely unobserved in it.

### A NEW file cannot be committed by the mandated form at all — and the technique that can **never touches `.git/index`**

**Read that heading as the whole claim, because this section otherwise says "never the index" and this is not the retraction.** The measured casualty above is a **shared-index** commit; what follows is not one, and the evidence is its own: across the run that landed `48c64a73`, `.git/index` was sha256 `b16392e5…` before and `b16392e5…` after — **byte-identical** — with `git diff --cached --name-only` empty before and **0** paths after the follow-up resync. Nothing here is permission to stage anything.

**The trigger is narrow and is the whole scope of the exception.** `git commit -o` commits paths git already knows; against an untracked path it refuses outright, which this file has never stated:

```text
error: pathspec 'crates/fln-conformance/tests/artifact_referent_census.rs' did not match any file(s) known to git
```

So the mandated form cannot introduce a new file **at all**. Assemble that one commit in a **private** index built from `HEAD`:

```bash
IDX=/data/tmp/<yours>.index                              # OUTSIDE the repository
GIT_INDEX_FILE=$IDX git read-tree HEAD                   # start from HEAD, never from the shared index
GIT_INDEX_FILE=$IDX git add -- <exactly your paths>
GIT_INDEX_FILE=$IDX git diff --cached --name-only HEAD   # must print EXACTLY your paths
GIT_INDEX_FILE=$IDX git commit -F <msg>
```

`GIT_INDEX_FILE` redirects every git command in that environment, so the `git add` writes `$IDX` and nothing else.

**It is stronger than `-o` rather than a fallback from it, which is why it is stated here instead of hidden as a workaround.** The second residual above measures that `-o` reads the **worktree**, so a copy older than `HEAD` — or a peer's edit to a path you name — lands under your authorship with no conflict and no warning. An index built from `HEAD` plus exactly your paths **cannot contain anything else by construction**: not a peer's staging, not a peer's worktree edit to any other path. It does not close the first residual, which is about paths you name but did not author.

**The gate is part of the technique, not an optional extra.** Both assertions must hold *before* the commit runs, in one `&&` chain:

- the prospective delta — `GIT_INDEX_FILE=$IDX git diff --cached --name-only HEAD` — is **exactly** the paths you intend; and
- **nothing is staged in the shared index**, re-checked immediately before rather than earlier, because the resync below discards staged content and is safe only when there is none. That re-check is [the block-expiry rule](#a-block-is-a-claim-and-it-expires--re-test-it-before-you-wait-on-it-and-before-you-act-on-it) applied to shared state: an earlier look at a staged set has expired by the time you act on it.

**The resync is mandatory, and skipping it hands the next pane a deletion to commit.** A private-index commit leaves the shared index with no entry for the new file while `HEAD` has one, which a later `git status` reads as a staged **deletion**. Repair it immediately with `git read-tree HEAD`, which is safe precisely because the gate refused unless nothing was staged.

**What this does not earn.** Nothing enforces any of it: no hook can see how a commit was assembled, and the gate is a rule in a script one pane wrote. It says nothing about a peer's write landing between the gate and git's own read. One host, one git version, one instant, class `bounded_model`.

**Which pane made a commit is not recoverable from git, and inferring it has already misfired.** Measured over the last 200 commits at `7e1765cd`: **one** author identity, **one** committer identity, **one** `Co-Authored-By` trailer — every field git offers is constant across all three panes. This file states that fact three times already, but always as a *limit on some other rule*; the two operational consequences have lived only in handoffs, which is why every handoff has had to re-teach them:

- **Identify your own commits by subject line, never by author.** `git log --author` returns the whole repository.
- **When you land a commit, name the sha in your next message to whoever sequences the swarm.** The alternative is not neutral: absent your word they must attribute by *inference from what you last said you were working on*, which is a heuristic. On 2026-07-27 it credited the wrong pane — inside a message praising the work — and the misattribution was caught only because the pane being praised checked and declined it. **Declining credit you did not earn is the same act as declining a close you did not earn**, and a swarm where authorship is provably indistinguishable depends on that reflex rather than on a record.

**What this does not earn.** Nothing enforces any of it. `git add` still works; the pre-commit hooks judge the prospective *tree*, never how it was assembled; and commit authorship is not attributable in this shared checkout — the same limit the one-row manifest rule records below, and the reason the naming protocol above is a courtesy rather than a mechanism. This is a rule, not a guard. The cells are `bounded_model`: one host, one git version, one instant.

---

## Session Completion ("Landing the Plane")

Before finishing a work session you MUST:
1. File beads issues for remaining work (anything needing follow-up).
2. Run quality gates (if code changed) — tests, clippy, fmt, `ubs`.
3. Update issue status — close finished work, update in-progress.
4. `br sync --flush-only` to export beads to JSONL, then commit it **by path** — `git commit -o .beads/ …` per the section above, never `git add`.
5. Hand off — summarize what changed, gates run + results, remaining risks/gaps, concrete next steps.

---

## The routing store is the source of truth; a handoff's routing section is a summary of it

Panes hand work to each other by writing `/data/tmp/claude-1000/route-<from>-to-<to>-<topic>.md` carrying the **literal before/after text** of the change proposed, because Agent Mail has repeatedly failed as a delivery channel here and a *described* change is a claim with an expiry. Each handoff then carries a routing ledger summarising what arrived and what was sent, and step 5 above is where that ledger is written.

**That ledger is a summary, and it can be false at the moment it is written.** On 2026-07-27 a cc_2 handoff recorded "Nothing was routed TO me this session" while **three** files addressed to cc_2 already sat in the store: an h4o1 adoption route relaying a sequencer decision that assigned work to that very pane, a proposed UBS-TRIAGE/1 amendment, and a revised robot-schema change. All three predate the handoff — the earliest by **54 minutes** — so "they arrived afterwards" does not explain it. Nobody was careless. A ledger records what a pane *acted on*; a store holds what it *received*, and the two diverge silently in exactly the direction that strands the successor, because unacted-on items are the ones a summary has least reason to mention and most reason to be read for.

> **On intake, list the WHOLE store by mtime and read what is RECENT — never what is ADDRESSED. Do not take the predecessor's ledger as the population.**

```bash
find /data/tmp/claude-1000 -maxdepth 1 -name 'route-*.md' -printf '%T@ %p\n' | sort -rn
# the listing IS the population; the ledger is not. `ls` is aliased here, so never `ls -t`
```

It costs one command, and it is the section above applied to the one artifact a fresh pane has no other way to check: a status recorded at time T is a claim with an expiry, and a handoff's routing section is a status recorded by someone who has since stopped running.

**The second half of that rule used to read "read every file whose name targets you", and it is now measured wrong — by the pane it stranded, against an instruction three panes had been handed an hour earlier.** `route-cc_1-to-sequencer-f2t9-ownership-column-wrong-artifact.md` is *about* cc_3's routed partition and *addressed to* whoever sequences the swarm, so no `to-cc_3` glob will ever surface it; and it was written three minutes before cc_3's predecessor composed their handoff, so the ledger could not carry it either. One file, and both channels a successor has are defeated at once. **A filename carries the sender's idea of the audience, not the reader's need.**

**The specific shape is a route addressed to the sequencer about your artifact, and it defeats every addressing scheme rather than this one.** There are exactly two candidate audiences — the pane that must decide, and the pane that must act — and a finding about someone else's work is naturally filed under the first while the second is the one who has to read it. No convention repairs that, because the sender is not wrong to address the decision-maker. Only reading by *time* rather than by *address* sees it. What it cost is why this is doctrine and not a note: the route corrected a load-bearing number in cc_3's own partition — rows with no living owner, 22 down to 12 — and three panes would otherwise have acted on the wrong one. Landed at `fb6c1fd3`; this file already disclosed the hole in the abstract, one paragraph down, and an abstract disclosure did not stop it.

**What this does not earn.** It is a practice and not a mechanism: nothing reconciles a handoff's routing section against the store, nothing enforces the filename convention, and the store lives outside the repository, so nothing here can hold its contents, its retention or its path. Reading by mtime removes the addressing hole and installs two of its own, so state them rather than discover them: a file not matching `route-*.md` at all is still invisible, and **recent** has no boundary — the instance above was three minutes old, nothing says how far back a fresh pane must read, and the store is never pruned. Reading a route is still not acting on one, which stays a judgement about ownership.

**Writing a rule down and telling people are two different acts, and this file states only one of them.** The lesson everywhere above — a broadcast dies at the next rotation, so put it here — is one direction. Its converse is equally true and is the one that gets skipped: **landing a rule in this file reaches every *future* pane and no *current* one**, because a pane already running has read this file and has no reason to read it again. On 2026-07-27 seven rules that existed only in sequencer broadcasts were written into this repository by panes that noticed they lived nowhere durable; every one of them still needed a broadcast *as well*, because the panes that most needed them were mid-rotation and would not see the commit. Publication is for your successors, notification is for your peers, and neither substitutes for the other. **When you land a durable rule, say so to whoever sequences the swarm and ask for it to be broadcast, and record in your handoff which of the two you did** — a rule that is committed but unannounced looks identical, from inside the repository, to one that is both.

---

## MCP Agent Mail — Multi-Agent Coordination

A mail-like layer for agents to coordinate via MCP tools/resources: identities, inbox/outbox, searchable threads, advisory file reservations with human-auditable Git artifacts. **Measured unreliable for delivery in this swarm on 2026-07-27** (three failures in one day); use the routing store above and tell the sequencer the path.

- **Register identity:** `ensure_project(project_key=<abs-path>)` → `register_agent(project_key, program, model)`.
- **Reserve files before editing:** `file_reservation_paths(project_key, agent_name, ["crates/fln-kernel/**"], ttl_seconds=3600, exclusive=true, reason="br-###")`.
- **Communicate with threads:** `send_message(..., thread_id="br-###")`, `fetch_inbox`, `acknowledge_message`.
- **Prefer macros:** `macro_start_session`, `macro_prepare_thread`, `macro_file_reservation_cycle`, `macro_contact_handshake`.
- Common pitfalls: `"from_agent not registered"` → `register_agent` in the right `project_key` first; `"FILE_RESERVATION_CONFLICT"` → adjust patterns / wait / use non-exclusive.

### Everything above is documented and is not the channel in use — read this before reaching for it

**The section above describes a producer that, today, does not produce.** Observed on
2026-07-27, four separate failures in one day: one pane's inbox fetch timed out at 30 s
**three times**; a routing request sat undelivered for **fourteen minutes**; a second pane
waited on a request that never arrived; and a third pane's own handoff ledger recorded
"nothing was routed to me" while **three** routes addressed to it sat in the store. The mail
section is kept rather than deleted, because it may work again and a fresh pane should know
**both** facts. What it must not do is what it did four times: send a pane to the broken
channel with no mention that a working one exists.

**The channel in use is the routing store**, and its rules are stated once, above:
[The routing store is the source of truth](#the-routing-store-is-the-source-of-truth-a-handoffs-routing-section-is-a-summary-of-it).
That section and this one were written within minutes of each other by two panes who could not
see each other's work, and the first version of this paragraph restated the store's convention
rather than pointing at it — two copies of one fact in one file, which is the defect this file
names most often. Deduplicated deliberately; what remains here is only what that section does
not carry.

Two operational facts that belong at *this* vantage point, because they are what a pane
reaching for mail actually needs:

* **The store is outside the repository**, so writing a route is safe even while the build
  gate is held — no mechanism in [The Build Gate](#the-build-gate--while-a-lane-runs-the-repository-is-frozen)
  can see it. That is half of why it won. Nothing polls it either, so tell whoever sequences
  the swarm the path once the file is written.
* **On intake, enumerate the store yourself.** `ls` is aliased in this environment; use
  `find /data/tmp/claude-1000 -maxdepth 1 -name 'route-*.md'` and sort by mtime. A route
  written after your predecessor composed their handoff is precisely the one that handoff
  cannot mention.

One further instance of why the literal text is required, recorded because it cuts toward the
reader rather than away: a routed patch proposing a trigger-reachability predicate read
correctly in prose, and only writing its literal body out exposed that it rejected a spelling
YAML permits — a wall that would have reddened a correct workflow. The prose was not wrong
about intent; it simply could not be checked.

---

## The Build Gate — while a lane runs, the repository is frozen

**The mechanism, measured rather than described.** **Five** checks can end a lane, not one, and which of them you are subject to decides which mid-lane action is fatal. **That word is no longer transcribed** — `the_build_gate_table_names_every_freeze_mechanism_in_the_code` binds it to the number of rows below and binds those rows to the code in both directions, because this count said "Four" for two days after a fifth mechanism landed, and the sentence it replaced was itself a correction (`franken_lean-pfei` instance six). Measured at `3407ca10` against the *committed* `scripts/evidence.py` (blob `79172e7f`), every cell with a positive control, in a purpose-built real repository — bead `franken_lean-build-gate-lane-governed-set-98np`, comment `1367`:

| # | mechanism | where | scope | measured |
|---|---|---|---|---|
| **M1** | `repository_state() -> (head, tree)` sampled **three times**, with `scan_index_and_worktree()` between samples | `verify_vendor_binding` in `scripts/evidence.py`; reached by every `hash-tree --vendor-path` and by `vendor-binding` | the **`HEAD` commit, repo-wide** — plus content **scoped to `vendor/lean4-src`** | a commit landing in the sample window: **12/12 killed**, `Reference repository state changed during verification`. Continuous churn of a tracked file **outside** `vendor/` during the call: **12/12 passed**. Untracked creation outside `vendor/`: **12/12 passed** |
| **M2** | governed root, **start vs end** | `scripts/check.sh` → `final_workspace_changed`, exit 3 | that lane's `INPUT_PATHS` | root moves for an in-set write, not for an out-of-set one; a write **reverted before finalization is invisible** |
| **M3** | governed root at **every step boundary** vs run start | `require_unchanged` in the lane script → `governed_inputs_changed`, exit 3 | that lane's `INPUT_PATHS` | same content semantics as M2, caught a step earlier instead of at the end |
| **M4** | `stable_file_facts` `fstat`s each governed file **before and after reading it** | `scripts/evidence.py` → `file changed while being read`; `check.sh` names it `governed_input_mutation_during_initial_hash` | the paths being hashed | churn of a **governed** file during the hash: **8/8 killed**. Churn of an ungoverned file: **8/8 passed** |
| **M5** | `stable_symlink_facts` — M4's sibling for a governed **symlink**: `lstat` rather than `fstat`, and it hashes the link's **target string**, not the target's bytes | `scripts/evidence.py:1500` → `canonical link changed type`, `symlink changed while being read` | the governed symlinks being hashed | **retargeting a symlink moves the governed root with no file content edited anywhere** — the one write shape M2/M3/M4 all read as "nothing changed". Measured by cc_1 in `76298969`; the row above is that measurement plus the code, and I have re-derived only that the function exists and which refusals it raises |

**The sentence this section used to carry — that the freeze "asserts that the whole repository held still" — is false, and the correction makes the rule sharper, not weaker.** M1's *content* check is scoped to the pinned Reference tree; only `rev-parse HEAD` is repo-wide. What is genuinely path-agnostic is **committing**: a commit of anything, anywhere — `.beads/`, `ci/`, `AGENTS.md`, a file no lane governs — moves `HEAD` and kills any lane in its sample window. Both casualties recorded below were commits, which is exactly why the old wording predicted them correctly while naming the wrong cause. Note also what M2/M3 and M4/M5 divide between them: M2 and M3 compare content at **instants**, so transient drift slips between them, while M4 and M5 are the ones watching an **interval**.

Two consequences you must hold together, because either alone yields a wrong rule. **No mechanism is the strict one.** M1 is stricter than any path list about commits and blind to uncommitted edits outside `vendor/`; M2 through M5 are precisely the reverse. The safe rule is their **union**, which is what the box below states, and getting it wrong has cost two lanes:

```bash
flock -n /data/tmp/fln-gate.lockfile -c true    # exit 0 = free, exit 1 = HELD
```

> **HELD means something holds the gate lock — not that a lane is running. Treat the repository as frozen anyway: make no change of any kind inside it.** No commits. No edits. No file creation. No `br` command that writes. Not `crates/`, not `ci/`, not `scripts/` — and **not `AGENTS.md`, `README.md` or the plan either.** Holding still is cheap and the conservative behaviour is unchanged; what you may **not** do is report that freeze to anyone else without naming its holder, for the reason two paragraphs below.

**Why three people derived three wrong rules.** `INPUT_PATHS` in `scripts/check.sh` is real, and it *looks* like the boundary — it is an explicit, short, authoritative-looking list, so everyone reads it as "these are the files that matter". It governs M2/M3 (`governed_inputs_changed`, `final_workspace_changed`) and nothing else. But the freeze is not simply "separate and stricter", which is what this paragraph used to say and what the measurement disproves: it is stricter in one direction and **blind** in the other. If you remember one thing, remember the union: **any commit kills any lane; any write to that lane's governed set kills that lane; and "my file is not on the list" is an argument about M2/M3 that says nothing about M1.**

The three attempts, recorded because each was made in good faith by someone following the rule as then stated:

1. "No writes to governed paths" — missed that `.beads/issues.jsonl` is `INPUT_PATHS` line 150, so *filing a bead* is a write. Cost the first `env_snapshots` lane. **This attribution is now doubted and has not been re-measured:** `.beads/issues.jsonl` is in **`check.sh`'s** list and *not* in `env_snapshots`', so M2/M3 could not have seen it there, and the kill was more likely M1 catching an accompanying commit. The bundle was not retained, so this stays recorded as unresolved rather than replaced by a second confident guess.
2. "…and `AGENTS.md` is outside `INPUT_PATHS`, so it is safe mid-lane" — the half of that sentence about `INPUT_PATHS` was *correct* and the conclusion still wrong, which is what makes it worth keeping. `24b16eeb` was an `AGENTS.md` **commit** at 21:30:59, and it killed the rerun at 21:31:10 through M1's `HEAD` half, which no path list governs. **The section you are reading replaces the one that did it.**

   **This entry used to end "an uncommitted `AGENTS.md` edit would have survived all four mechanisms — a fact about the mechanisms". That is false, and it is false in the direction that costs a lane.** It was a fact about **one** lane. Measured at `5f7e44ad` by deriving every lane's governed set from the scripts instead of reading one: `scripts/e2e/vellum_naming_no_mock_e2e.sh:83` lists `AGENTS.md`, `README.md` and `COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md` in its `INPUT_PATHS` — and again in its `SUBJECT_PATHS`. For that lane an **uncommitted** `AGENTS.md` edit is a governed-input mutation and fires M2/M3/M4 with no commit anywhere. The old sentence generalised from `env_snapshots`, whose 13 paths do not include it.
3. This one, taken from the source line rather than inferred from a path list — and now superseded by the measurement above, because reading the source got M1's *scope* wrong in the same way the prose did.

**What is safe while the lock is held:** reading anything; `br` **only** with `--no-auto-flush` (it auto-flushes the JSONL on ordinary *reads*, so a bare `br show` writes); thinking, planning, drafting; and writing **outside the repository**, i.e. under `/data/tmp`. Draft the bead body, the commit message, the diff into the scratchpad and apply them the moment the lane releases. Avoid `cargo` too — it can rewrite `Cargo.lock`.

**A failed probe is an answer, not an obstacle.** If `flock -n … && git commit …` exits 1 with no commit, the plumbing worked: the gate said *held*. Do not re-run without the guard. Written from a real one — on 2026-07-25 cc_3 diagnosed the short-circuit correctly, read it as shell friction, committed directly 16 seconds into a running lane (`bb561892`), and cost the rerun before this one.

**Do not use `pgrep -f` to decide whether a lane is running.** It matches its own command line and will report a lane that is your own grep. Use `ps -eo pid,ppid,args` with your own process tree excluded. **This sentence used to end "or just trust the lock, which is what it is for", and that clause is now measured false in both directions** — it sent readers away from the one thing that answers the question and towards the one thing that does not.

**A probe that says FREE can also be wrong, and that is the harder case.** `flock -n` answers "is it held *right now*", and the answer is stale the instant it returns. The lane acquires with `flock -w 2400` — a *waiting* acquire — so it can be dispatched and queued while the lock still reads free. On 2026-07-25 three panes probed correctly, got free, and wrote; `.beads/issues.jsonl` was written at 21:23:35Z against a lane dispatched at 21:23:06Z. **Do not "fix" this by wrapping the write in `flock -w …`**: that queues your write to fire the moment the lock frees, which is precisely when the next lane takes it. There is no safe way to *gate* a write on a probe. Write when the tree is confirmed quiet, not when a probe happens to return zero.

**A probe that says HELD is wrong in the mirror direction, and that is the half this file was asserting rather than doubting.** Bead `franken_lean-gate-lock-producer-optional-o2vz` records why FREE carries no information: the gate lock engages only if the caller volunteers, so an unwrapped lane leaves nothing for any probe to observe. Derived at `8c13c543`, the population is sharper than "no lane acquires it" — `fln-gate.lockfile` is named in exactly **three tracked files**, `.beads/issues.jsonl`, this file, and `ci/VERIFICATION_MANIFEST.jsonl`, every one of them prose or record. **Zero executable surfaces name it at all.** The one `flock` in `scripts/evidence.py` is an unrelated `fcntl` lock on its own descriptor, identical in the committed blob and the working copy. HELD then fails for the mirror reason: *anything* may take that path. Measured by the sequencer at 2026-07-27T08:25:56Z — a pane's `flock -n /data/tmp/fln-gate.lockfile zsh -f` (pid 2719272, state `S<s`, WCHAN `do_wait`) held the gate for nearly three minutes with **no lane running**. That form is not a probe: it runs a shell under the lock for that shell's entire life, and the probe form is the `-c true` one in the box above. Reproduced by cc_1 on a scratch lockfile at `8c13c543`, same state signature, with a planted non-lane holder: two consecutive `-c true` probes both exit 0, so the probe never holds; under the plant the prescribed probe exits 1.

**So neither answer is load-bearing, and the common cause is that nothing joins this lock to lanes in either direction** — `fln-bench-apparatus-empty-referent-bkw6`'s empty referent at the process layer, where the far end of the claim is not stale but absent. It has already cost a phantom freeze: a tick printed `static since lane start`, skipped its own bead queries, and told six panes the repository was frozen for a lane that did not exist. **The repair needs no new machinery and is available in one command: name the holder before you believe it, and never publish a freeze you have not attributed.** **The command this file used to give for it was `fuser -v <lockfile>` or `lsof <lockfile>`, and both answer a different question — measured false at `f5359c22`, in the direction that manufactures the very phantom freeze this paragraph exists to prevent.** A lock belongs to the open file description; `fuser` and `lsof` report every process holding a **descriptor**. Three cells on a scratch lockfile, one variable each, ground truth taken from `flock -n <lock> -c true`: on a fresh free inode both tools name nothing — the negative control, without which the cell passes vacuously; against a genuine holder `fuser` names **two** pids, the holder and its child; and against one process that merely did `exec 7>><lock>` and never locked, with the gate **FREE by ground truth**, `fuser -v` and `lsof` **each named that process as a holder**. `fuser`'s own ACCESS column reads `F` there, meaning *open for writing* — it never claimed to mean *locked*. The third form, `ps -eo pid,ppid,stat,wchan,args`, takes no lockfile at all and associates no process with the lock: it can confirm an argv you already have and cannot find one. The first cell run against this was itself contaminated — a killed holder left its child holding the lock, so the "free" cell measured a held one; a cell whose precondition is not asserted varies two things, which is this file's own rule arriving inside its own repair.

**Use `/proc/locks`**, the kernel's record of *actual* holdings: one `FLOCK` row per held lock carrying the holding pid and the file's `MAJOR:MINOR:INODE`. Match on the inode from `stat -c '%i' <lockfile>` and exclude your own pid. Then **resolve the holder's working directory and require it to be this repository before classifying its argv at all** — the paragraph below measures why — and only then classify that argv against `scripts/check.sh` and the 21 scripts in `scripts/e2e/`, where a holder matching none of them is not a lane. **The classification rule is what makes the superset load-bearing rather than cosmetic, and a superset breaks it in both directions:** once a lane wraps its own invocation its caller's descriptor appears in its own holder report, so a reader classifies that argv, finds a lane, and concludes a lane holds a gate that a stray shell holds — inverting the repair; and an unrelated process with the file merely open is classified not-a-lane, so a pane publishes that a squatter holds a gate a legitimate lane holds. Measured independently by cc_2 and re-measured by cc_1 against the same landed bytes.

**Resolve the holder's `cwd` first, because an argv-only classification is unsound wherever two checkouts on one host share a script name — and this box has many.** The rule above says to classify the argv against `scripts/check.sh` and the 21 lane scripts. That path is **relative**: it names a file *within some checkout* and says nothing about which, and `scripts/check.sh` is not a unique name on a machine hosting a dozen FrankenSuite repositories. **Negative control, measured on 2026-07-27 at `fe9198dd`:** pid 435986's argv was `bash scripts/check.sh`, which matches the classification pattern **exactly** and would be scored a lane by the rule as written — and `readlink /proc/435986/cwd` returned **`/data/projects/frankengraphdb`**. A different repository, its own gate, nothing to do with this tree. Its child was `bash /data/projects/frankengraphdb/scripts/g0_identity_e2e.sh`, which is where the collision became visible, since only *that* argv happened to be absolute.

The cost is the thing to take from it: a pane applied this section's own repair faithfully, concluded a franken_lean lane was running, and **froze itself for twenty minutes on a repository nothing was holding**. That is the **phantom freeze this section exists to prevent, arriving through the section's own prescribed fix** — the rule did not fail to fire; it fired on a non-holder. So `readlink /proc/<pid>/cwd` and require it to equal this repository's root before the argv is classified at all. **The classifier has THREE outcomes, not two — lane, stray, and UNATTRIBUTED — and the rule as written had room for only the first two.** That is the structural defect, not merely an edge case: `cwd` is **unreadable for any process owned by another user**, which on this shared box is the *common* case, so a two-bucket classifier must put every such holder somewhere and is wrong whichever it picks. **An unattributed holder is reported as neither.** Repairing only the foreign-repo half yields the mirror error — a holder you cannot read scored a stray, and a stray is a claim that no lane is running.

**Independently patched and controlled in four cells by the sequencer in the same tick, so the tick script and this file agree** — and its *failed* first attempt is the half worth keeping: all three cells returned **identical output**, which nearly read as a result and was a broken scan, the pids having been captured dead with `$!` inside a command substitution. **Identical cells across a matrix are a broken scan, not a finding** — the same lesson this file already records for an empty grep, arriving in the control rather than in the thing controlled. The working matrix, one variable per cell: (1) lane argv with `cwd=/data/projects/frankengraphdb` → **foreign repo, not our lane**, the case measured above, which the argv-only rule scored a real lane; (2) lane argv with `cwd` this repository → **real lane**, the positive control, without which the repair degenerates into never parking for anything; (3) non-lane argv with our `cwd` → **stray lock**; (4) dead pid → **unclassified**, not a guess.

The same correction applies to anything else naming holders by argv — an orchestrator tick script classifying that way carries the identical defect. **And `cwd` does not rescue you from the self-match trap, which is the one place this repair makes things *look* better without being better.** Measured while landing this paragraph: a `pgrep -f 'scripts/check.sh|scripts/e2e/'` returned two pids whose `cwd` resolved to **this repository**, passing the new check cleanly — they were the `pgrep`'s own subshell, and both were already dead when `/proc` was read a second later. Your own tooling has the right `cwd` *by construction*, so cwd-resolution filters foreign checkouts and does nothing about self-matches; exclude your own process tree as well, and read `/proc` for a pid that has since exited and you get the sequencer's dead-cell artifact rather than an answer. **What this does not earn:** `/proc/<pid>/cwd` is Linux-specific; a process that `chdir`s after launch reports where it *is*, not where it started; and both the measurement above and the four-cell matrix are one host at one instant, class `bounded_model`, bound by no test.

`scripts/lib/gate_lock.sh`'s `fln_gate_name_holder` still uses the `fuser` form at `f5359c22`, so this is a **live** defect and not a repaired one (bead `franken_lean-gate-lock-producer-optional-o2vz`). **What this does not earn:** `/proc/locks` is Linux-specific, and its blocked-**waiter** rows begin with `->`, which shifts the columns — skip them deliberately, because a waiter is not a holder. Where a lock is held through a shared open file description the kernel records one pid while others hold it too, so naming the recorded holder is a judgement rather than a measurement. Nothing here is bound by a test; it is prose, one host, one commit, class `bounded_model`. Note what you cannot recover afterwards: on release the lockfile is **0 bytes**, so nothing anywhere records that it was ever held, by what, or when — which is why this must be observed live and why a run's own self-report would be the wrong repair. And because a HELD probe is a block, the block-expiry section above applies to it exactly: re-test it before you wait on it, and now also name what is holding it.

**A lane can kill itself.** Its own script and `scripts/evidence.py` are both tracked, so the pane running the lane must finish editing them **before** launching, not merely refrain during. A save 30 seconds in looks identical to an outsider's edit and ends the run the same way.

**A *static* dirty tree is fine; a *changing* one is not.** The conclusion holds and its old justification did not: `tree` is `rev-parse HEAD:vendor/lean4-src`, a **committed subtree object id**, so uncommitted work never enters M1's comparison at all rather than "hashing identically". What actually makes a static dirty tree safe is that M2/M3 compare content at instants and M4 only refuses a file that moves *while it is being read*. An unfinished edit you stop touching is acceptable — a rushed commit to "get it in before the lane" is not, and that is M1.

**Two traps inside that allowance, both measured.** Writing a governed file with **byte-identical content** does not save you: M4's stability check includes `st_mtime_ns` and `st_ctime_ns`, so a no-op rewrite during a governed hash still raises `file changed while being read` (7/8 trials; the 8th is the race, not a reprieve). And "static" means *untouched*, not *unchanged* — a formatter, an editor autosave, or a `cargo` invocation rewriting `Cargo.lock` all count as motion.

**Narrowness is a property of the lane you are running, never of lanes.** Derived at `5f7e44ad` from all 21 scripts in `scripts/e2e/` rather than read off one — 98np R1. **Eight lanes declare a governed set; thirteen declare none at all** and so cannot raise M2/M3/M4 under any write:

| governed paths | lane | relative to `check.sh`'s 51 |
|---|---|---|
| 40 | `contract_handoff.sh` | 2 outside: `scripts/extract/census_materialize.sh`, `…/validate_extern_builtin_census.py` |
| 19 | `vellum_naming_no_mock_e2e.sh` | 3 outside: **`AGENTS.md`**, `README.md`, the plan |
| 15 | `closure_audit.sh`, `structure_gate.sh` | contained |
| 13 | `env_snapshots.sh` | contained — the lane every generalisation here was made from |
| 12 | `unsafe_note_clippy.sh` | contained |
| 10 | `verdict_schema.sh` | governs bare **`scripts`**, so *any* write under `scripts/` voids it; `check.sh` enumerates individual scripts instead |
| 8 | `kernel_replay.sh` (`AP6_INPUT_PATHS`) | contained |
| 0 | the other 13 | no governed set; M1 only |

So "an e2e lane's governed set is narrower than `check.sh`'s" is true of `env_snapshots` and **false of three lanes in three different directions**. Two consequences: a `verdict_schema` lane is killed by any pane touching `scripts/`, which is broader than `check.sh` in that dimension; and the thirteen zero-governed lanes are protected by **nothing but M1**, which — given that no lane takes the gate lock unless its caller wraps the invocation (bead `franken_lean-gate-lock-producer-optional-o2vz`) — means a mid-lane write to their subject is invisible to every mechanism.

**The derivation needed its own control, and that is not a footnote.** The first extractor matched `^[A-Z_]*INPUT_PATHS=\(` and reported `kernel_replay.sh` as governing **zero** paths; it declares `AP6_INPUT_PATHS`, and the character class excluded the digit. Caught only by an independent count of governance references per file, which disagreed. A derived scope is exactly as trustworthy as its extractor, so derive the scope **and** a cheap independent signal, and reconcile them.

**What this section still does not earn — stated because it is exactly the defect family of item 7 below, sitting on the doctrine that costs the most lanes.** Nothing holds any of it to the code. The table of mechanisms above is a **measurement written down**, not a derived one: they were found by reading `scripts/evidence.py`, `scripts/check.sh` and one lane script, so a *sixth* could exist and nothing would say so — a *fifth* already did, `stable_symlink_facts`, found by derivation after the four-row table had read as complete three times. **The governed-set table above is now held to the scripts per commit — 98np R1 derived it, R4 binds it.** `crates/fln-conformance/tests/build_gate_governed_sets.rs` re-derives every lane's governed set at test time and fails in **both** directions: a lane whose declaration moves without this table moving, and a row that moves without its lane. The `| 0 | the other 13 |` row names no lane, so it is bound to its **cardinality**; and the sentence introducing the table is bound to both, because item 7 records a day this section's prose and its own table disagreed after a row was added and only two of the three places stating the count were moved. Nine mutants planted against the guard, each killed by a named test. A tenth — a partition check — proved **unkillable**, because every membership change is already caught by one of the three rules above; it was removed rather than kept, and the guard says so where it stood, so it is not re-added as an improvement.

**What that binding covers is every lane's path COUNT. What nothing covers is its GRANULARITY — and granularity is the half that decides whether your write voids a lane.** Five of `check.sh`'s fifty entries are **bare directories**: `ci crates tools`, plus `contracts` and `tribunal`. Between them they cover essentially every source file in this repository, so the rule a pane actually needs is not on this page — **any edit to any Rust file under `crates/` or `tools/` voids a running `check.sh`**, and equally `closure_audit.sh`, `structure_gate.sh` and `verdict_schema.sh`, plus `contract_handoff.sh` for anything under `tools/structure-guard` and `kernel_replay.sh` for anything under `crates/fln-conformance`. Fifty *entries* is not fifty *paths*, and the difference is the whole repository. The count guard cannot see this: a row saying `40` stays true whether those forty are forty files or forty trees.

**The obvious probe inverts the answer, which is why this paragraph exists.** `grep -rln <your-path> scripts/check.sh scripts/e2e/*.sh` returns **nothing** for `crates/fln-conformance/tests/ci_execution_join.rs` and nothing for `tools/structure-guard/src/contract_handoff.rs` — two files governed by **seven** arrays each. Measured at `984a1555`, run first, and believed until a second probe contradicted it. **A search returning nothing is evidence of absence only when the search is known to be capable of finding the thing.** Derive the arrays instead, with `[A-Za-z0-9_]*INPUT_PATHS=\(`: `[A-Z_]*` misses the digit in `kernel_replay.sh`'s `AP6_INPUT_PATHS` — the failure the paragraph above already records — and a `+` where that `*` stands misses bare `INPUT_PATHS=(` altogether, yielding **21** entries across 22 scripts instead of **217**. Both bugs parse cleanly and return a well-formed answer meaning "you are safe to write". Then expand each entry as a directory prefix, and **floor the result**, because that floor is the only thing that caught either bug.

Two properties worth taking from it. Its anti-vacuity floors are **reachable from a test**: an earlier version read `scripts/e2e/` directly inside the `#[test]`, and the campaign killed every comparison mutant while leaving both floors alive, since with 21 real lanes present `lanes.len() >= 20` can never fire. A check that exists for the day the scan breaks is precisely the one a healthy tree cannot exercise — inject the inputs or it is decorative. And the derivation is reconciled against a **cheap independent signal**, because the first extractor for R1 matched `^[A-Z_]*INPUT_PATHS=(` and reported `kernel_replay.sh` as governing zero: it declares `AP6_INPUT_PATHS` and the character class excluded the digit. A derived zero looks exactly like a lane that governs nothing, so it is now refused as a broken scan instead.

The table of **mechanisms** is still prose. Treat it the way you would treat any claim whose evidence is prose: **re-measure before relying on an edge of it**, and record the commit you measured at.

---

## Beads (br) — Dependency-Aware Issue Tracking

This project uses [beads_rust](https://github.com/Dicklesworthstone/beads_rust) (`br`). Issues live in `.beads/` and are tracked in git. **`br` is non-invasive — it NEVER runs git.** After `br sync --flush-only`, commit the export **by path**: `git commit -o .beads/ <your other paths>`. Never `git add` — the index is shared with every other pane, and [the section above](#committing-in-a-shared-checkout--git-commit--o-paths-never-the-index) measures what that costs.

```bash
br ready                 # issues ready to work (no blockers)
br list --status=open
br show <id>             # full detail with dependencies
br create --title="..." --type=task|bug|feature|epic --priority=2   # 0=critical..4=backlog (NUMBERS)
br update <id> --status=in_progress
br close <id> [<id2> ...] [--reason "..."]
br dep add <issue> <depends-on>
br sync --flush-only     # export to JSONL (NO git ops)
```

Conventions: use the bead ID (e.g. `br-123`) as the Agent-Mail `thread_id` and prefix subjects with `[br-123]`; put the issue ID in the file-reservation `reason`; include `br-###` in commit messages. Map beads to workstreams (W1 Substrate & Contracts … W12 Distribution & Epochs) and gates (G0–G6) from §22 of the plan.

### A comment body is a shell word before it is a record — pass it with `-f`, never `-m` (bead `fln-qpkj`)

**The write reports success and the record is already damaged.** A body passed as an inline
double-quoted argument is expanded *before* `br` ever sees it, so a markdown backtick pair is a
**command substitution**: the shell runs the enclosed word and splices its output in. Observed on
`fln-171x` — a backticked field name vanished and the stored text reads `carries , the byte
offset`, a grammatical sentence with the identifier silently removed. It was caught only because
the word happened to name a binary that is not installed; `date`, `id` or `w` would have injected
their **output** into the durable record with no signal at all. **Bead comments are immutable, so
this cannot be repaired — only annotated.** The same hazard covers `$(…)`, bare `$VAR` and `!`.

```bash
br comments add <id> -f body.md          # correct: no expansion is possible
git commit -F msg.txt                    # the second surface: `-m` globbing eats backticked tokens
```

**Post-hoc detection does not work here and the measurement is the reason, not an excuse.** Over
407 beads and 1502 stored comments, the two signatures with real recall are saturated by this
project's own house style — call syntax quoted in comments (169) and column-aligned tables inside
comments (162) — so 19.4% of comments carry a signature and **that figure is not a damage count.**
Hand-adjudicating the seven low-saturation hits gave 1 confirmed, 1 correction quoting it, 1
previously-unrecorded candidate, 1 ambiguous, and 3 false positives all from `--root .`. This is
[`fln-ysvo`'s shape](#evidence--census-pins--operational-gotchas): **a detector saturates on good
practice.** Refusing the write instead has no such problem, so the tool is a write-path one.

`scripts/br_comment.py` (`write <id> <body-file>`) hands the body to `br` through an **argv list**,
so no expansion is possible at all. On read-back `scripts/br_comment.py` refuses any mismatch it
finds, which is exact rather than heuristic: it compares what landed against what was meant rather
than reasoning about the path between them. (The producer is named twice on purpose — the census
that counts these claims segments by **physical line**, so a hard wrap falling between a claim and
its producer is by itself enough to make a bound claim read as unbound.) Demonstrated in both directions against a scratch database:
a body carrying a backtick *and* a `$(…)` is **accepted** byte-identically, the same body written
the corrupting way is **refused** naming the first differing character, and two controls separate
those from a verifier that always refuses.

**What this does not earn.** Nothing forces the tool's use: plain `br` still works and a corrupting
write still succeeds. The read-back proves *this* write landed intact and says nothing about any
other. The saturation figures are one corpus at one commit, class `bounded_model`, and the
adjudicated count is a **floor** — damage whose lost token left no whitespace scar is invisible to
any scan.

### The projection guard (bead `franken_lean-projection-republish-mechanical-voz4`)

`ci/KERNEL_CONTRACT_OWNERSHIP.jsonl` is a canonical projection over the sorted id set of `.beads/issues.jsonl`. A commit carrying the JSONL with a stale projection turns `cargo test` red **workspace-wide**, for every agent — and four separate agents produced that state on 2026-07-24/25 alone, each of whom knew the rule. One of them had not touched beads at all: an incidental `git add` swept the JSONL into their commit.

So it is enforced rather than remembered. `scripts/git-hooks/pre-commit` refuses any commit whose prospective tree changes `.beads/issues.jsonl` without a matching projection. Install once per clone (all panes share one):

```bash
bash scripts/git-hooks/install.sh          # sets core.hooksPath; idempotent
bash scripts/git-hooks/test_projection_guard.sh \
  scripts/git-hooks/pre-commit "${CARGO_TARGET_DIR:-target}/debug/kernel-ownership-publisher"
```

What to know when it fires:

- It refuses only when the **id set** moves. Status, comment and closure edits leave the projection valid and commit normally — the guard is precise, not a nag.
- It judges the **commit**, not the checkout, so it is correct under `git commit -o` (mandatory here) where the index and working tree differ.
- It compares the regenerated manifest **byte-for-byte** using the publisher binary. A record-count check would pass two equal-sized id sets with different members, and a second copy of the projection algorithm could drift from the real one.
- It refuses on a leftover `ci/KERNEL_CONTRACT_OWNERSHIP.jsonl.candidate` (structure-guard reads that state as typed inconclusive) and on anything it cannot decide — never exits 0 on an unanswered question.
- It chains to `.git/hooks/pre-commit` if one exists, so an Agent-Mail guard installed there keeps working.
- `--no-verify` bypasses it. That is a real limit: this closes the feedback loop at the moment of the mistake, it does not make the failure impossible.

---

### Closing a bead: the judgement row, and the one sanctioned exception to `ci/` ownership

A closed bead derives verification state `complete`, and a `complete` coverage row whose evidence arrays are empty fails `validate-verification-manifest`. So the close and its judgement row **must be one commit**: closing first reddens the workspace for every pane in the gap between two commits.

**This section is written entirely about closes, and the obligation is wider: FILING a bead owes a row too.** That cost a refused commit to learn, by a pane who had read this section and reasoned from it. A merely *created* bead has crossed what the validator calls the **adoption boundary**, and the verification-coverage-guard in `scripts/git-hooks/pre-commit` refuses the commit that files it when no row accompanies it. Its own words, refusing the first attempt at `23f80f44` on 2026-07-27:

```text
verification-coverage-guard: REFUSED — prospective verification coverage is invalid (exit 1):
  beads crossed the adoption boundary without coverage rows:
  ['franken_lean-d3-root-attr-no-creation-affordance-sso4']
verification-coverage-guard: New beads need judgment rows, and closed beads need
verification-coverage-guard: complete human-authored evidence in the same commit.
```

**So filing a bead is three artifacts in one commit, not one** — the bead, the regenerated ownership projection (gotcha 1 below, since any new bead stales it), and a coverage row. The row for an open bead is legitimately **sparse**: every evidence array empty, the notes carrying the measurement and what it does not establish, because no repair is being claimed yet. `franken_lean-evidence-fields-never-resolved-bs5o`'s row is the model and says so in its own text.

**The reasoning that fails here is worth stating, because it reads as sound and is half true**: *a judgement row binds a close; my bead is open and derives no `complete` state; therefore no row is owed.* Both premises hold. The conclusion does not follow, because the guard keys on the **boundary crossing**, not on the terminal state — and the paragraphs below, which are all about `complete` rows and `closed_at`, are exactly what makes the wrong inference available. Take the obligation from the refusal message, not from this section's title.

That collides with `ci/` being cod_2's. **Standing rule, decided 2026-07-25: atomicity wins, with disclosure.**

- You MAY edit `ci/VERIFICATION_MANIFEST.jsonl` in the same commit as your close, **strictly limited to your own bead's coverage row**.
- You MUST say so plainly in the commit message or a bead comment.
- You may NOT touch any other row, and NO other file in `ci/`. The adoption record, the schema, other panes' rows, `WORKSPACE_GRAPH.txt`, and the ownership projection's algorithm all remain cod_2's sole authority.
- **HOW you write it is part of the rule, not a style note: edit your own row's line IN PLACE, and never rewrite the whole file.** This is the one file where "never stash, revert or overwrite another agent's work" and "author your own row" meet, and a whole-file rewrite obeys the first rule's *intent* while breaking it anyway — a peer's uncommitted row is re-serialized under your hand without your ever deciding to touch it. Recorded from a real one on 2026-07-27: cc_1 briefly overwrote the manifest while a peer's `acm4` row was uncommitted, could not fully undo it, and disclosed the exact scope in both directions — content unchanged, that row's *whitespace* possibly no longer as its author wrote it, and now committed in that form. Measured afterwards by the user: `validate-verification-manifest` `valid=true`, 400 beads, 184 rows, 17 closure-bound, projection 400/400 MATCH, every string array sorted and duplicate-free, zero violations. **Clean — and the disclosure was still exactly right**, which is the whole difference between a residue and a defect. cc_2's attempt the same tick succeeded where an earlier one was blocked, and said the operative sentence out loud: *"I did not write a peer's row."*
- **The validator cannot cover you here, because it checks structure and not authorship.** A `valid=true` says every row parses and every array is sorted; it says nothing about who serialized which line. So its silence is not evidence that you touched only your own row. If you find that you have touched one, report the scope precisely — what might differ, and what provably did not — rather than letting a green stand in for an answer nobody asked the file for.

The trade is deliberate: a red workspace blocks six panes immediately and visibly, while a one-row edit by the person who owns the judgement is small, disclosed, and reviewable after the fact. Note that this is a **rule, not a guard** — nothing enforces the one-row limit, because commit authorship is not attributable in this shared tree.

Practical notes: array fields must be sorted and duplicate-free or the validator refuses the row; and a row that records what the work did *not* establish is worth more than one that implies a win (`franken_lean-ext-observable-fixture-drift-gap-vqnu`'s row says the capture was never stale, only unchecked).

**The row must judge *that* closure, and the validator checks it now** (bead `fln-judgement-row-not-bound-to-its-closure-iumd`). Non-empty arrays prove a row *exists*; they never proved it was authored for the close it is filed under, and at `b2ee77cd` a close landed carrying a row authored earlier for different work on the same bead, with `validate-verification-manifest` returning `valid=true`. So for any bead closed at or after `2026-07-26T20:50:06Z` — `fln-lyc8`'s close, the instance this was built from — a `complete` row must cite one bead comment on its own bead created at or after that bead's `closed_at`:

```
"artifacts": [..., "bead-comment:<bead-id>:<comment-id>", ...]
```

Which makes a close **three writes then one commit, in this order**: `br close`, `br comments add` recording the judgement, then the row citing that comment's id. The comment id exists before the commit does — that is the whole reason the citation is a comment and not the closing sha, since a row must be *inside* the commit that closes its bead and so can never name it. Closes before that instant are exempt **by their own `closed_at`**, so there is no allowlist to maintain.

**This sentence used to end "and the exempt set can only shrink". That was false, and it was doctrine nobody had measured** (bead `franken_lean-closure-binding-exempt-rows-uninspected-3s8w`, commit `7d10158c`). Exemption is keyed by the **bead's** `closed_at`, never by when the **row** was authored, so a coverage row added tomorrow for a bead that closed on 2026-07-20 is exempt *by construction* and this law never applies to it. The date boundary therefore does **not** close the population; it only classifies the rows that happen to exist. Measured at `29852ec1`: 155 closed beads, 147 of them pre-boundary, 113 complete rows = 105 exempt + 8 bound — and **42 pre-boundary closed beads carry no coverage row at all**, against 0 post-boundary ones. Those 42 are slots the exempt set can grow into, silently. It does not shrink either: repairing an exempt row does not move its bead's `closed_at`, so the count is unmoved by repair. It moves only when a row is added or removed for a pre-boundary bead, or a bead is reopened and re-closed.

The law is **satisfiable** for all 42 — a comment added today to a bead closed last week has `created_at` > `closed_at`, and 36 of the 42 already carry one — so the honest repair is to bind the disclosed exempt population to the measured one, **equality in both directions**, plus the conservation identity `exempt + bound == complete` as the anti-vacuity guard. Then 42 silent additions become 42 deliberate, disclosed ones: a new exempt row pushes 105 to 106 and its author must either bind the row or raise the number under review. Equality both ways is right here and one-way-plus-floor is not — that shape is for a declared remainder of *permitted violations*, which shrinks as people repair it; this is a disclosure of a *measured population*, which does not. **The guard is not built**: it belongs in `scripts/evidence.py` beside where `closure_exempt_rows` is produced, because a Rust re-implementation would plant a second copy of the predicate — the defect this bead's own family is about — and it waits on that file landing. Until it exists, the 105 is a number in a row that nothing rechecks.

What this earns is **structural**: the row was authored after the close and names an immutable post-close record. It does not read the comment, so it does not establish that the row's prose describes the work. The refusal names the bead, the closure instant, and why each citation present cannot bind it — take the requirement from that message rather than from this paragraph.

---

## bv — Graph-Aware Triage

`bv` computes PageRank/betweenness/critical-path/cycles over `.beads/beads.jsonl`. **Use ONLY `--robot-*` flags — bare `bv` launches a blocking TUI.** Start with `bv --robot-triage` (counts + top picks + quick wins + blockers). `bv --robot-plan` for parallel tracks; `bv --robot-insights` for full metrics (check `.Cycles` — must be empty).

---

## UBS — Ultimate Bug Scanner

Run `ubs <changed-files>` before every commit. **Its exit code is not a
verdict.** A nonzero exit can mean completed findings or a staging/scanner
failure; zero can mean a completed clean scan or that no scanner ran. The
JSONL-only control on 2026-07-26 exited 0 while saying `no supported languages
detected` and `nothing was checked (this is NOT a pass)`. A clean result
requires positive message-text evidence that the intended scanner ran,
accounted for every intended supported input, completed, and reported zero
blocking findings.

```bash
ubs file.rs file2.rs                    # specific files (< 1s)
ubs $(git diff --name-only --cached)    # staged files — before commit
ubs --only=rust,toml crates/            # language filter
```

Run from the checkout being assessed and pass relative paths. Do not invoke
UBS from one checkout with absolute paths into another. Do not compare counts
across trees unless cwd, relative path, and bytes are identical; hold cwd and
path fixed and vary only content.

Classify the terminal text before findings:

- `completed_clean`: intended scanner ran, every supported input is accounted
  for, totals are consistent, and there are zero blocking findings.
- `completed_findings`: the same execution/accounting proof, with one or more
  findings.
- `not_applicable_no_supported_inputs`: the declared change set contains zero
  files in languages UBS supports and the output confirms that fact. This
  supplies no scanner evidence and is never called a pass, but it does not
  block an unsupported-only documentation/JSONL commit; record it and use the
  applicable validators.
- `no_scanner_executed`: at least one supported input was intended, but its
  scanner did not run or did not account for that input. This supplies no
  safety evidence even when exit is 0.
- `staging_or_scanner_failure`: shadow-workspace preparation, missing scanner,
  timeout, or aborted/incomplete scan — supplies no safety evidence even
  though it may share a nonzero exit with real findings.
- `inconclusive`: execution, input accounting, completion, or totals cannot be
  established or contradict one another.

Only `completed_clean` is UBS-clean.
`not_applicable_no_supported_inputs` is an explicit non-pass with zero scanner
coverage; the last three modes block until corrected and rerun. A known-false
exception starts only from `completed_findings`, never from a failed or
vacuous run.

For a known-false class, put a durable `UBS-TRIAGE/1` comment on the active
change bead. Record: owning bead and exact class; absolute cwd; exact command;
UBS version; HEAD and porcelain status; relative input paths plus SHA-256;
exit code; expected/observed scanner and its positive execution evidence;
intended/accounted supported-file counts; exact terminal mode and message
excerpt; reported and enumerated distinct totals; and, for every site,
file:line, both operands, both semantic roles, changed-hunk intersection, and
classification. Counts must reconcile exactly. “Pre-existing” establishes
attribution, not safety. Put a compact terminal-mode/class/count/bead-comment
disclosure in the commit message; never call a nonzero known-false run
“passed.” Any other critical, uncertain role, or count mismatch blocks, as does
a missing site **wherever the tool emits per-site records at all**.

**Where the tool has no per-site record, this is satisfied at CLASS granularity
and must say so.** Measured for the rust module at UBS v5.3.7 (bead
`fln-7vzi`): the findings model is per-**class**, so criticals emit one record
carrying a class total plus a capped sample list, and no per-site object exists
in any format — text, `-v`, json, jsonl, toon, sarif, `--beads-jsonl`, or the
module's own emitter driven directly. The per-site clause is unsatisfiable
there **by construction, not by effort**, and a triage comment that omits it is
not thereby incomplete. Record instead: the tool version and the content hash
it was measured at; the per-class totals and the capped sample list **as
emitted**; that enumeration is unavailable at that version, named as such; and
the class-level reconciliation. Type the result `class-level`, never
`site-level`, and never write “every site reviewed” — a count taken from a
capped list is a **floor, not a census**. This is a declared remainder of
permitted shortfalls, so it is **one-way plus a floor**: a language/version
pair joins it only with the measurement showing enumeration unavailable, and
leaves when the tool grows a per-site record. Equality in both directions is
wrong here — it would make the tool *acquiring* the capability redden a correct
triage. Absent that measurement the per-site requirement stands unchanged; “the
tool is awkward” is not a measurement.

**That exemption is keyed to the ABSENCE of a capability, which is a shape this
repository has already watched rot.** Nothing fails on the day UBS grows
per-site records for rust: the allowance simply keeps excusing a clause the
tool could now satisfy, and it reads exactly as it did when it was true. UBS
lives outside this repository, so no check here can notice — which is why the
version belongs in the triage comment and not only in this paragraph. **Treat
any UBS version bump as expiring every `class-level` claim: re-measure the
format matrix before reusing one, and record the version you measured at.**
The recorded version is the only thing that makes staleness visible to the next
reader, and a `class-level` claim citing a version older than the installed
tool is inconclusive, not exempt.

`fln-lyc8` owns the exact class `Secret, signature, or token compared with
==/!=`. Its bounded UBS v5.3.7 measurement at
`dbc3e998b19cc8eb31e8245efc9870c8107786b5` found 126 sites and zero true
credential/signature comparisons. The implementable upstream narrowing
inspects only the two operand ASTs; matches exact normalized credential
components `secret`, `hmac`, `signature`, `api_key`, `csrf`, `bearer`, or
`reset_token` rather than file/scope taint or bare `token`; and excludes a
comparison when both operands are numeric or byte literals. It silences
**124/126 measured criticals and 0 measured true positives**. The two retained
semantic homonyms remain visible pending a sound type/role discriminator.
This is a bounded proposal, not a suppression or a claim about future bytes.

Parse `file:line:col` → location, 💡 → suggested fix. Fix root cause, not
symptom. Critical (always fix): memory safety, UB, data races. Important:
unwrap panics, resource leaks, overflow. Do not add `ubs:ignore`, broad
`.ubsignore`, category skips, or correctness-neutral source contortions to make
a known-false heuristic green.

---

## RCH — Remote Compilation Helper

RCH offloads `cargo build/test/clippy` to remote workers to avoid local compilation storms. Installed at `~/.local/bin/rch`, hooked into Claude Code's PreToolUse — usually transparent. Manual: `rch exec -- cargo build --release`. Health: `rch doctor`, `rch status`. Fails open (builds run locally if workers unavailable). **Codex/GPT users:** no auto-hook — manually `rch exec -- <cmd>` for heavy builds.

### The worker does not have the tracker — a beads-reading suite answers for a checkout that lacks it

The green-bar table above says where evidence may be taken from when the *tree* is wrong. This is the same defect one layer out: the **host** is wrong, the suite still runs, and the exit code is the one a real finding uses. Measured for bead `fln-y0f7`; the head, the rch version and the classifier numbers are in the block below, which is the single producer for every figure in this section:

- `~/.config/rch/config.toml`'s `exclude_patterns` holds **`.beads/` and `.beads/**`**, while `.beads/issues.jsonl` is **tracked** (`git ls-files .beads/` returns four paths). The worker's checkout is therefore missing a file the repository contains — not stale, absent.
- A suite that reads the tracker dies there with `No such file or directory` and **exits 101 — the same code libtest uses for a genuine assertion failure.** Both were hit on one command. **Judge from the message text; the exit status cannot separate them.**
- **It is not opt-in.** `rch diagnose -- cargo test -p fln-conformance --test ci_execution_join` classifies it `CargoTest` at a confidence at or above the interception threshold — both are in the block below — and prints `✓ WOULD INTERCEPT`. With the PreToolUse hook installed a plain `cargo test` is offloaded with nothing in the command saying so.
- **The dodge is the command line, not a flag** — the classifier matches the text it is given. A one-line wrapper (`exec cargo "$@"`) is not matched and runs locally. Bead `fln-y0f7` and the pin row in the gotchas list below both rely on this.

**The population, derived per commit and disclosed here because that is the half a broadcast cannot keep.** Every Rust file under `crates/` and `tools/` naming the tracker is counted, classified, and listed — the numbers and the members have one producer, this block, so prose can never drift from a count:

```text
rch-measured-at: head=c0f2ace5 rch=1.0.52 confidence=0.95 threshold=0.85
rch-tracker-population: mentions=9 non-reads=3 reads=6
rch-tracker-reads: crates/fln-conformance/src/naming.rs crates/fln-conformance/src/ownership.rs crates/fln-conformance/tests/ci_execution_join.rs crates/fln-conformance/tests/commit_anchor_reachability.rs tools/structure-guard/kernel-ownership-publisher/src/main.rs tools/structure-guard/tests/real_workspace.rs
rch-tracker-non-reads: crates/fln-conformance/tests/evidence_finalization.rs crates/fln-conformance/tests/vellum_surface_inventory.rs crates/fln-env/src/extensions.rs
```

**Discriminate on the read, never on the mention.** `vellum_surface_inventory.rs` compares a finding's path string and never opens the file; `evidence_finalization.rs` and `extensions.rs` name it only in prose. A count taken from a bare grep is the `mentions` figure, and that wrong one was published to this swarm once already.

`the_rch_tracker_exclusion_row_matches_the_measured_population` re-derives the population per commit and **fails the build** in both directions — a file that starts naming the tracker and is in neither list, and a listed member that has stopped naming it — and it also **refuses a scan** that came back empty or that walked implausibly few files, because a broken walk and a clean tree are the same green (`c0f2ace5`'s lesson, one section down).

**What this does not earn, stated because it is the load-bearing half.** `~/.config/rch/config.toml` is **outside the repository**, so no test here can hold the exclusion, the threshold, or the confidence — a version bump changes all three silently and nothing in this tree would notice. Those four cells are a measurement at one host at one instant, class `bounded_model`, and the version is recorded above precisely so the next reader can tell whether it still describes their machine. What *is* held per commit is the in-repo population that would be answered for by a worker without the file. Re-measure the rch half before relying on it, and record the version you measured at.

### The worker may lack a component of the pin — and for one gate that is indistinguishable from a finding

The tracker case above is the worker missing a **file**. This is the worker missing a **component of the toolchain**, and it reaches further, because one of the two gates it breaks reports the breakage in the shape of a code defect (bead `franken_lean-m3fq`).

`rust-toolchain.toml` declares `components = ["rustfmt", "clippy", "miri", "rust-src"]`. Those are components **of the pin**, not a second pin — a machine holding `nightly-2026-07-13` without `clippy` does not have this repository's toolchain. **Nothing verifies them.** `parse_rust_lock` in `scripts/evidence.py` is the sealed-cargo path's toolchain check and it reads `rust-toolchain.toml` for `channel` only, asserting it equals `SUITE.lock`'s `rust-nightly`; the `components` array is never read by anything. Locally rustup installs them from the same file, which is why this has never been felt on a developer machine — and is exactly why the remote case went four reproductions without a rule.

**Re-measured at rch 1.0.52 on 2026-07-27, and the exposure has grown.** `rch workers capabilities` reports `Rust : 1.99.0-nightly` per worker and inventories Bun, Node and npm — it does not inventory `clippy`, and it reports a *version* rather than the pinned *toolchain*, so it cannot distinguish a worker that lacks the component from one that has it, nor one on the pin from one on some other nightly. The fleet is **11 workers**; when this bead was filed there were 2. cod_1 reproduced the selection of a worker without `cargo-clippy` four times on 2026-07-25, each time after the full ~68-second sync had already been paid.

**The measured 2×2, which is the part that matters and was not in the bead.** A component-absent failure and a real finding are separable for one gate and not the other:

| gate | real code finding | component absent | `check.sh` registers | separable? |
|---|---|---|---|---|
| `cargo clippy --all-targets -- -D warnings` | **101** | **1** | `--semantic-failure-exit 101` | **yes** — an absent component is outside the semantic set, so it types `internal_fault`, never a stage failure |
| `cargo fmt --check` | **1** | **1** | `--semantic-failure-exit 1` | **no** — the environment fault and the finding are the same exit |

So the clippy gate already satisfies FL-INV-07 here, by a margin nobody had written down: **do not "simplify" that 101 to 1**, because that single edit would convert every environment fault on the clippy stage into a reported code defect. The fmt gate does not satisfy it, and that is an open defect of this repository rather than of RCH — now tracked as bead `franken_lean-fmt-gate-env-fault-as-finding-u4j7`, and recorded rather than repaired here because repairing it changes the gate's control flow and no full-gate `check.sh` verdict is obtainable while the two orphaned working-tree files stand (bead `franken_lean-h4o1`, which `u4j7` is filed as blocked on). **That bead exists because this disclosure was not enough.** The defect was measured on 2026-07-27 and deliberately left unfiled — creating a bead moves the id set and forces an ownership-projection regeneration in the same commit — so for one rotation it lived only as this paragraph, under a guard that kept it from vanishing silently but outside `br ready` and every triage. A guarded disclosure and a tracker entry are not substitutes: the first stops a fact from being lost, the second is what makes it schedulable.

> **A gate failure whose text says a component `is not installed` is an environment fault — FL-INV-07 `Inconclusive`, never a finding about the code.** Do not diagnose the repository, and do not retry until a worker answers, which is how an unattributed green gets adopted. Re-run pinned locally, or under `--base <sha> --clean-overlay`.

`the_pin_declares_components_and_the_gates_that_cannot_separate_them_are_disclosed` derives the component list from `rust-toolchain.toml` rather than transcribing it, and fails if the pin's components move without this section, if the clippy stage stops registering an exit outside the environment-fault code, or if the disclosure of the non-separable gate disappears.

**What this does not earn.** The RCH figures are one host at one instant, class `bounded_model`, and the capability surface is outside this repository — a version bump changes it silently. Nothing here verifies that a component is *present* before a gate consumes its verdict; what is held per commit is that the pin's declared components are disclosed and that the separable gate stays separable.

---

## ast-grep vs ripgrep vs warp_grep

- **`ast-grep`** when structure matters (refactors/codemods, policy checks, safe rewrites): `ast-grep run -l Rust -p '$X.unwrap()'`.
- **`ripgrep`** for raw text/literal hunts and pre-filtering.
- **`mcp__morph-mcp__warp_grep`** for exploratory "how does X work?" — an AI agent expands the query, reads files, returns line ranges with context. Don't use it to find a known symbol (use `rg`); don't use `rg` to understand architecture (use `warp_grep`).

---

## cass — Cross-Agent Session Search

`cass` indexes prior agent conversations so we can reuse solved problems. **Never run bare `cass` (TUI)** — always `--robot` or `--json`.

```bash
cass search "olean codec relocation" --robot --limit 5
cass view /path/to/session.jsonl -n 42 --json
```
stdout is data-only, stderr diagnostics, exit 0 = success. Treat it as a way to avoid re-solving problems other agents already handled.

---

## Subsystem Naming Contract (bead fln-7gr6)

The FrankenLean W4 parser/syntax/hygiene/macro subsystem is named **Vellum** (crates `fln-parse`, `fln-syntax` — crate names unchanged). The name "Quill" is reserved suite-wide for the Frankensearch lexical engine and is NOT a FrankenLean subsystem.

- The registry of every load-bearing codename is `ci/SUBSYSTEM_REGISTRY.txt` (schema `fln-subsystem-registry/1`): owner repo, scope, crates, aliases, status, with a case-insensitive collision law. Register new codenames there before using them; regeneration goes through a `.candidate` sibling and an atomic rename — a leftover candidate fails the gate typed.
- **Enforcement runs in plain `cargo test`** (fln-conformance suites `subsystem_name_registry`, `reserved_name_collision_model`, `vellum_surface_inventory`, `generated_name_drift_guard`): a reserved name in governed docs, source, ci artifacts, contracts, scripts, or **mutable bead fields** (title/description/acceptance_criteria/design/notes) fails the build unless the same line/field also names the owning project (e.g. "Quill" is legitimate only when Frankensearch is cited alongside it, as here). Immutable bead comments and `.br_history/` are exempt.
- The scanner's only file exemptions are the public `CONTRACT_DEFINITION_PATHS` list in `crates/fln-conformance/src/naming.rs` — never add a hidden exception.

---

## Evidence & Census Pins — Operational Gotchas

Hard-won facts that will bite you if unknown:

1. **Creating ANY new bead stales `ci/KERNEL_CONTRACT_OWNERSHIP.jsonl`** and fails the `kernel_contract` suite workspace-wide (`bead-evidence/stale-binding`). The file binds the sorted set of bead IDs (`DomainHasher(Fixture)`, tag `fln.kernel-contract-ownership.ids/1`, NUL, u64le-length-prefixed sorted ids; header carries `record_count` + `projection_hash`). After creating beads, regenerate the projection (a one-off regenerator against the crate's own algorithm byte-reproduces prior bindings — validate yours the same way) and commit it with your beads export.
2. **The kernel-admission census (`fln.e2e.kernel-admission`, version 2) moves only by bead**, and its pins must move together: the expected-rows array in `crates/fln-conformance/tests/kernel_replay.rs`, and `KERNEL_ADMISSION_CENSUS` / `KERNEL_ADMISSION_ARTIFACT_ROWS` / `KERNEL_ADMISSION_ARTIFACT_WITNESS` / `KERNEL_ADMISSION_VERSION` in `scripts/evidence.py`, plus the census needles in `scripts/e2e/kernel_replay.sh`. The witness digest recomputes via `fln_env::decl_closure::witness_digest` (tag `fln.artifact-incomplete-witness/2`; binds declaration, safety class, and missing refs). Version 2 binds the **structural** `Name` — component kinds and lengths — not its display form: `to_display_string` joins components with `.` without escaping and renders numeric and string components alike, so distinct names collided and the witness stopped discriminating (bead `franken_lean-f6br`). Note the witness *hex* is not itself a pin in `kernel_replay.rs` — that file recomputes it; only the census rows are pinned there.
3. **ArtifactIncomplete is an FL-INV-07 inconclusive-family outcome** (`fln_env::decl_closure`): a declaration whose serialized artifact cannot supply its dependency closure is never Accepted, never Rejected, never counted checked, never cacheable, and never enters an environment. Do not fold it into any success total; the validator enforces count conservation (`checked + artifact_incomplete == decls_total`).
4. **Writing a new `fln.e2e/2` lane**: model on `scripts/e2e/closure_audit.sh`; every `--wait-ms` for the process-identity guards is capped at **30000** (a larger value makes the guard raise instantly and the lane SIGKILLs its own runner with a bare "Killed"); every scenario MUST be registered with its exact ordered step list in `E2E_STEP_ORDERS` at the top of `scripts/evidence.py`; register the script in `scripts/check.sh` (INPUT_PATHS + shellcheck stage) and as a `.github/workflows/ci.yml` step (new e2e steps must also join the verify-step's `expected_roots` set and `specs` tuple — the roots set is closed). Expected-fail cargo steps use `--semantic-failure-exit 101` and must grep BOTH `.out` and `.err` captures for the intended reason (libtest panics print to stderr under `--nocapture`).
5. **While an e2e lane holds the gate lock, change NOTHING inside the repository** — see [The Build Gate](#the-build-gate--while-a-lane-runs-the-repository-is-frozen) above for the mechanism and the full rule. Stated here only because this is the list people read: `INPUT_PATHS` (`scripts/check.sh:179`) governs `governed_inputs_changed` and is a *path list*; the freeze that ends a lane is `repository_state()` and is *path-agnostic*. **During a lane, every tracked file is effectively a governed input.** Reading only the path list is how "I checked, my file wasn't on it" kills a run — item 7's defect family one floor down, two artifacts with neither naming the other. **This entry used to add "…and does not include `AGENTS.md`", which was true of `check.sh` and read by three people as true of lanes.** It is not: `scripts/e2e/vellum_naming_no_mock_e2e.sh` governs `AGENTS.md`, `README.md` and the plan, so for that lane an *uncommitted* edit to this file is enough. There is no single path list to check — each lane declares its own and thirteen of the twenty-one declare none.
6. **The pinned Reference toolchain** lives at `~/.elan/toolchains/leanprover--lean4---v4.32.0/` (install with `elan toolchain install leanprover/lean4:v4.32.0` if absent; the kernel-replay suites SKIP typed without it). RCH remote workers do NOT have it — run pin-dependent tests locally (a small wrapper script avoids the RCH cargo hook). Lanes longer than the 10-minute tool timeout should be launched detached (`setsid nohup … &`) and watched.
7. **The recurring defect: evidence must be produced where the claim is made.** Stated once, generally, because it has now been found eleven times and every single time by somebody *reading carefully* rather than by a check:

   > Every level, digest, capture and delegation must **name the thing that produces it**, and must **fail when that thing changes**.

   The reason it keeps recurring is that the claim is always *locally* consistent. The gap lives in the **join** between a claim and its evidence, so no single artifact reads as wrong and no single-artifact review can find it. When stating a claim's evidence requires two artifacts, the join between them needs its own check.

   The twelve, with the join that was unwatched — and, more usefully, whether anything would catch a recurrence:

   | instance | the unwatched join | caught by |
   |---|---|---|
   | `franken_lean-4o3n` | a bound and the configuration it was measured in | **mechanism** — `Calibration` is a private field so no bound can exist without provenance; `Comparability::establish` refuses mismatched configurations; the always-on descent guards falsify the measurement in the direction that aborts |
   | `franken_lean-pnav` | an assertion and the lane it delegates to | **mechanism** — `contract_roots.rs` asserts the lane exists, still invokes `--check`, **and is named by `scripts/check.sh`**, with a negative control. Registration is the part that matters: a script can sit in the tree unrun for months |
   | `fln-parity-ledger-l2-pinned-source-qydn` | a level and the oracle that produced it | **mechanism** — `validate_level_is_supported_by_its_oracle`; the thirteen known violations are declared, so the fourteenth fails, and the allowance is checked in both directions so it shrinks with each repair |
   | `franken_lean-ext-observable-fixture-drift-gap-vqnu` | a capture and the pin it came from | **mechanism** — `ext_observable_capture.rs` re-derives from the pinned binary on every run (~1.6 s) |
   | `franken_lean-parity-ledger-l2-definition-split-kl4h` | a term and the document that defines it | **partly** — the Witness row fails if *either* definition moves, but the standing contradiction is `Acknowledged` and green. Movement is mechanised; the state is not |
   | `fln-8zsq` | a census and the claim class it supports | **mechanism** — `corpus_census_keeps_disclosing_its_claim_class` reads the source and fails if either census's SUMMARY row drops its inline class, if a CLAIM-CLASS row loses its `means=`, its cadence or the lane it points at, if the module doc stops scoping the per-commit matrix to the Prelude, or if a class token drifts outside the allowance the file's own code earns — checked as an exact token, in both directions, and against the code in that census's own region. It had to be **source**-level: both censuses are printed by `#[ignore]`d tests, so a stdout grep sees silence, not a missing disclosure |
   | `fln-mandated-mutant-join-unwatched-uagk` | a mandated mutant and the test that kills it | **mechanism** — `mandated_mutants.rs` derives §18's five names from AGENTS.md at test time rather than transcribing them, and now closes *both* joins. List→marker fails four ways: a name neither marked nor declared not-yet-seeded; a not-yet-seeded declaration whose crate has stopped being a stub, which is the reminder firing at the moment the subsystem lands; a declaration that outlived its own repair, so the remainder shrinks; and a scan that returns empty, which is a broken scan rather than a clean tree. Marker→**kill** is a campaign that plants each seedable mutant and requires the *named* killers to die *for the stated reason* — measured live, skipping the positivity check still leaves the bad block rejected, for "block declares 0 recursors", so a rig accepting any non-zero exit would have scored it killed by a test that had stopped testing positivity — plus a per-commit receipt keyed by a digest over the mutated site and the killer bodies, so gutting a marked test expires the recorded kill mechanically. Four mutants planted against the mechanism itself, all killed; the sharpest is gutting a marked killer, which leaves the test passing and the marker intact, makes the mutant *survive*, and is exactly what the marker-only guard stayed green on. **What it does not earn:** a campaign run is one measurement at one commit on one host, class `bounded_model`; what runs per commit is the *retention* check — the recorded kill still describes this tree — not the run. A weekly dispatcher now exists (`.github/workflows/mandated-mutants.yml`), and the receipt's `class` token is **derived** from what actually dispatches the campaign rather than transcribed, so a cadence claim cannot outlive the thing producing it: deleting the workflow, dropping its cron, or dropping `--ignored` — which would make the libtest filter match nothing and *exit 0*, a lane green forever while running no campaign — each turn the recorded rows into a claim with no producer and redden the per-commit suite. Five mutants planted against that join, all killed, one of them at a different assertion because an empty workflow scan is refused as a broken scan rather than reported as no cadence. **What the cron still does not buy:** any evidence a scheduled run *happened*. The token records the cadence that is configured, not one that fired, and a cron GitHub silently disables is invisible from inside the repo (bead `fln-mandated-mutant-join-unwatched-uagk`, commits `0f2dbc70` and `505ac423`) |
   | `fln-bench-apparatus-empty-referent-bkw6` | a claim and an apparatus with **no instances** — the *empty-referent* shape, where there is nothing on the far end to join to | **mechanism** — the claim is bound to the **cardinality** of what it asserts: `the_bench_apparatus_disclosure_matches_the_measured_inventory` resolves the workspace's own `members` globs and fails whenever the disclosed count and the measured count disagree, in either direction; claim row `PERF-GATE-BENCH-APPARATUS` is `Enforced` so the overclaim cannot return, and its citation keeps the replacement disclosure present. This one is worth reading for *why it was invisible*: every other row here is a claim whose evidence **exists** with the join unwatched, so all the techniques above check that a claim still matches its evidence — and there was no evidence object to compare against. What finds it is asking whether the thing a sentence says exists, exists. Two traps were live: a hand-listed scope picks up twelve throwaway fixture manifests under `scripts/e2e/artifacts/`, and counting only `[[bench]]` sections is a false clean because cargo auto-discovers `benches/*.rs` with no manifest section at all. Five planted mutants, including that one, were each confirmed to die |
   | `franken_lean-worktree-gitdir-refusal-hugg` | a **verification practice** and the gates it cannot actually run — the *hollow-green* shape, where the claim is "verified" and the far end never executed | **mechanism, with its scope still hand-listed** — `the_evidence_surface_refuses_a_gitdir_pointer_root` builds a root whose `.git` is a gitdir pointer, asserts the real refusal, and requires the AGENTS.md green-bar section to keep naming the surfaces it takes down; five mutants killed, including relaxing the refusal, dropping one surface from the table, and defeating the probe's own control. **Two properties make this one worth reading.** First, the exit code is *not* the discriminator: a root whose `.git` is a real directory also exits 2, because git then runs and fails on its own terms, so only the file/directory distinction separates a genuine refusal from a mistyped probe — a rig checking "non-zero" would have passed with no content. Second, and the reason it survived so long, **the failure actively misdirects**: `check.sh` reports that it cannot inventory UBS inputs, a lane that it cannot hash governed inputs, seven lanes that they cannot verify the pinned Reference tree. Three wrong causes are asserted loudly above one correct line on stderr. Nobody misread anything. **What it does not earn:** the affected-surface list is written down, not derived — static reachability is provably wrong here, since `hash-tree` reaches `run_git` yet succeeds without `--vendor-path` — so a *new* lane that starts refusing would go unnamed and nothing would notice. And the misdirection is now **half** fixed: `run_git` names the worktree condition as of `cc9ecf0f` (2026-07-26), verified in a real linked worktree at `e4219404` and held per commit by `the_evidence_surface_refuses_a_real_linked_worktree_whose_pointer_resolves` as of `cd3e203e` — a pointer **git itself wrote**, resolving to a gitdir that **exists**, where the fixture sibling writes a pointer to a nonexistent target and so would be satisfied by a refusal keyed on the target being absent. The other two wrong causes this row names are untouched, and the sentence that used to stand here predicted its own retirement and then outlived the repair by a day, which is this table's defect arriving inside this table's own row |
   | `fln-history-rewrite-evidence-anchor-reachability-vdi4` | a recorded verification and the commit it names, after a history rewrite silently changed every hash | **partly — the classifier/fixture join is watched; the repository-wide population is not.** Plain `cargo test` reaches `golden_vellum.rs`: `the_checked_in_producer_anchor_is_reachable_from_main` refuses a mutable Vellum producer that is not an ancestor of `refs/heads/main`, and `rewritten_history_separates_current_backup_only_and_unresolved_anchors` keeps an old real commit alive under both `refs/original/refs/heads/main` and `pre-filter-branch-backup` while proving that only `merge-base --is-ancestor` distinguishes it from current evidence. An existence-only mutant was killed at that backup-only assertion, so classification drift and the R5 trap now fail per commit. **That is not the systemic guard this row originally asked for.** `scan_evidence_file` is invoked only on the temporary fixture's `anchors.txt` and on a missing-path refusal; no tracked test scans `.beads/issues.jsonl`, the verification manifest, AGENTS.md, README, the plan, `ci/`, `crates/`, `scripts/`, and `tools/`, and no declared unreachable-anchor allowance is checked in either direction. Re-audited and manually re-measured at stable `2f9112f74bb2ea77dc2e1ddebff02aff3aaabc1b`: 563 commit-anchor tokens across 327 tracked scoped files = 397 main-reachable + **166 local-backup-only**, with zero ancestry-indeterminate; the original **166 of 411** at `14bbbe7f` is historical. The 2026-07-25 `filter-branch` did not make those anchors wrong; it made them unverifiable from `main`, while local backup refs still make a naive existence check pass. Because the census and its population are not a per-commit producer, a hundred more backup-only anchors would still not fail the build. The close earned R2/R5 classification and seeded controls, not corpus-wide retention |
   | `fln-cross-tree-baked-root-k60n` | a verdict and the **checkout that produced it** — a test binary compiled in one tree answers for that tree, and says so nowhere | **mechanism, over part of the workspace, and the part is measured rather than claimed** — `crates/fln-conformance/src/tree_identity.rs`. `CARGO_TARGET_DIR` is shared machine-wide here, `env!("CARGO_MANIFEST_DIR")` is a **compile-time** constant, and cargo treats a test binary built from an identical-bytes copy of the same package in another tree as *fresh*, rebuilding nothing and saying nothing. `checked_workspace_root!()` compares the baked value against the one cargo puts in the **process environment** — exact, and independent of the working directory — and refuses, naming both paths. Macros rather than functions: measured, a `macro_rules!` body expands `env!` in the *calling* crate and a plain function captures its own, and lib and test targets are cached separately so they can come from different trees. Observed live at `5c5ada4b`: `structure-guard`'s `real_workspace` binary carried `/data/tmp/wt-cc_2`, so the same command reported `PASS` here and `INCONCLUSIVE` there at the same instant, citing a symlink defect on a path that is a regular file in the tree the reader is standing in — `hugg`'s misdirection exactly. **The direction that matters is the one not currently firing:** today the bake tree is the dirtier one, so the result is a loud false red; swap which tree is dirty and the identical mechanism yields a **false green**, a suite reporting *structurally clean* about a repository that is not the one under test. **What it does not earn:** detection is not prevention — the clean fix is a per-tree target directory, a machine-level disk cap that is not this repository's to change — and the refusal only protects the crates that *call* it. **How much that is, is no longer prose here.** This row said "8 sites in `tools/structure-guard`" while `2a96e7b9` had already taken one of those files from 7 raw sites to 9, and the conversion below then took it to 0: a claim and the population it counts, unjoined, inside the section that exists to name that defect, and nothing would have said so. Every number that follows is now re-derived from `git ls-files` per commit by `tree_identity`'s `the_k60n_coverage_disclosure_matches_the_measured_populations`, which fails when the tree moves without this row **and** when this row moves without the tree — one-way would let a repair silently overstate coverage — refuses a reworded, doubled or digit-less phrase as a *vacuous* comparison rather than a passing one, refuses a raw site belonging to no population named here, and refuses if it cannot locate exactly one such row. Measured, and note which numbers are floors and which are exact, because the first version of this row made them all exact and that reddened the workspace twice in an hour for the *good* event — a rig being converted, which grows the protected count, is a repair and must not be a wall (`RAW_SITE_RESIDUE`'s own rule: "reverse membership is a wall that reddens a correct repair"). The **protected** figures are lower bounds that may grow freely and may not shrink; the **unprotected** ones are exact in both directions, because silent growth there is the defect this bead exists for. So: at least 41 checked invocation sites in at least 2 crates outside the defining module; 0 raw sites in tools/structure-guard; 19 unprotected sites across 9 product crates; 1 unprotected site in tribunal/epoch-lab; 4 raw sites in the defining module itself, being the two macro definitions and the two unit tests that feed the compile-time value in as known-good input. `tools/structure-guard` was the population blocked by **one line** — `FLN-STRUCT-007` exempts `kind=tool` crates from layering outright (`checks.rs:1948`), so it needed a dev-dependency plus one acknowledged edge and nothing else — and it is converted, with its residue rows *deleted* rather than zeroed, because a retained row keeps its slot and that path could then regress up to its old count silently. **This row gave two reasons for what remained, and `839ff2ec` measured one of them BACKWARDS** — it named as the blocker the very property that was the way in, which is worse than a missing reason because every reader downstream inherits it and stops looking. It said `tribunal/epoch-lab` was unreachable *because it is a nested workspace the members glob never walks*. Nested-ness is exactly why it **was** reachable: outside the graph means **no layering law governs it**, it already path-depends into the product workspace (`fln-hash`), and it owns its own `Cargo.lock`, so a `dev-dependency` on `fln-conformance` added **no governance row and did not touch the root lock** — the pair of concerns that crate's own manifest comment raises. Converted, **11 sites to 1**. `bkw6`'s shape still applies and in the sharper direction: a scope you never walk is one you also never *check*. The single site left is `src/main.rs`, a **bin** target a dev-dependency cannot reach, so converting it means a normal dependency putting a rank-22 crate in that binary's runtime closure — a different blocker, not a leftover. The second reason was *overstated* rather than inverted: the nine product-crate members are blocked by a **decision about where the check lives**, not by an architectural impossibility. `fln-conformance` is rank 22 so a dev-dependency from below is genuinely an upward edge — but `fln-core` is **rank 0**, every one of those crates sits above it, and **five of the eight already declare that edge**, so they are convertible with no graph change at all and only `fln-rt`, `fln-unsafe-region` and `fln-checker` need one (`fln-checker`'s also touching the §8 allowlist). The block is on the macro's **address**; it is routed to the graph's owner, not fixed here |
   | `fln-ysvo` | a bead's **mutable summary** and the immutable comment log beneath it — and `br show` prints the summary *above* the log, so a reader who starts at the top believes the stale half | **nothing — and this is the first row here whose join is measured *unbindable* rather than merely unwatched.** Four candidate joins were priced and each fails for a **different** measured reason, which is what makes that a finding rather than a shrug. **A**, an out-of-tree referent: 4 beads cite a routing-store path in notes, **11 citations, 11 of 11 outside the repository, 0 missing on this host** — decorative here, and on CI or an rch worker every referent is absent so it fails for the *environment* rather than for the claim, `hugg`'s class exactly. **B**, a near-empty population: comment-id citations reach **4 beads of 400, 12 citations, 0 true dangling**, and the check caught **0 of the 3** instances that prompted the bead; its first version reported one dangling and *checking it dissolved it* — the citation was cross-bead and named its own bead — so a naive implementation would have reddened the workspace on a **correct** citation. **C**, absent from the data model: the record carries `created_at` and `updated_at` and **no per-field timestamp**, and `updated_at` moves on comment-add, so it cannot separate "notes edited" from "comment added". **D**, a saturated proxy: over the most recent 120 of **518** beads commits, **153 comment-adds, 20 carrying a same-commit notes edit, 133 not (86%)**, and narrowing by correction vocabulary excludes only **18** of those — a gate firing on 133 of 153 events reddens nearly every beads commit, the cry-wolf failure this file already measured when the enforcement census drifted 26 → 27 → 28. **The unifying reason is the finding**: the predicate that matters is *semantic*, and D is saturated **because the practice is good** — this project writes corrections into comments as house style, so the corpus is adversarial to its own detector, and a team with a clean signal here would have a worse process. Figures **re-derived at `075a84db`** rather than transcribed, and they had moved: the bead's own `c45e041b` numbers read 2 beads and 8 citations for B, and 143 events for D. D's marker count is a property of a hand-chosen vocabulary, so it is not comparable across the two runs — but two independently chosen lists both saturate, which is worth more than either alone. **What would change the answer**, named so this is falsifiable and not a closed door: a per-field timestamp or field-level history in `br` makes C real; moving the routing store inside the repository makes A runnable off this host; and removing the duplication, so the summary *points at* comments instead of restating them, is the only candidate that attacks the cause rather than guarding it |

   **Where the luck is still load-bearing.** Nine of the twelve now fail on recurrence; two are partial; and one is wholly unwatched — **this sentence ended "none is wholly unwatched" until `fln-ysvo` was added, and that is no longer true.** It is not unwatched for want of trying: four joins were priced and each *measured* to fail, so the honest state is a row with no mechanism and a recorded reason why none of the obvious ones works. A negative row is worth its slot precisely because the next reader would otherwise re-derive it. **This sentence and its neighbour above spent a day disagreeing with the table between them** — the list read "The nine" while ten rows sat under it, because a row was added and only two of the places that state this section's own cardinality were moved. **There are four, not the three that sentence assumed, and adding `fln-ysvo` moved all four**: the line introducing the table, the two in this paragraph, and the "a thirteenth is already filed" line below. Counting them was the first step of adding a row, and the count was wrong before it was counted — which is this paragraph's own lesson arriving one layer down. That is a claim and the population it counts, unjoined, inside the section about claims and the evidence they count, and nothing would have said so; it is fixed here by hand and remains unmechanised. `kl4h`'s movement is mechanised but the contradiction's `Acknowledged` status is not. `uagk` closed its second half: the marker→kill join is now watched per commit by a receipt that expires when either the mutated site or a killer body moves, and the campaign behind it was itself attacked with four planted mutants before being believed. Its cadence half is now half-closed and worth reading for which half: the retention check forces a re-run exactly when the code changes, a weekly workflow dispatches it when the code does *not*, and the receipt's class token is derived from that dispatcher in both directions so neither can move alone. What is still missing is the **observation that a run occurred** — nothing inside the repo can tell a cron that fired from one GitHub quietly disabled, so the token attests a configured cadence, never a kept one, and each run is still one measurement at one commit on one host. `vdi4` closed the classifier/fixture half: per-commit tests now catch main-reachability classification drift and the existence-only trap, but its 166-anchor population remains a manual census, and no per-commit repository-wide scan or bidirectional allowance would notice a hundred more. `k60n` is mechanised over one crate of nine and discloses which. Everywhere else the mechanism, not the reviewer, is doing the work. Twelve instances found by attentive reading is not a mechanism; it is luck with good people, and luck does not survive a context restart. `hugg` is the sharpest argument for that sentence: the practice it invalidated had been corrected by broadcast three times in one day, and broadcasts do not survive a pane restart, which is why the correction is in this file and held there by a test.

   **Two of these rows differ in a way worth keeping.** `bkw6` is a claim whose referent **never existed**; `vdi4` is a claim whose referent **existed and was destroyed wholesale by a tool**. Both defeat the same technique for the same reason — there is nothing addressable to compare a claim against — and neither is reachable by reading one artifact more carefully. The generalisable move is the one `bkw6` used: when the far end is empty or gone, bind the claim to the **cardinality** of what it asserts, and let the number fail in both directions. `hugg` adds a third variant: a referent that **exists and is addressable, but was never reached** — the tooling refused before it ran, and said so in words that named something else. Where a claim rests on a run, check that the run *happened*, not merely that the command was issued and the exit code looked right.

   **`k60n` sharpens that rule rather than repeating it, and the sharpening was paid for.** Binding a claim to the cardinality of what it asserts is right; *which* cardinality decides whether it works. `k60n`'s coverage claim was first bound to **one aggregate count** over the whole workspace — derived from `git ls-files` rather than hand-listed, failing in the growth direction, everything the rule above asks for. It is still a **budget**, because a sum over many members is refilled by its own repairs. Measured over the 70 commits from `d40f0c0b` to `017000f0`: one conversion took the total from 44 to 38 and opened eight slots, and four new unprotected rigs then landed in four separate commits in four different crates — `b241943d`, `6e7531e6`, `1b0a9eb1`, `8391bafd` — every one of them under a guard that was green the whole time, because the total never came back to 46. The replacement declares a count **per member**, so a repair frees a slot only in the file that earned it and a new file has no slot at all; against it all four refuse and are *named*, three as undeclared files and one as growth inside a declared one — a distinction a membership-only check could not draw either. **Bind to the cardinality of each member, not to the cardinality of the population.** Two things about this are worth more than the repair: the guard that admitted those four *was itself* the mechanism for an instance in this table, so a row here is not evidence that its own shape is sound; and while fixing it, the floor on protected sites turned out to be partly satisfied by the module's **own failure messages**, which name `checked_workspace_root!()` as the repair and so matched its own needle — `fln-8zsq`'s lesson recurring inside a later instance's fix, and a reminder that a scanner's prose belongs outside any count it floors.

   **A standing habit because `vdi4` closed only the classifier/fixture half:** whenever you re-derive a measurement, record the hash you re-derived it **at**. A fresh anchor costs one `git rev-parse` and is the only thing stopping the next reader from being stranded the way this section's own examples now strand one. Re-anchoring on touch will not converge by itself — it is what keeps a manual measurement attributable while the population remains unmechanised.

   **Two things `fln-8zsq`'s repair taught, both worth more than the repair.** First, *the guard's own text is inside its search space*. The first version asserted the qualifier appeared **somewhere** in the file; a planted mutant that gutted the SUMMARY row survived, because the standalone CLAIM-CLASS row satisfied the check — the identical wrong-scope shape the bead was about, reproduced inside its own fix and caught only because the mutant was planted. Scope an assertion to the **site** that must carry the evidence, never to the file. Second, a source-reading guard must exclude **every guard body, not merely its own**. Excluding only itself is not enough and the correction cost a third instance: `franken_lean-2ki4`'s guard probes whether the corpus is still single-width by looking for the size-heuristic literal — which also appears inside the `fln-8zsq` guard's *assertion*, so the probe reported the production heuristic present after it had been deleted, and demanded a qualifier that had become false. Cut the search region at the **first** source-reading guard, so only production code is in scope. When self-exclusion is removed entirely the failure is *loud* (the guard refuses on a clean tree), which is the correct direction for a check that cannot decide.

   **What this does not earn:** mechanising a disclosure does not upgrade the claim it discloses. That real evidence — a `{1, 8, 32}` corpus run comparing stream digests at an explicitly pinned width — was built and run separately (`fln-corpus-thread-matrix-93te`), and it moved corpus schedule-independence from *inferred* to **one observation, still not a measured invariant**: the lane runs on demand, so PG-5's per-commit gate stays a documented shortfall. Note which half each bead earned. `fln-8zsq` and `franken_lean-2ki4` closed on the disclosure and bought nothing about the corpus; `93te` bought a bounded observation about the corpus and nothing about cadence. Neither is the invariant, and stacking them does not make one.

   A thirteenth is already filed and deliberately unmechanised: `fln-term-plane-population-differential-wv4u` carries constraints R1–R4 as *prose in a bead*, on a rig nobody has started. Its own R4 says the enforcement law must land **with** the rig rather than after it — which is this rule applied to a claim that does not exist yet.

   **This file's own enforcement claims are now counted, by a producer in the repository** (bead `franken_lean-pfei` R1). AGENTS.md is the densest source of unbound enforcement claims here, and four of its claims were measured false in two days — so the population is derived per commit rather than described:

   ```text
   enforcement-census: live=32 bound=16 unbound=16 catalogued=14
   ```

   `scripts/agents_enforcement_census.py --check` derives it and refuses any disagreement **in either direction**, so a new unbound claim raises the number and its author must say so, while a repair lowers it. `the_agents_enforcement_census_matches_the_file_it_describes` runs it under plain `cargo test`.

   **Read `bound` as "names a candidate referent in the same sentence" — never as "verified".** A sentence citing a deleted test still counts as bound; making the producer *denote* is pfei R2 and is not built.

   **The 29 → 30 movement is the `fln-qpkj` write-path guard, disclosed here as its author, and getting it counted took four attempts that are themselves the finding.** "Same sentence" is implemented as **same physical line**, and this file is hard-wrapped, so the same claim in the same words was scored three different ways by nothing but typography: `is **refused**` does not match while `is refused` does, because markdown emphasis breaks the verb; `refuses on any mismatch` does not match while `refuses any mismatch` does; and a wrap falling between `refuses any` and `mismatch`, or between a claim and its producer, silently converts counted→uncounted and bound→unbound. So `live` under-counts wherever this file's own emphasis habit meets an enforcement verb, and `bound` under-counts wherever a paragraph wraps in the wrong place — **both in addition to the over-count** the burstiness row above records, where a disclaimer matched on a positive verb phrase inside a negative sentence. Read the pair as **upper bounds with unstable margins in both directions**, not as a conservative estimate. Narrowing the verb set to exclude negated subjects would move the over-counted member but also delete the three deliberate `nothing holds|watches|binds` members, so it is not a pure narrowing and needs a decision rather than a patch (measured by cc_3 at `7b5dd549`; routed to the census's owner rather than repaired here, since the scan is not this pane's file).

   **The 27 → 28 movement on 2026-07-27 is disclosed here with its reason, because the reason is a limit of the scan rather than of the sentence.** The new member is the coverage-row obligation added to the judgement-row section, and it *does* name its producer in plain English — the verification-coverage-guard living in the pre-commit hook. The scan cannot see it: `test-fn` requires a closing backtick immediately after the token, so a backticked **path** never matches, and `source-file` requires one of seven file **extensions**, which an extensionless executable hook does not have. So the member is genuinely unbound *by this scan's definition* while naming its producer to any reader, and the number was raised rather than the sentence reworded — softening the sentence to go green is pfei R5 and is the one move this census exists to make expensive. Two consequences worth keeping: the unbound figure is an **upper bound** on real unboundedness, not a count of unnamed producers; and extending the pattern set to recognise extensionless hook paths would move this member without any prose changing, which is a repair someone should make deliberately rather than discover as drift.

   **The 28 → 29 movement, same day, is the mirror image and sharpens what `live` counts.** That member is a **disclaimer**: the burstiness section's "nothing mechanises any of it — no check samples anything or refuses a projection." Its entire content is that no mechanism exists, and the scan scores it an enforcement claim because it matches the verb `refuses a projection`; it then scores it **bound** because the same sentence carries the backticked token `bounded_model`, read as a `test-fn` producer when it is a claim class. So `live` over-counts in a direction the paragraph above does not name: not only claims whose producer the scan cannot see, but sentences that assert no mechanism at all. The number was raised rather than the sentence reworded, for the same reason as before — and note that rewording here would have been *cheap and undetectable*, since a disclaimer can be phrased a dozen ways, which is exactly why the rule has to bite hardest where softening looks harmless. **Read `live` as an upper bound on enforcement claims, exactly as `unbound` is an upper bound on unbound ones.** Narrowing the verb set to exclude sentences whose subject is a negation would move this member with no prose changing — the same deliberate repair the paragraph above describes, in the other direction.

   **The 30 → 31 movement is a THIRD sub-shape, and naming it is the point: the new member is a sentence about what this DOCUMENT records, not about any mechanism.** It is the opening line of the worktree-admissibility decision above — *"Everything above records that the evidence surface refuses a linked worktree"* — whose subject is this file's own prose. The scan scores it live on the embedded verb phrase `refuses a linked` and finds no producer, so it lands **unbound**, and it is genuinely unbound *by the scan's definition* while asserting no mechanism to anybody reading it. So the over-count now has three known causes rather than two: a claim whose producer the scan cannot see (27 → 28), a disclaimer asserting that no mechanism exists (28 → 29), and now a **meta-sentence describing the document**. The number was raised rather than the sentence reworded — and rewording was especially cheap here, since the sentence is scaffolding and a dozen phrasings carry the same meaning, which is exactly the condition under which pfei R5 is tempting. **This also sharpens what was routed to this census's owner and is recorded here rather than left in a scratch file:** two disclaimers landing the same day were scored oppositely, and the deliberate `nothing holds|watches|binds` members are negative by construction, so "exclude negative subjects" is not a pure narrowing — it would delete an intended class. A third sub-shape whose subject is neither positive nor negative but *metatextual* is not reached by that proposal at all, which is one more reason the repair needs a decision rather than a patch.

   **The 31 → 32 movement is the first one that is a REPAIR rather than a disclosure of a limit, and it moves `bound` with it — 15 → 16, leaving `unbound` unchanged at 16.** Every movement recorded above added a member the scan could not see correctly, or a sentence asserting no mechanism at all; this one adds a sentence that asserts a mechanism which *exists*, names it in the same sentence, and is new because the mechanism is new: the line-citation guard now refuses a range and checks a site where the needle recurs, closing a tolerance measured at up to 50 lines. That is the direction this census is supposed to make cheap — the number rose and its author is saying so here, exactly as R3 requires, and going green by softening the sentence instead would have been pfei R5. Note what did **not** move: `unbound` is flat at 16, so nothing was added that names no producer. **`catalogued` did move, 13 → 14, and the first draft of this very sentence claimed it was flat — measured false before it landed.** This paragraph sits inside the excluded region and carries enforcement verbs, so it is counted as *catalogued*; that is the exclusion working exactly as intended, since it kept `live` from being inflated by a paragraph whose only subject is the census itself. A disclosure that changes the number it discloses is this section's own recursion, and the honest form is to state both movements rather than the flattering one.

   **The number that governs is the one with item 7's own table excluded, and that distinction inverted the answer once.** The catalogue above quotes every phrase the scan searches for, because quoting them is what the rows are *for*. The first version of this census declared that exclusion in a constant and never applied it, and the resulting figure moved 26 → 27 → 28 across three commits — re-anchored each time as evidence that a count of claims is itself a claim — while **the live population never moved from 22**. Every one of those movements was a catalogue row. A count bound to the unfiltered figure would have reddened on exactly the commits that record good work, and been ignored within a week. The scan now **fails** if it cannot locate the region, or if the region excludes nothing.

---

## The document's own line citations (bead `franken_lean-pfei`, R2)

A line number is a claim about *where* something is, and it rots the moment anyone inserts a line above it. This file carried **12** of them and nothing checked one. Measured at `c0f2ace5`: all twelve resolved to a real file at an in-range line — the existence check passes 12/12 — and **eight pointed at code that does not support the sentence citing them**. Every one of the eight was correct **when it was written**. The four reaching into `tools/structure-guard/src/checks.rs` had each drifted by exactly **+40**, from two commits inserting above line 1488.

**The same insertion rotted a citation in two documents, and only one of them said so.** `2a96e7b9` moved `FLN-STRUCT-037` in `fln-checker`'s charter from line 983 to 1014; that went red within hours and was repaired at `740947ed`, because the charter carries a citation registry and `crates/fln-checker/tests/charter_citations.rs` parses it. The identical drift here stayed invisible. So this is not a new mechanism — it is the one this repository already proved, applied to the file that teaches item 7.

```text
cite tools/structure-guard/src/checks.rs:1591 :: constitutional prohibition
cite tools/structure-guard/src/checks.rs:1842 :: let mut actual_edges
cite tools/structure-guard/src/checks.rs:1948 :: (CrateKind::Tool, _)
cite tools/structure-guard/src/checks.rs:1999 :: code: "FLN-STRUCT-008"
cite tools/structure-guard/src/boundary_api.rs:109 :: fields.iter().any(|f| f.is_empty())
cite tools/structure-guard/tests/real_workspace.rs:51 :: fn real_workspace_is_structurally_clean
cite tools/structure-guard/tests/seeded.rs:253 :: fn prohibited_transitive_path_is_flagged
cite ci/BOUNDARY_API.txt:13 :: no-admission ground
cite scripts/check.sh:179 :: INPUT_PATHS=(
cite scripts/e2e/vellum_naming_no_mock_e2e.sh:83 :: INPUT_PATHS=(
cite scripts/evidence.py:1500 :: def stable_symlink_facts
```

`crates/fln-conformance/tests/agents_enforcement_census.rs` **fails the build** on any disagreement, in both directions plus conservation: every row's cited region must still contain its named construct; every `path:line` in the prose must have a row, so a new citation cannot be added unbound; and every row must be cited by the prose, so a row cannot outlive the sentence it served. A citation that deliberately names a **past** state is marked `(historical)` and excluded — which is how the `ApiRow` range in D3's paragraph, describing that struct before field 4 was retained, stays in the narrative without claiming to be current.

**What this does not earn.** The construct is matched as a substring of the cited region: it establishes that the region still holds the named text, never that the sentence's argument about it is sound. And the construct is *named* rather than inferred because inference was tried first and failed in **both** directions — scoring each region against the backticked tokens of its own sentence passed the `FLN-STRUCT-008` citation, which was wrong, and failed the `seeded.rs` one, which was right.

**And substring-of-a-region under-reports drift itself, which is measured rather than reasoned.** `0f2ae0ba` inserted 45 lines at `checks.rs:247` (historical) — the hunk's position in that commit's diff, not a construct anyone should track, so **all four** of this file's `checks.rs` citations drifted by exactly +45 — one defect, one commit. The guard reddened on **two**. `FLN-STRUCT-024` occurs eight times in that file and its 25-line region caught a *different* occurrence after the shift (1543 before, 1529 and 1536 after); `let mut actual_edges` occurs once, but its region is 51 lines wide and absorbed a 45-line shift (1797 → 1842, still inside `1797-1847`). Both passed while pointing at the wrong place. So the failure mode is not only "the argument is unchecked" — a **wide** region or a **recurring** needle silently tolerates real movement, and the tolerance is the region width minus the shift. Two consequences: when one citation into a file reddens, re-derive **every** citation into that file rather than repairing the one that shouted, which is how all four were caught here; and prefer a narrow region and a needle that occurs once, because precision here is not tidiness but the difference between a citation that denotes and one that merely resolves.

**That tolerance is now CLOSED, and the measurement that decided HOW is the point of this paragraph.** The sentence standing here used to end "the guard's green is itself a claim with a tolerance, and nothing states that tolerance but this paragraph" — true when written, and a disclosure is not a repair. Measured over the whole registry at `b58d0b09` before anything was changed: of 11 rows, **zero** carried a recurring needle *inside* its cited region and **six** were wide regions, worst tolerance **50 lines** — the `let mut actual_edges` row this paragraph already named, whose 51-line span absorbed the +45 shift with five lines to spare. Five rows were already width 1 and exact. **The dominant shape here is the wide region, and the recurring needle is absent** — the exact inverse of the sibling registry in `fln-checker`'s charter, where the needle recurs six times and no region is wide. A repair ported between them without re-measuring would have fixed the shape the file does not have and left the one it does, which is how a guard arrives decorative.

**So: every row is width 1, and `every_agents_line_citation_points_at_the_construct_it_names` refuses a range outright.** Tolerance is zero by construction — any insertion above a cited line moves the construct off it and reddens. The one surviving vector at width 1 is a shift landing *exactly* on another occurrence, so a row whose construct recurs in its **file** must also name the item it sits inside (`@@ fn <name>`), checked against the file. The site field is required **only** where the construct recurs: elsewhere any shift already breaks containment, so a second assertion could never fail and would be decoration reading as coverage.

**That mechanism was built for one row, MEASURED NOT TO WORK ON IT, and the row was repaired a different way — recorded because the failed attempt is the useful part.** `FLN-STRUCT-024` occurs seven times in `checks.rs`, and a planted mutant moving the citation onto another of them was **not caught**: all seven sit inside the *same* function, so the enclosing item is a **coarser identity than the occurrence** and cannot separate them. The site field is real (a mutant declaring the wrong item dies), but for this row it was blind to the vector it was chosen for. The repair is the one this section already prescribes and the guard cannot impose — **a needle that occurs once**: the row now cites `constitutional prohibition`, unique in the file, at the line carrying that finding's own detail text. Tolerance zero, and it denotes *which* `FLN-STRUCT-024` site rather than merely one of seven. **So AGENTS.md now has no row needing a site**, and the rule stands as a forward guard with zero members, exercised by injected inputs rather than by the tree — a repaired population's live guard is unkillable, and only a planted member still catches the mutant.

**Accept the consequence explicitly rather than treating it as a cost: width 1 reddens MORE often.** That is correct behaviour, not a regression — it fails loudly exactly where the wide region failed silently, and a citation that cannot rot quietly is the whole purpose of the registry. The maintenance it implies is bounded and is already this section's prescribed practice: when one citation into a file reddens, re-derive **every** citation into that file. **What is still not earned:** the guard establishes that a line holds its construct and, where the needle recurs, which item it sits in — never that the sentence's argument about that construct is sound. And this is one measurement at one commit on one host, class `bounded_model`; what runs per commit is the binding.

### The tests this document names must exist *and run* (R2, second referent kind)

A line citation is one of the referent kinds this file uses; the other load-bearing one is a **test function name**, cited as the mechanism that makes a claim per-commit. Measured at `984a1555`: that population went **0 → 20 over three days**, moving on **16 of AGENTS.md's last 40 revisions**, and every one of the twenty movements was an **addition** — the set has never once shrunk. Twenty citations accreted in three days and nothing checked one of them.

Because the prose side only grows, the rot vector is never "the sentence drops the name". It is the test being renamed, deleted, `#[ignore]`d, or moved into a package `cargo test` does not walk, while the sentence stays. So the population is derived from the **prose** and resolved against the **tree**; deriving it from the tree instead is the trap this lineage has already recorded, since two derived sets that both shrink agree perfectly and a deleted test would simply leave the population rather than fail it.

`every_agents_test_citation_names_a_test_that_runs` fails the build in two tiers. **Tier 1** takes every backticked `snake_case` token and, where it resolves to a real `#[test]`, requires that test to actually run: not `#[ignore]`d, not declared by two different files, and under some workspace member's `src/` or `tests/`. There is no shape threshold, because demanding that an already-resolving test still run cannot produce a false positive. **Tier 2** requires a token that resolves to **nothing** to be declared as a non-test, and that is the direction where a wrong guess reddens a peer's tree, so it is bounded to tokens with at least four underscores — measured, all 17 cited tests clear that bar and only three non-test tokens do.

The predicates are **borrowed rather than re-implemented**: `crates/fln-conformance/src/execution.rs` already answers "what is a test" and "is it ignored" for `ci/VERIFICATION_MANIFEST.jsonl` under bead `fln-rgha`, and a second copy here would be free to drift from the one the manifest is judged by. That reuse also inherits a trap this repository has paid for twice and which recurred while this population was being derived: `#[test]` and `#[ignore]` appear in doc comments and inside guard assertions, so the construct is recognised by the **attribute at line start**, never by the token. A window-based reading — written fresh, in the course of this work — reported `corpus_census_keeps_disclosing_its_claim_class` as not running, because a doc comment six lines above it discusses `#[ignore]`d tests. It runs.

**What is declared, and what is deliberately not.** The bound half is the *remainder*: three tokens that are not tests (a `check.sh` failure name, a UBS terminal-mode class, and one `pub fn` producer) and the single cited test that does not run per commit, `present_olean_corpus_thread_matrix_compares_stream_digests`, which is legitimate only because the corpus-matrix section declares the PG-5 shortfall and its expiring waiver in the same breath. Both allowances are checked in both directions under a ceiling, so each shrinks when the thing it excused is repaired. The **total** is deliberately *not* bound: a gate on `cited=20` would redden on exactly the commits that add a good citation, which is the cry-wolf failure this bead already measured once when a census counted item 7's catalogue and drifted 26 → 27 → 28 while the live population stood still.

**What this does not earn.** Tier 2's threshold is a measured separation, not a law: a cited test whose name carries three underscores or fewer, and which has been deleted, is invisible to it — tier 1 still requires it to run if it exists, so the uncovered case is precisely *deleted-and-short-named*. Nothing checks that the sentence's **argument** about a test is true, only that the test exists, is unambiguous and runs. R5 remains unenforced here as everywhere: deleting the citation is still a way to go green. Seven mutants were planted against the guard and each was killed by a named test, the paired ones at different assertions; that campaign is one measurement at one commit on one host, class `bounded_model`, and what runs per commit is the binding.

---

## Note for Codex/GPT agents — unexpected working-tree changes

If `git status` shows edits you did not make (in `Cargo.toml`, `crates/**/*.rs`, etc.), those are from the **other agents working on this project concurrently** — a normal, frequent occurrence. **NEVER** stash, revert, or overwrite another agent's work. Treat those changes exactly as if you made them yourself. Do not stop to ask about them.

---

## Note on Built-in TODO Functionality

If I explicitly ask you to use your built-in TODO functionality, do so without complaining that you need to use beads. Always comply with such orders.
