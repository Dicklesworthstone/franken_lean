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

**CI walks the first mechanically; the second is *part walked, part declared-and-reviewed*, and this sentence has now been wrong in both directions** (bead `fln-boundary-api-no-admission-argument-discarded-ez07`, audited at `c7a23f02`, repaired in the same commit as this sentence). It first claimed CI walked both, which was false; the correction said the export law was walked *nowhere*, which is no longer true. The **dependency** law is real and *derived*: the edge set comes from the actual `Cargo.toml` files (`checks.rs:1757-1807`), `FLN-STRUCT-008` (`checks.rs:1884-1925`) walks it transitively for every crate matching the `fln-unsafe-*` **pattern** — so a new boundary crate is covered without editing the rule, and a laundering path whose every hop is rank-legal still fails (`seeded.rs:252` plants exactly that, since `fln-unsafe-jit` is rank 12 and `fln-kernel` rank 6, so layering alone would permit it) — and `FLN-STRUCT-024` (`checks.rs:1488-1512`) pins the prohibition itself, so deleting the line fails too. It runs under plain `cargo test` (`real_workspace.rs:33`, not `#[ignore]`d), not only in a lane.

The **export** law is weaker than it reads. What CI enforces is an *inventory*: every bare-`pub` item needs a reviewed `ci/BOUNDARY_API.txt` row, and undeclared items, stale rows, unclassifiable shapes, macro-synthesised exports and stray `export_name`/`no_mangle` sites all fail. **Launderability itself is nowhere expressed in code.** The row grammar's last three fields — surface type, evidence, and the argument for why the item cannot launder into kernel admission — are checked non-empty (`boundary_api.rs:74`) and then **discarded**: `ApiRow` (`boundary_api.rs:16-26`) keeps only `id`, `path`, `kind`, `name`. The file's own doc-comment calls it "the no-admission export covenant's type-aware half" and the parser retains no type. Of the 66 rows at `c7a23f02`, 31 argue from the discarded surface type, 24 describe behaviour without arguing admission at all, and 14 of the 15 rows returning an opaque handle rest entirely on one row plus a **comment** at `BOUNDARY_API.txt:13-16` that is stripped before parsing.

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
| `cargo test` / `clippy` / `fmt`, **one package or one target** | **yes** — this is the sanctioned escape hatch |
| `cargo test --workspace --no-fail-fast` | **two suites red, three tests** — all `structure-guard`, all reading `contracts/*.tsv`, which is **untracked** (53 MB, bead `fln-census-out-of-git-2ya9`): a fresh checkout has no copy, and the symlink shim people install to compensate is refused as `handoff_output_ambiguous`. Measured `7ebbddea`: **138 ok, 2 red** — `--lib`'s `contract_handoff_no_mock_e2e`, and `--test real_workspace`'s `real_workspace_is_structurally_clean` and `robot_real_workspace_binds_complete_authority_evidence` (bead `fln-census-empty-referent-no-mock-krb0`) |
| `cargo test --workspace` **without** `--no-fail-fast` | **do not report a tally from it** — cargo stops at the first failing *target*. The same tree, same commit, reports "101 ok, 1 red": it hides 37 suites and the second failing suite entirely. A test name absent from that output means *did not run*, never *passed*. I published the 101/1 figure before re-running with the flag; this row is that correction |
| `ubs <paths>` — the fourth mandated check | **yes — `cd` into the tree first and pass RELATIVE paths.** `ubs` stages a shadow workspace rooted at **cwd** and cannot stage a path resolving outside it; the trigger is the argument, not the checkout. Measured as a 2×2 at `14638e4c`, same file, worktree `.git` a 59-byte pointer file: cwd=main+relative **0**, cwd=worktree+relative **0**, cwd=main+absolute-into-worktree **1**, cwd=worktree+absolute-into-main **1** (cc_3, reproduced by cc_2). A worktree `ubs` delta at a pinned commit is therefore still available, and is the cleanest attributable baseline while the shared tree is dirty. **But never compare counts across two trees**: a worktree at a clean commit and a main tree carrying WIP hold different bytes, so the gap reads as a tool inconsistency when it is a content difference (56 vs 34 on one file, measured 2026-07-26). Hold the path and the cwd fixed and vary **only** the content — `git show <sha>:<path> > <path>`, scan, restore — which is the same one-variable rule that this row's own first version broke |
| `evidence.py hash-tree --root R --path P` | yes, exit 0 |
| `evidence.py hash-tree … **--vendor-path V**` | **no** — exit 2 |
| `evidence.py ubs-inventory`, `evidence.py vendor-binding` | **no** — exit 2 |
| `scripts/check.sh`, the evidence self-test, `scripts/verify_vendor_tree.sh` | **no** — exit 2 |
| any `fln.e2e/2` lane | **no** — `hash-tree --vendor-path` is its first governed step |

So the evidence surface runs in the **main tree only**. Two consequences worth stating separately, because each has already cost something:

1. **Every one of those failures blames something else.** `check.sh` says `cannot inventory UBS inputs`, so you go looking for `ubs`. `closure_audit.sh` says `cannot hash governed inputs`, so you go looking for a dirty tree. Seven lanes say `cannot verify the pinned Reference tree`, so you go looking for `vendor/`. The true line — `requires a real repository .git directory` — is printed once on stderr, *above* the lane's own louder and wrong summary. Nobody misread anything; the artifact asserts the wrong cause. **Until `run_git` names the worktree condition itself, this paragraph is doing a job an error message should do** — and doctrine that a message could replace is doctrine that rots. The rows measured on 2026-07-26 sharpen this, one of them the hard way. `structure-guard` says `handoff_output_ambiguous`, which reads as a corrupt handoff; the cause is an untracked input. `ubs` says `Failed to prepare files workspace`, which reads as a broken scanner — and I published a row here blaming the worktree, because I compared a worktree path against a main-tree path **from the same cwd** and so varied two things at once. cc_3 ran the 2×2; the cause is cwd. **So the misdirection is not `run_git`'s defect**: a message naming neither candidate lets every reader supply whichever cause they arrived with, and a wrong one written down here travels faster than the measurement that corrects it — this one reached five panes before it was two hours old. Fixing `run_git`'s message, still the right repair, will shorten this section by one row rather than retire it. **Vary one thing per probe, and say which one.**
2. **Reachability is not execution.** Twelve `evidence.py` subcommands reach `run_git`; deriving the affected set from the call graph is wrong in both directions, because `hash-tree` is on that list and succeeds without `--vendor-path`. Measure the exit code with a main-tree control; never infer it, and never read it through a pipe (`… | tail` reports `tail`'s status).

If you have reported a bead verified against `check.sh`, the evidence self-test, or an e2e lane **from a worktree**, that claim is hollow — say so and re-verify in the main tree under `flock`, rather than carrying it.

`crates/fln-conformance/tests/evidence_finalization.rs::the_evidence_surface_refuses_a_gitdir_pointer_root` holds this table to the code: it builds a root whose `.git` is a file and asserts the real refusal, and it fails if this section stops naming the surfaces that refuse. Neither half can drift silently without the other failing.

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
- **Determinism closure.** Thread counts {1, 8, 32} per commit — over kernel-authored declarations everywhere (`fln-kernel`'s `thread_matrix_determinism`, no pin needed, bead `fln-q944`) and **over the Prelude wherever the pin is installed**, which is not every machine. The corpus differential itself still scores verdicts at one explicitly pinned width; the corpus-scale {1, 8, 32} comparison is a separate on-demand lane (`present_olean_corpus_thread_matrix_compares_stream_digests`), `#[ignore]`d for cost and typed-SKIP without the pin. It has been run at the pin (2026-07-26, whole present-olean corpus, every per-module verdict stream and its exact consumption identical at 1, 8 and 32 threads) — corpus matrix observations recorded: 1 — which earns **one observation** at that corpus revision, pin and host — class `bounded_model`, not the invariant FL-INV-01 states. PG-5 asks for {1, 8, 32} **per commit**; an on-demand lane is a documented shortfall against that gate, not compliance with it (beads `fln-8zsq`, `fln-corpus-thread-matrix-93te`). **The PG-5 waiver, stated publicly because that is the only way a gate may be bypassed:** per-commit corpus width coverage is waived on the measured cost — one run is 1,926,656 ms (32.1 min) on a 64-way host, three quarters of it in the sequential column — and because CI installs no Reference toolchain, so the lane cannot execute there at all. The standing evidence is the retained receipt at `crates/fln-conformance/evidence/corpus_thread_matrix/<pin>.jsonl`, which binds each run to the pin, the corpus revision and the host. **The waiver expires when the Reference pin moves**, and it expires *mechanically*: the receipt path is keyed by pin, so advancing `SUITE.lock` makes `the_corpus_matrix_observation_is_retained_and_bound_to_the_current_pin` fail with the re-run command, its measured cost, and the cheaper honest alternative of withdrawing the claim (bead `franken_lean-p6x1`). Bit-identical artifacts across the certified platform matrix under `--reproducible`; release binaries built twice in isolated builders and compared; the stdlib double-elaboration fixpoint.
- **Torture (asupersync lab).** The daemon and build fabric under virtual time with cancellation storms, fault injection, crash-recovery of the frankensqlite stores, seed-replay of every failure.
- **No-mock lanes.** Release-level claims close only against the real thing: real Reference binaries, real filesystems, real editor clients, real corruption. Mocked boundaries are fine for unit tests and rejected by the evidence gate.

---

## Agent Ergonomics Requirements

CLI robot surfaces must be: stable versioned schema, deterministic where possible, explicit exit codes, line-oriented output, easy to pipe. Do not mix human decoration with machine output. `--json` shapes are conformance surface (pinned to the Reference where the flag exists there; versioned under `--fln-*` where new). Robot responses from Envoy carry schema/epoch/profile versions, request and snapshot ids, resource facts, data grade (provisional/verified), and evidence links. Dogfood `fln doctor --sql`: the build database is the observability surface.

---

## Session Completion ("Landing the Plane")

Before finishing a work session you MUST:
1. File beads issues for remaining work (anything needing follow-up).
2. Run quality gates (if code changed) — tests, clippy, fmt, `ubs`.
3. Update issue status — close finished work, update in-progress.
4. `br sync --flush-only` to export beads to JSONL, then `git add .beads/`.
5. Hand off — summarize what changed, gates run + results, remaining risks/gaps, concrete next steps.

---

## MCP Agent Mail — Multi-Agent Coordination

A mail-like layer for agents to coordinate via MCP tools/resources: identities, inbox/outbox, searchable threads, advisory file reservations with human-auditable Git artifacts.

- **Register identity:** `ensure_project(project_key=<abs-path>)` → `register_agent(project_key, program, model)`.
- **Reserve files before editing:** `file_reservation_paths(project_key, agent_name, ["crates/fln-kernel/**"], ttl_seconds=3600, exclusive=true, reason="br-###")`.
- **Communicate with threads:** `send_message(..., thread_id="br-###")`, `fetch_inbox`, `acknowledge_message`.
- **Prefer macros:** `macro_start_session`, `macro_prepare_thread`, `macro_file_reservation_cycle`, `macro_contact_handshake`.
- Common pitfalls: `"from_agent not registered"` → `register_agent` in the right `project_key` first; `"FILE_RESERVATION_CONFLICT"` → adjust patterns / wait / use non-exclusive.

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

> **HELD means the repository is frozen. Make no change of any kind inside it.** No commits. No edits. No file creation. No `br` command that writes. Not `crates/`, not `ci/`, not `scripts/` — and **not `AGENTS.md`, `README.md` or the plan either.**

**Why three people derived three wrong rules.** `INPUT_PATHS` in `scripts/check.sh` is real, and it *looks* like the boundary — it is an explicit, short, authoritative-looking list, so everyone reads it as "these are the files that matter". It governs M2/M3 (`governed_inputs_changed`, `final_workspace_changed`) and nothing else. But the freeze is not simply "separate and stricter", which is what this paragraph used to say and what the measurement disproves: it is stricter in one direction and **blind** in the other. If you remember one thing, remember the union: **any commit kills any lane; any write to that lane's governed set kills that lane; and "my file is not on the list" is an argument about M2/M3 that says nothing about M1.**

The three attempts, recorded because each was made in good faith by someone following the rule as then stated:

1. "No writes to governed paths" — missed that `.beads/issues.jsonl` is `INPUT_PATHS` line 150, so *filing a bead* is a write. Cost the first `env_snapshots` lane. **This attribution is now doubted and has not been re-measured:** `.beads/issues.jsonl` is in **`check.sh`'s** list and *not* in `env_snapshots`', so M2/M3 could not have seen it there, and the kill was more likely M1 catching an accompanying commit. The bundle was not retained, so this stays recorded as unresolved rather than replaced by a second confident guess.
2. "…and `AGENTS.md` is outside `INPUT_PATHS`, so it is safe mid-lane" — the half of that sentence about `INPUT_PATHS` was *correct* and the conclusion still wrong, which is what makes it worth keeping. `24b16eeb` was an `AGENTS.md` **commit** at 21:30:59, and it killed the rerun at 21:31:10 through M1's `HEAD` half, which no path list governs. **The section you are reading replaces the one that did it.**

   **This entry used to end "an uncommitted `AGENTS.md` edit would have survived all four mechanisms — a fact about the mechanisms". That is false, and it is false in the direction that costs a lane.** It was a fact about **one** lane. Measured at `5f7e44ad` by deriving every lane's governed set from the scripts instead of reading one: `scripts/e2e/vellum_naming_no_mock_e2e.sh:83-95` lists `AGENTS.md`, `README.md` and `COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md` in its `INPUT_PATHS` — and again in its `SUBJECT_PATHS`. For that lane an **uncommitted** `AGENTS.md` edit is a governed-input mutation and fires M2/M3/M4 with no commit anywhere. The old sentence generalised from `env_snapshots`, whose 13 paths do not include it.
3. This one, taken from the source line rather than inferred from a path list — and now superseded by the measurement above, because reading the source got M1's *scope* wrong in the same way the prose did.

**What is safe while the lock is held:** reading anything; `br` **only** with `--no-auto-flush` (it auto-flushes the JSONL on ordinary *reads*, so a bare `br show` writes); thinking, planning, drafting; and writing **outside the repository**, i.e. under `/data/tmp`. Draft the bead body, the commit message, the diff into the scratchpad and apply them the moment the lane releases. Avoid `cargo` too — it can rewrite `Cargo.lock`.

**A failed probe is an answer, not an obstacle.** If `flock -n … && git commit …` exits 1 with no commit, the plumbing worked: the gate said *held*. Do not re-run without the guard. Written from a real one — on 2026-07-25 cc_3 diagnosed the short-circuit correctly, read it as shell friction, committed directly 16 seconds into a running lane (`bb561892`), and cost the rerun before this one.

**Do not use `pgrep -f` to decide whether a lane is running.** It matches its own command line and will report a lane that is your own grep. Use `ps -eo pid,ppid,args` with your own process tree excluded — or just trust the lock, which is what it is for.

**A probe that says FREE can also be wrong, and that is the harder case.** `flock -n` answers "is it held *right now*", and the answer is stale the instant it returns. The lane acquires with `flock -w 2400` — a *waiting* acquire — so it can be dispatched and queued while the lock still reads free. On 2026-07-25 three panes probed correctly, got free, and wrote; `.beads/issues.jsonl` was written at 21:23:35Z against a lane dispatched at 21:23:06Z. **Do not "fix" this by wrapping the write in `flock -w …`**: that queues your write to fire the moment the lock frees, which is precisely when the next lane takes it. There is no safe way to *gate* a write on a probe. Write when the tree is confirmed quiet, not when a probe happens to return zero.

**A lane can kill itself.** Its own script and `scripts/evidence.py` are both tracked, so the pane running the lane must finish editing them **before** launching, not merely refrain during. A save 30 seconds in looks identical to an outsider's edit and ends the run the same way.

**A *static* dirty tree is fine; a *changing* one is not.** The conclusion holds and its old justification did not: `tree` is `rev-parse HEAD:vendor/lean4-src`, a **committed subtree object id**, so uncommitted work never enters M1's comparison at all rather than "hashing identically". What actually makes a static dirty tree safe is that M2/M3 compare content at instants and M4 only refuses a file that moves *while it is being read*. An unfinished edit you stop touching is acceptable — a rushed commit to "get it in before the lane" is not, and that is M1.

**Two traps inside that allowance, both measured.** Writing a governed file with **byte-identical content** does not save you: M4's stability check includes `st_mtime_ns` and `st_ctime_ns`, so a no-op rewrite during a governed hash still raises `file changed while being read` (7/8 trials; the 8th is the race, not a reprieve). And "static" means *untouched*, not *unchanged* — a formatter, an editor autosave, or a `cargo` invocation rewriting `Cargo.lock` all count as motion.

**Narrowness is a property of the lane you are running, never of lanes.** Derived at `5f7e44ad` from all 21 scripts in `scripts/e2e/` rather than read off one — 98np R1. **Eight lanes declare a governed set; thirteen declare none at all** and so cannot raise M2/M3/M4 under any write:

| governed paths | lane | relative to `check.sh`'s 50 |
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

**What this section still does not earn — stated because it is exactly the defect family of item 7 below, sitting on the doctrine that costs the most lanes.** Nothing holds any of it to the code. The table of mechanisms above is a **measurement written down**, not a derived one: they were found by reading `scripts/evidence.py`, `scripts/check.sh` and one lane script, so a *sixth* could exist and nothing would say so — a *fifth* already did, `stable_symlink_facts`, found by derivation after the four-row table had read as complete three times. The governed-set table is now derived, which closes 98np R1; nothing yet re-derives it **per commit**, so it rots exactly like the prose it replaced. Compare `the_evidence_surface_refuses_a_gitdir_pointer_root`, which does hold the green-bar table to the code one section up. R4 remains open (a test that fails when a lane's governed set moves without this section moving, in **both** directions, with a planted decoy proving the scan is not vacuous). Until R4 lands, treat both tables the way you would treat any claim whose evidence is prose: **re-measure before relying on an edge of it**, and record the commit you measured at.

---

## Beads (br) — Dependency-Aware Issue Tracking

This project uses [beads_rust](https://github.com/Dicklesworthstone/beads_rust) (`br`). Issues live in `.beads/` and are tracked in git. **`br` is non-invasive — it NEVER runs git.** After `br sync --flush-only`, manually `git add .beads/ && git commit`.

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

That collides with `ci/` being cod_2's. **Standing rule, decided 2026-07-25: atomicity wins, with disclosure.**

- You MAY edit `ci/VERIFICATION_MANIFEST.jsonl` in the same commit as your close, **strictly limited to your own bead's coverage row**.
- You MUST say so plainly in the commit message or a bead comment.
- You may NOT touch any other row, and NO other file in `ci/`. The adoption record, the schema, other panes' rows, `WORKSPACE_GRAPH.txt`, and the ownership projection's algorithm all remain cod_2's sole authority.

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
“passed.” Any other critical, uncertain role, missing site, or count mismatch
blocks.

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
5. **While an e2e lane holds the gate lock, change NOTHING inside the repository** — see [The Build Gate](#the-build-gate--while-a-lane-runs-the-repository-is-frozen) above for the mechanism and the full rule. Stated here only because this is the list people read: `INPUT_PATHS` (`scripts/check.sh:149-171`) governs `governed_inputs_changed` and is a *path list*; the freeze that ends a lane is `repository_state()` and is *path-agnostic*. **During a lane, every tracked file is effectively a governed input.** Reading only the path list is how "I checked, my file wasn't on it" kills a run — item 7's defect family one floor down, two artifacts with neither naming the other. **This entry used to add "…and does not include `AGENTS.md`", which was true of `check.sh` and read by three people as true of lanes.** It is not: `scripts/e2e/vellum_naming_no_mock_e2e.sh` governs `AGENTS.md`, `README.md` and the plan, so for that lane an *uncommitted* edit to this file is enough. There is no single path list to check — each lane declares its own and thirteen of the twenty-one declare none.
6. **The pinned Reference toolchain** lives at `~/.elan/toolchains/leanprover--lean4---v4.32.0/` (install with `elan toolchain install leanprover/lean4:v4.32.0` if absent; the kernel-replay suites SKIP typed without it). RCH remote workers do NOT have it — run pin-dependent tests locally (a small wrapper script avoids the RCH cargo hook). Lanes longer than the 10-minute tool timeout should be launched detached (`setsid nohup … &`) and watched.
7. **The recurring defect: evidence must be produced where the claim is made.** Stated once, generally, because it has now been found eleven times and every single time by somebody *reading carefully* rather than by a check:

   > Every level, digest, capture and delegation must **name the thing that produces it**, and must **fail when that thing changes**.

   The reason it keeps recurring is that the claim is always *locally* consistent. The gap lives in the **join** between a claim and its evidence, so no single artifact reads as wrong and no single-artifact review can find it. When stating a claim's evidence requires two artifacts, the join between them needs its own check.

   The eleven, with the join that was unwatched — and, more usefully, whether anything would catch a recurrence:

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
   | `franken_lean-worktree-gitdir-refusal-hugg` | a **verification practice** and the gates it cannot actually run — the *hollow-green* shape, where the claim is "verified" and the far end never executed | **mechanism, with its scope still hand-listed** — `the_evidence_surface_refuses_a_gitdir_pointer_root` builds a root whose `.git` is a gitdir pointer, asserts the real refusal, and requires the AGENTS.md green-bar section to keep naming the surfaces it takes down; five mutants killed, including relaxing the refusal, dropping one surface from the table, and defeating the probe's own control. **Two properties make this one worth reading.** First, the exit code is *not* the discriminator: a root whose `.git` is a real directory also exits 2, because git then runs and fails on its own terms, so only the file/directory distinction separates a genuine refusal from a mistyped probe — a rig checking "non-zero" would have passed with no content. Second, and the reason it survived so long, **the failure actively misdirects**: `check.sh` reports that it cannot inventory UBS inputs, a lane that it cannot hash governed inputs, seven lanes that they cannot verify the pinned Reference tree. Three wrong causes are asserted loudly above one correct line on stderr. Nobody misread anything. **What it does not earn:** the affected-surface list is written down, not derived — static reachability is provably wrong here, since `hash-tree` reaches `run_git` yet succeeds without `--vendor-path` — so a *new* lane that starts refusing would go unnamed and nothing would notice. And the misdirection itself is unfixed: the honest repair is to make `run_git` name the worktree condition, at which point this doctrine becomes unnecessary |
   | `fln-history-rewrite-evidence-anchor-reachability-vdi4` | a recorded verification and the commit it names, after a history rewrite silently changed every hash | **partly — the classifier/fixture join is watched; the repository-wide population is not.** Plain `cargo test` reaches `golden_vellum.rs`: `the_checked_in_producer_anchor_is_reachable_from_main` refuses a mutable Vellum producer that is not an ancestor of `refs/heads/main`, and `rewritten_history_separates_current_backup_only_and_unresolved_anchors` keeps an old real commit alive under both `refs/original/refs/heads/main` and `pre-filter-branch-backup` while proving that only `merge-base --is-ancestor` distinguishes it from current evidence. An existence-only mutant was killed at that backup-only assertion, so classification drift and the R5 trap now fail per commit. **That is not the systemic guard this row originally asked for.** `scan_evidence_file` is invoked only on the temporary fixture's `anchors.txt` and on a missing-path refusal; no tracked test scans `.beads/issues.jsonl`, the verification manifest, AGENTS.md, README, the plan, `ci/`, `crates/`, `scripts/`, and `tools/`, and no declared unreachable-anchor allowance is checked in either direction. Re-audited and manually re-measured at stable `2f9112f74bb2ea77dc2e1ddebff02aff3aaabc1b`: 563 commit-anchor tokens across 327 tracked scoped files = 397 main-reachable + **166 local-backup-only**, with zero ancestry-indeterminate; the original **166 of 411** at `14bbbe7f` is historical. The 2026-07-25 `filter-branch` did not make those anchors wrong; it made them unverifiable from `main`, while local backup refs still make a naive existence check pass. Because the census and its population are not a per-commit producer, a hundred more backup-only anchors would still not fail the build. The close earned R2/R5 classification and seeded controls, not corpus-wide retention |
   | `fln-cross-tree-baked-root-k60n` | a verdict and the **checkout that produced it** — a test binary compiled in one tree answers for that tree, and says so nowhere | **mechanism, over part of the workspace, and the part is measured rather than claimed** — `crates/fln-conformance/src/tree_identity.rs`. `CARGO_TARGET_DIR` is shared machine-wide here, `env!("CARGO_MANIFEST_DIR")` is a **compile-time** constant, and cargo treats a test binary built from an identical-bytes copy of the same package in another tree as *fresh*, rebuilding nothing and saying nothing. `checked_workspace_root!()` compares the baked value against the one cargo puts in the **process environment** — exact, and independent of the working directory — and refuses, naming both paths. Macros rather than functions: measured, a `macro_rules!` body expands `env!` in the *calling* crate and a plain function captures its own, and lib and test targets are cached separately so they can come from different trees. Observed live at `5c5ada4b`: `structure-guard`'s `real_workspace` binary carried `/data/tmp/wt-cc_2`, so the same command reported `PASS` here and `INCONCLUSIVE` there at the same instant, citing a symlink defect on a path that is a regular file in the tree the reader is standing in — `hugg`'s misdirection exactly. **The direction that matters is the one not currently firing:** today the bake tree is the dirtier one, so the result is a loud false red; swap which tree is dirty and the identical mechanism yields a **false green**, a suite reporting *structurally clean* about a repository that is not the one under test. **What it does not earn:** detection is not prevention — the clean fix is a per-tree target directory, a machine-level disk cap that is not this repository's to change — and the refusal only protects the crates that *call* it, which is 31 invocation sites in one crate against 38 elsewhere that still produce verdicts about whichever tree compiled them. Those 38 are three populations with three different blocks, re-measured rather than inherited: 8 sites in `tools/structure-guard`, unblocked by **one line**, since `FLN-STRUCT-007` exempts `kind=tool` crates from layering outright (`checks.rs:1863`); 19 in nine product crates, blocked *architecturally* because `fln-conformance` is rank 22 and a dev-dependency from below is an upward edge; and 11 in `tribunal/epoch-lab`, a nested workspace the members glob never walks — `bkw6`'s shape, where the scope measured and the scope meant are different sets |

   **Where the luck is still load-bearing.** Nine of the eleven now fail on recurrence; two are partial; none is wholly unwatched. **This sentence and its neighbour above spent a day disagreeing with the table between them** — the list read "The nine" while ten rows sat under it, because a row was added and only two of the three places that state this section's own cardinality were moved. That is a claim and the population it counts, unjoined, inside the section about claims and the evidence they count, and nothing would have said so; it is fixed here by hand and remains unmechanised. `kl4h`'s movement is mechanised but the contradiction's `Acknowledged` status is not. `uagk` closed its second half: the marker→kill join is now watched per commit by a receipt that expires when either the mutated site or a killer body moves, and the campaign behind it was itself attacked with four planted mutants before being believed. Its cadence half is now half-closed and worth reading for which half: the retention check forces a re-run exactly when the code changes, a weekly workflow dispatches it when the code does *not*, and the receipt's class token is derived from that dispatcher in both directions so neither can move alone. What is still missing is the **observation that a run occurred** — nothing inside the repo can tell a cron that fired from one GitHub quietly disabled, so the token attests a configured cadence, never a kept one, and each run is still one measurement at one commit on one host. `vdi4` closed the classifier/fixture half: per-commit tests now catch main-reachability classification drift and the existence-only trap, but its 166-anchor population remains a manual census, and no per-commit repository-wide scan or bidirectional allowance would notice a hundred more. `k60n` is mechanised over one crate of nine and discloses which. Everywhere else the mechanism, not the reviewer, is doing the work. Eleven instances found by attentive reading is not a mechanism; it is luck with good people, and luck does not survive a context restart. `hugg` is the sharpest argument for that sentence: the practice it invalidated had been corrected by broadcast three times in one day, and broadcasts do not survive a pane restart, which is why the correction is in this file and held there by a test.

   **Two of these rows differ in a way worth keeping.** `bkw6` is a claim whose referent **never existed**; `vdi4` is a claim whose referent **existed and was destroyed wholesale by a tool**. Both defeat the same technique for the same reason — there is nothing addressable to compare a claim against — and neither is reachable by reading one artifact more carefully. The generalisable move is the one `bkw6` used: when the far end is empty or gone, bind the claim to the **cardinality** of what it asserts, and let the number fail in both directions. `hugg` adds a third variant: a referent that **exists and is addressable, but was never reached** — the tooling refused before it ran, and said so in words that named something else. Where a claim rests on a run, check that the run *happened*, not merely that the command was issued and the exit code looked right.

   **`k60n` sharpens that rule rather than repeating it, and the sharpening was paid for.** Binding a claim to the cardinality of what it asserts is right; *which* cardinality decides whether it works. `k60n`'s coverage claim was first bound to **one aggregate count** over the whole workspace — derived from `git ls-files` rather than hand-listed, failing in the growth direction, everything the rule above asks for. It is still a **budget**, because a sum over many members is refilled by its own repairs. Measured over the 70 commits from `d40f0c0b` to `017000f0`: one conversion took the total from 44 to 38 and opened eight slots, and four new unprotected rigs then landed in four separate commits in four different crates — `b241943d`, `6e7531e6`, `1b0a9eb1`, `8391bafd` — every one of them under a guard that was green the whole time, because the total never came back to 46. The replacement declares a count **per member**, so a repair frees a slot only in the file that earned it and a new file has no slot at all; against it all four refuse and are *named*, three as undeclared files and one as growth inside a declared one — a distinction a membership-only check could not draw either. **Bind to the cardinality of each member, not to the cardinality of the population.** Two things about this are worth more than the repair: the guard that admitted those four *was itself* the mechanism for an instance in this table, so a row here is not evidence that its own shape is sound; and while fixing it, the floor on protected sites turned out to be partly satisfied by the module's **own failure messages**, which name `checked_workspace_root!()` as the repair and so matched its own needle — `fln-8zsq`'s lesson recurring inside a later instance's fix, and a reminder that a scanner's prose belongs outside any count it floors.

   **A standing habit because `vdi4` closed only the classifier/fixture half:** whenever you re-derive a measurement, record the hash you re-derived it **at**. A fresh anchor costs one `git rev-parse` and is the only thing stopping the next reader from being stranded the way this section's own examples now strand one. Re-anchoring on touch will not converge by itself — it is what keeps a manual measurement attributable while the population remains unmechanised.

   **Two things `fln-8zsq`'s repair taught, both worth more than the repair.** First, *the guard's own text is inside its search space*. The first version asserted the qualifier appeared **somewhere** in the file; a planted mutant that gutted the SUMMARY row survived, because the standalone CLAIM-CLASS row satisfied the check — the identical wrong-scope shape the bead was about, reproduced inside its own fix and caught only because the mutant was planted. Scope an assertion to the **site** that must carry the evidence, never to the file. Second, a source-reading guard must exclude **every guard body, not merely its own**. Excluding only itself is not enough and the correction cost a third instance: `franken_lean-2ki4`'s guard probes whether the corpus is still single-width by looking for the size-heuristic literal — which also appears inside the `fln-8zsq` guard's *assertion*, so the probe reported the production heuristic present after it had been deleted, and demanded a qualifier that had become false. Cut the search region at the **first** source-reading guard, so only production code is in scope. When self-exclusion is removed entirely the failure is *loud* (the guard refuses on a clean tree), which is the correct direction for a check that cannot decide.

   **What this does not earn:** mechanising a disclosure does not upgrade the claim it discloses. That real evidence — a `{1, 8, 32}` corpus run comparing stream digests at an explicitly pinned width — was built and run separately (`fln-corpus-thread-matrix-93te`), and it moved corpus schedule-independence from *inferred* to **one observation, still not a measured invariant**: the lane runs on demand, so PG-5's per-commit gate stays a documented shortfall. Note which half each bead earned. `fln-8zsq` and `franken_lean-2ki4` closed on the disclosure and bought nothing about the corpus; `93te` bought a bounded observation about the corpus and nothing about cadence. Neither is the invariant, and stacking them does not make one.

   A twelfth is already filed and deliberately unmechanised: `fln-term-plane-population-differential-wv4u` carries constraints R1–R4 as *prose in a bead*, on a rig nobody has started. Its own R4 says the enforcement law must land **with** the rig rather than after it — which is this rule applied to a claim that does not exist yet.

---

## Note for Codex/GPT agents — unexpected working-tree changes

If `git status` shows edits you did not make (in `Cargo.toml`, `crates/**/*.rs`, etc.), those are from the **other agents working on this project concurrently** — a normal, frequent occurrence. **NEVER** stash, revert, or overwrite another agent's work. Treat those changes exactly as if you made them yourself. Do not stop to ask about them.

---

## Note on Built-in TODO Functionality

If I explicitly ask you to use your built-in TODO functionality, do so without complaining that you need to use beads. Always comply with such orders.
