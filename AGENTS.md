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

3. **The unsafe posture (D3).** `#![forbid(unsafe_code)]` in every authoritative crate. Project-authored `unsafe` exists only in three named boundary crates — `fln-unsafe-abi`, `fln-unsafe-region`, `fln-unsafe-jit` — with `deny(unsafe_code)` at the root and narrowly scoped, ledgered `allow` sites. `fln-kernel` is `forbid(unsafe_code)`: the TCB contains zero project-authored unsafe. Two structural laws: no `fln-unsafe-*` crate may depend on `fln-kernel`/`fln-checker`, and no unsafe crate exports any function whose return type can be laundered into a checked declaration. CI walks both.

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
- **Determinism closure.** Thread counts {1, 8, 32} per commit — over kernel-authored declarations everywhere (`fln-kernel`'s `thread_matrix_determinism`, no pin needed, bead `fln-q944`) and **over the Prelude wherever the pin is installed**, which is not every machine. The corpus differential itself still scores verdicts at one explicitly pinned width; the corpus-scale {1, 8, 32} comparison is a separate on-demand lane (`present_olean_corpus_thread_matrix_compares_stream_digests`), `#[ignore]`d for cost and typed-SKIP without the pin. It has been run once at the pin (2026-07-26, whole present-olean corpus, every per-module verdict stream and its exact consumption identical at 1, 8 and 32 threads), which earns **one observation** at that corpus revision, pin and host — class `bounded_model`, not the invariant FL-INV-01 states. PG-5 asks for {1, 8, 32} **per commit**; an on-demand lane is a documented shortfall against that gate, not compliance with it (beads `fln-8zsq`, `fln-corpus-thread-matrix-93te`). **The PG-5 waiver, stated publicly because that is the only way a gate may be bypassed:** per-commit corpus width coverage is waived on the measured cost — one run is 1,926,656 ms (32.1 min) on a 64-way host, three quarters of it in the sequential column — and because CI installs no Reference toolchain, so the lane cannot execute there at all. The standing evidence is the retained receipt at `crates/fln-conformance/evidence/corpus_thread_matrix/<pin>.jsonl`, which binds each run to the pin, the corpus revision and the host. **The waiver expires when the Reference pin moves**, and it expires *mechanically*: the receipt path is keyed by pin, so advancing `SUITE.lock` makes `the_corpus_matrix_observation_is_retained_and_bound_to_the_current_pin` fail with the re-run command, its measured cost, and the cheaper honest alternative of withdrawing the claim (bead `franken_lean-p6x1`). Bit-identical artifacts across the certified platform matrix under `--reproducible`; release binaries built twice in isolated builders and compared; the stdlib double-elaboration fixpoint.
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

**The mechanism, so nobody re-derives a weaker rule from it.** `scripts/evidence.py:10296-10307` samples `repository_state() -> (head, tree)` **three times**, calling `scan_index_and_worktree()` between samples, and raises `Reference repository state changed during verification` unless all three are identical. It is not hashing a list of paths. It asserts that **the whole repository held still**.

That distinction is the entire rule, and getting it wrong has cost two lanes:

```bash
flock -n /data/tmp/fln-gate.lockfile -c true    # exit 0 = free, exit 1 = HELD
```

> **HELD means the repository is frozen. Make no change of any kind inside it.** No commits. No edits. No file creation. No `br` command that writes. Not `crates/`, not `ci/`, not `scripts/` — and **not `AGENTS.md`, `README.md` or the plan either.**

**Why three people derived three wrong rules.** `INPUT_PATHS` in `scripts/check.sh` is real, and it *looks* like the boundary — it is an explicit, short, authoritative-looking list, so everyone reads it as "these are the files that matter". It governs a different check (`governed_inputs_changed`). The freeze above is separate and stricter, and it is the one that ends a lane. If you remember one thing, remember the strict one: **the lock freezes the repo, not a subset of it.**

The three attempts, recorded because each was made in good faith by someone following the rule as then stated:

1. "No writes to governed paths" — missed that `.beads/issues.jsonl` is `INPUT_PATHS` line 150, so *filing a bead* is a write. Cost the first `env_snapshots` lane.
2. "…and `AGENTS.md` is outside `INPUT_PATHS`, so it is safe mid-lane" — wrong for the reason above. `24b16eeb`, an `AGENTS.md` commit at 21:30:59, killed the rerun at 21:31:10. **The section you are reading replaces the one that did it.**
3. This one, taken from the source line rather than inferred from a path list.

**What is safe while the lock is held:** reading anything; `br` **only** with `--no-auto-flush` (it auto-flushes the JSONL on ordinary *reads*, so a bare `br show` writes); thinking, planning, drafting; and writing **outside the repository**, i.e. under `/data/tmp`. Draft the bead body, the commit message, the diff into the scratchpad and apply them the moment the lane releases. Avoid `cargo` too — it can rewrite `Cargo.lock`.

**A failed probe is an answer, not an obstacle.** If `flock -n … && git commit …` exits 1 with no commit, the plumbing worked: the gate said *held*. Do not re-run without the guard. Written from a real one — on 2026-07-25 cc_3 diagnosed the short-circuit correctly, read it as shell friction, committed directly 16 seconds into a running lane (`bb561892`), and cost the rerun before this one.

**Do not use `pgrep -f` to decide whether a lane is running.** It matches its own command line and will report a lane that is your own grep. Use `ps -eo pid,ppid,args` with your own process tree excluded — or just trust the lock, which is what it is for.

**A probe that says FREE can also be wrong, and that is the harder case.** `flock -n` answers "is it held *right now*", and the answer is stale the instant it returns. The lane acquires with `flock -w 2400` — a *waiting* acquire — so it can be dispatched and queued while the lock still reads free. On 2026-07-25 three panes probed correctly, got free, and wrote; `.beads/issues.jsonl` was written at 21:23:35Z against a lane dispatched at 21:23:06Z. **Do not "fix" this by wrapping the write in `flock -w …`**: that queues your write to fire the moment the lock frees, which is precisely when the next lane takes it. There is no safe way to *gate* a write on a probe. Write when the tree is confirmed quiet, not when a probe happens to return zero.

**A lane can kill itself.** Its own script and `scripts/evidence.py` are both tracked, so the pane running the lane must finish editing them **before** launching, not merely refrain during. A save 30 seconds in looks identical to an outsider's edit and ends the run the same way.

**A *static* dirty tree is fine; a *changing* one is not.** `tree` is content, so uncommitted work that nobody touches hashes identically on all three samples. An unfinished edit you stop touching is acceptable — a rushed commit to "get it in before the lane" is not.

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

---

## bv — Graph-Aware Triage

`bv` computes PageRank/betweenness/critical-path/cycles over `.beads/beads.jsonl`. **Use ONLY `--robot-*` flags — bare `bv` launches a blocking TUI.** Start with `bv --robot-triage` (counts + top picks + quick wins + blockers). `bv --robot-plan` for parallel tracks; `bv --robot-insights` for full metrics (check `.Cycles` — must be empty).

---

## UBS — Ultimate Bug Scanner

`ubs <changed-files>` before every commit. Exit 0 = safe; exit >0 = fix & re-run.

```bash
ubs file.rs file2.rs                    # specific files (< 1s)
ubs $(git diff --name-only --cached)    # staged files — before commit
ubs --only=rust,toml crates/            # language filter
```
Parse `file:line:col` → location, 💡 → suggested fix. Fix root cause, not symptom. Critical (always fix): memory safety, UB, data races. Important: unwrap panics, resource leaks, overflow.

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
5. **While an e2e lane holds the gate lock, change NOTHING inside the repository** — see [The Build Gate](#the-build-gate--while-a-lane-runs-the-repository-is-frozen) above for the mechanism and the full rule. Stated here only because this is the list people read: `INPUT_PATHS` (`scripts/check.sh:149-171`) governs `governed_inputs_changed` and is a *path list* that does **not** include `AGENTS.md`; the freeze that ends a lane is `repository_state()` and is *path-agnostic*. **During a lane, every tracked file is effectively a governed input.** Reading only the path list is how "I checked, my file wasn't on it" kills a run — item 7's defect family one floor down, two artifacts with neither naming the other.
6. **The pinned Reference toolchain** lives at `~/.elan/toolchains/leanprover--lean4---v4.32.0/` (install with `elan toolchain install leanprover/lean4:v4.32.0` if absent; the kernel-replay suites SKIP typed without it). RCH remote workers do NOT have it — run pin-dependent tests locally (a small wrapper script avoids the RCH cargo hook). Lanes longer than the 10-minute tool timeout should be launched detached (`setsid nohup … &`) and watched.
7. **The recurring defect: evidence must be produced where the claim is made.** Stated once, generally, because it has now been found six times in four subsystems and every single time by somebody *reading carefully* rather than by a check:

   > Every level, digest, capture and delegation must **name the thing that produces it**, and must **fail when that thing changes**.

   The reason it keeps recurring is that the claim is always *locally* consistent. The gap lives in the **join** between a claim and its evidence, so no single artifact reads as wrong and no single-artifact review can find it. When stating a claim's evidence requires two artifacts, the join between them needs its own check.

   The six, with the join that was unwatched — and, more usefully, whether anything would catch a recurrence:

   | instance | the unwatched join | caught by |
   |---|---|---|
   | `franken_lean-4o3n` | a bound and the configuration it was measured in | **mechanism** — `Calibration` is a private field so no bound can exist without provenance; `Comparability::establish` refuses mismatched configurations; the always-on descent guards falsify the measurement in the direction that aborts |
   | `franken_lean-pnav` | an assertion and the lane it delegates to | **mechanism** — `contract_roots.rs` asserts the lane exists, still invokes `--check`, **and is named by `scripts/check.sh`**, with a negative control. Registration is the part that matters: a script can sit in the tree unrun for months |
   | `fln-parity-ledger-l2-pinned-source-qydn` | a level and the oracle that produced it | **mechanism** — `validate_level_is_supported_by_its_oracle`; the thirteen known violations are declared, so the fourteenth fails, and the allowance is checked in both directions so it shrinks with each repair |
   | `franken_lean-ext-observable-fixture-drift-gap-vqnu` | a capture and the pin it came from | **mechanism** — `ext_observable_capture.rs` re-derives from the pinned binary on every run (~1.6 s) |
   | `franken_lean-parity-ledger-l2-definition-split-kl4h` | a term and the document that defines it | **partly** — the Witness row fails if *either* definition moves, but the standing contradiction is `Acknowledged` and green. Movement is mechanised; the state is not |
   | `fln-8zsq` | a census and the claim class it supports | **mechanism** — `corpus_census_keeps_disclosing_its_claim_class` reads the source and fails if either census's SUMMARY row drops its inline class, if a CLAIM-CLASS row loses its `means=`, its cadence or the lane it points at, if the module doc stops scoping the per-commit matrix to the Prelude, or if a class token drifts outside the allowance the file's own code earns — checked as an exact token, in both directions, and against the code in that census's own region. It had to be **source**-level: both censuses are printed by `#[ignore]`d tests, so a stdout grep sees silence, not a missing disclosure |

   **Where the luck is still load-bearing.** Five of the six now fail on recurrence; one fails only if a definition moves. `kl4h`'s standing state is the remaining half-open one: movement is mechanised, the contradiction's `Acknowledged` status is not. Everywhere else the mechanism, not the reviewer, is doing the work. Six instances found by attentive reading is not a mechanism; it is luck with good people, and luck does not survive a context restart.

   **Two things `fln-8zsq`'s repair taught, both worth more than the repair.** First, *the guard's own text is inside its search space*. The first version asserted the qualifier appeared **somewhere** in the file; a planted mutant that gutted the SUMMARY row survived, because the standalone CLAIM-CLASS row satisfied the check — the identical wrong-scope shape the bead was about, reproduced inside its own fix and caught only because the mutant was planted. Scope an assertion to the **site** that must carry the evidence, never to the file. Second, a source-reading guard must exclude **every guard body, not merely its own**. Excluding only itself is not enough and the correction cost a third instance: `franken_lean-2ki4`'s guard probes whether the corpus is still single-width by looking for the size-heuristic literal — which also appears inside the `fln-8zsq` guard's *assertion*, so the probe reported the production heuristic present after it had been deleted, and demanded a qualifier that had become false. Cut the search region at the **first** source-reading guard, so only production code is in scope. When self-exclusion is removed entirely the failure is *loud* (the guard refuses on a clean tree), which is the correct direction for a check that cannot decide.

   **What this does not earn:** mechanising a disclosure does not upgrade the claim it discloses. That real evidence — a `{1, 8, 32}` corpus run comparing stream digests at an explicitly pinned width — was built and run separately (`fln-corpus-thread-matrix-93te`), and it moved corpus schedule-independence from *inferred* to **one observation, still not a measured invariant**: the lane runs on demand, so PG-5's per-commit gate stays a documented shortfall. Note which half each bead earned. `fln-8zsq` and `franken_lean-2ki4` closed on the disclosure and bought nothing about the corpus; `93te` bought a bounded observation about the corpus and nothing about cadence. Neither is the invariant, and stacking them does not make one.

   A seventh is already filed and deliberately unmechanised: `fln-term-plane-population-differential-wv4u` carries constraints R1–R4 as *prose in a bead*, on a rig nobody has started. Its own R4 says the enforcement law must land **with** the rig rather than after it — which is this rule applied to a claim that does not exist yet.

---

## Note for Codex/GPT agents — unexpected working-tree changes

If `git status` shows edits you did not make (in `Cargo.toml`, `crates/**/*.rs`, etc.), those are from the **other agents working on this project concurrently** — a normal, frequent occurrence. **NEVER** stash, revert, or overwrite another agent's work. Treat those changes exactly as if you made them yourself. Do not stop to ask about them.

---

## Note on Built-in TODO Functionality

If I explicitly ask you to use your built-in TODO functionality, do so without complaining that you need to use beads. Always comply with such orders.
