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
- `crates/fln-conformance/tests/pinned_nat_council.rs` now decodes the **real** pinned `Nat`, `Nat.zero`, `Nat.succ`, and `Nat.rec` rows from the `Init.Prelude` companion chain and submits that exact block through the normal K1 + independent-checker `Engine::admit_declaration` door.
- `scripts/check_pinned_nat_council.py` derives the Reference tag from `SUITE.lock`, requires the complete Prelude companion chain, and invokes exactly that ignored real-artifact cell. An explicit invocation cannot report a hollow green when the pin is absent.

**Evidence grade for the Nat step in this document: artifact-bound, not observed in the session that added this status file.** The local execution environment used for the latest edits did not contain `cargo`/`rustc`, so this document deliberately does not claim that the new pinned-Nat runner passed. Run:

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

The repository contains source-to-kernel and source-to-Golem paths for a growing bounded subset, including caller-named definitions, imports, `#check`, Nat/Bool/String operations and emitted intermediate/artifact forms. This is meaningful executable ground, not full source-language compatibility.

### Lantern / LSP server

**Status: usable bounded transport and document-checking bridge; advanced editor semantics remain incomplete.**

Landed:

- Content-Length framed stdio transport.
- LSP lifecycle (`initialize`, `initialized`, `shutdown`, `exit`).
- full-sync `didOpen`, `didChange`, `didSave`, `didClose` handling.
- document checks routed through the bounded source engine with push diagnostics.
- `$/lean/fileProgress` processing/complete notifications.
- `lean --server` entrypoint compatibility.
- fail-closed JSON string decoding with standard escapes, UTF-16 surrogate-pair handling, and raw-control rejection.
- envelope-aware JSON-RPC routing: top-level `method`/`id` cannot be impersonated by nested payload fields.
- integer **and string** JSON-RPC request IDs are preserved in responses.
- malformed request IDs are a distinct invalid class and receive `-32600` with `id:null`; fractions, exponents, leading-zero integers, overflow, `null`, objects, and malformed string tails do not degrade into notifications.
- unimplemented `$/lean/rpc/connect` and `$/lean/rpc/call` now return LSP `RequestFailed` (`-32803`) instead of fabricating a session or successful null call.

Still incomplete:

- `$/lean/plainGoal` / `$/lean/plainTermGoal` do not yet expose cursor-position-aware proof state.
- hover, completion, and definition currently return no-information `null` responses rather than semantic results.
- Lean RPC sessions/calls are explicitly **not implemented**.
- the server is not yet the full shared-heap, declaration-granular, deterministic-parallel Lantern described by the plan.

The latest LSP parser/RPC changes are **landed**. This status file does not claim they were compiled in the session that wrote it because that session lacked a Rust toolchain.

### Agent-control plane

**Status: executable governance tools now exist, not just prose.**

Landed:

- [`AGENT_FRONTIER_PROTOCOL.md`](AGENT_FRONTIER_PROTOCOL.md): immutable anchors, semantic ownership, typed frontiers, negative evidence and promotion rules.
- read-only frontier capsule auditing and Git-anchor recording.
- deterministic Beads frontier selection with fail-closed handling of malformed tracker graphs and uncertain hard-filter facts.
- deterministic blocker-cycle detection with stable concrete witnesses instead of an empty-ready-set ambiguity.

This is intended to make agent work **accretive**: failed hypotheses and verified frontiers become reusable state rather than being rediscovered from commit prose.

### ABI / runtime / compiler / build / tactics / search / docs / MCP / WASM

**Status: mixed partial implementation.**

These subsystems contain real contract planes, data structures, bounded execution slices, or integration work, but the repository has **not** reached the README's finished-system claims. In particular, full mathlib-compatible elaboration/tactic execution, the complete native `Lean.*` Mirror, full Lake/Ledger behavior, production Iron codegen/JIT, full semantic LSP/RPC, complete MCP orchestration, and release-grade cross-platform distribution remain active program work.

---

## High-priority open proof obligations

1. **Advance `fln-51y8` with real pinned evidence.** Execute the pinned Nat council locally, then continue the exact Prelude first-failure frontier rather than generalizing from fixtures.
2. **Keep independent-checker authority boundaries intact.** The checker may veto/observe; it must never become a second admission authority.
3. **Replace LSP no-information scaffolding with truthful semantics one method at a time.** Never fabricate sessions, goals, hover data, completions, or definitions to suppress editor errors.
4. **Keep the JSON-RPC parser narrow but structurally correct.** If the supported wire vocabulary outgrows the bounded hand parser, replace the parser deliberately rather than adding substring heuristics that blur envelope and payload.
5. **Prefer executable frontier evidence over narrative status.** New compatibility claims should name a reproducer, pin/artifact identity, and outcome class.

---

## Local verification commands for the latest frontier

On a host with the pinned Rust and Reference toolchains:

```bash
cargo fmt --all -- --check
cargo test --locked -p fln-server
cargo test --locked -p fln-checker --no-fail-fast
cargo test --locked -p fln-conformance --test pinned_nat_council
python3 scripts/check_pinned_nat_council.py
```

The ordinary `pinned_nat_council` target leaves the real-artifact cell ignored; the Python runner is the explicit non-vacuous invocation.

Project-wide release/gate claims require the repository's broader governed evidence procedures, not just these focused commands.
