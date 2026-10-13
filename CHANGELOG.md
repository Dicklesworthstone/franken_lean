# Changelog

This is the synthesized, agent-facing changelog for **franken_lean**. It records what has actually landed. [`README.md`](README.md) is intentionally written as the finished 1.0 target, while [`IMPLEMENTATION_STATUS.md`](IMPLEMENTATION_STATUS.md) is the current evidence-graded state ledger.

Historical synthesis: project inception on **2026-07-21** through the September 3 source-aware and interleaved Lantern tranche rooted at substantive commits [`db4e3058`](https://github.com/Dicklesworthstone/franken_lean/commit/db4e30582303ee90b9f385634be96fe1fe7e9bc5) and [`852ca5af`](https://github.com/Dicklesworthstone/franken_lean/commit/852ca5af296e560f01187edc3a8bb98178a52efd).

No GitHub Release is implied by this history. Representative commits are navigation aids, not substitutes for the Beads graph, generated contracts, real-artifact receipts, or governed release evidence.

**Catch-up, landed 2026-10-06 (bead `franken_lean-z8j.1.19`).** The four sections below this note cover 2026-09-09 through 2026-10-06 (about 1,540 commits), synthesized from the full `git log` in four author-date windows with representative shas spot-checked against the history before publication. Entries are **landed** unless they name a receipt, closure, or independent verification; commits whose own messages say they were not compiled or tested in their publishing session are flagged where the miners found them. [`IMPLEMENTATION_STATUS.md`](IMPLEMENTATION_STATUS.md) remains the evidence-graded record of current state.

---

## Mathlib at scale: the whole stdlib accepted, S22–S25, and the G1 split — 2026-10-04 → 2026-10-06 (America/New_York)

413 commits in three days (none are dated 10-01 → 10-03). The council crossed from "frontier runs with aborts" to "the pinned stdlib whole, and 81% of the combined corpus, with receipts".

- **Every pinned stdlib module accepted.** All 2,433 v4.32.0 stdlib modules — 215,136 declarations — passed K1 plus the independent checker: 0 failed, 0 inconclusive, 0 blocked, 3,908 s at `--jobs 16` (`362ada2f` receipt; closed as `fln-elp6` after independent verification at `edf81de4`). The receipt itself says what it does not claim: one run at one width; thread-count determinism and PG-1 throughput were not measured.
- **Combined frontier S22 → S25** (`a846c149`, `a141b93b`, `f6d3f759`, `c43130c9`; receipts in `crates/fln-conformance/evidence/combined_frontier/`): accepted modules of 11,083 went 6,750 → 8,153 → 8,960 → 8,973, wall time fell 36,469 s → 6,610 s, peak memory ≈ 90–97 GiB. S25: **0 failed**, 11 inconclusive roots, 2,099 blocked — the largest root, `Ideal.Quotient.Operations`, exhausts K1's 10M-step budget and blocks 1,647 modules. S22 made rows crash-survivable: each module's verdict is emitted the moment it is decided.
- **Checker fixes that cleared the S22–S24 roots**, each matched to the pin's order of operations: theorem delta unfolding (`ec312344`), a K recursor stuck under a projection (`612670c8`), repeated binder descent — `MvPolynomial.degrees_def` went from exhausting 100M steps to ≈ 5 s (`e287c63a`), constructor parameter-domain conversion with a soundness test refusing the non-converting direction (`1917a8b0`, `afdb5a42`), any number of universe parameters (`511ece0a`), and K-gate proof irrelevance, which admitted HornColimits and `PowerSeries.Catalan` (`9a9a1405`); the one real council disagreement, a checker false-reject of `CategoryTheory.Discrete.opposite`, was fixed at `34c592ce`.
- **G1 split into G1-correctness and G1-performance** (`9c2a7e61`, operator-delegated decision recorded 2026-10-05): correctness is every pinned module decided by both engines with zero divergence; performance is PG-1 observed on a declared host. The commit states explicitly that no G1 progress is claimed by the split itself.
- **Reference-differential rows folded to agree**: constrained-induction parity, the pin's mutual-block header checks (z8j.1.6.5, `7cc7a4f7`), `injection`/`subst` as the pin's (`1189150a`), hygienic `by_cases`, plus ledger catch-ups (`bb32af0d`, `7eb66671`). The tally of files the Reference rejects but FrankenLean accepts fell from 44/43 to 38/24 (re-derived at `65c2f696`).
- **False accepts closed at the source front end**: protected names reachable by an atomic name, root names shadowing an opened namespace now reported Ambiguous, four seed constants the pin does not have made unreachable (`2898f3ef`, fln-ew20), and unknown names refused at elaboration instead of being passed to K1 (`8065f5b2`, `cac2dfcf`, `5190db5c`, `8dd5bc82`). Still open: `fln-5efd` (OfNat through a semireducible def), filed P0.
- **Elaborating against the real Init**: `decide` evaluates the pin's `Decidable.decide`, imported `export` aliases resolve, and instance candidates are narrowed by a discrimination tree at `instances` transparency in the pin's try order — 297 of 297 Init.Core goals select the pin's instance (`766eb953`, `df4bb38d`, `22bd593f`).
- **The independent checker now reads `.olean` bytes itself** — it imports neither fln-olean nor fln-core, the council compares the two readings, and FLN-STRUCT-042 keeps the independence in force (`79b5e477`, `bd90120d`). Header githash/flags are held to the pin: previously 173 of 1,024 single-bit header flips were admitted; a 25,930-part Mathlib corpus scan now refuses none (`26a58548`, `e17c8b19`).
- **`import Init` got fast enough to use**: the fixed 64 MiB refusal removed, parallel import admission, a Merkle declaration digest (74.0 s → 8.05 s for digesting), end-to-end reused import 147 s → 56 s, warm reuse 83 s → 21 s on 4 cores (`0a998c32`, `d38870fc`, `82854f4f`, `e77d3f00`). `lake build` reuses checked source modules by content and `build explain` reads a recorded snapshot (`61260daa`).
- **Drop-in `lean` surface growth**: the pin's operator trees (`binop%`/`binrel%`), `⟨…⟩` patterns, `.c` and `·` forms, `where` blocks, `∃`, `h ▸ e`, namespaces/sections/`open`, every pin-reserved keyword, and `#check`/`#eval` printing the pin's way (`1abbe8bd`, `ff54ec97`, `e685d64a`, `0a44e720`).
- **Float/Float32 math executes on the owned numerics plane**: 22 unary operations plus `pow` and `atan2` now run from the source seed through K1, the independent checker, compiler ingress and Golem onto `fln-libm` at each width's own precision (`4a82e447`, bead fln-nu8r, closed on independent verification with three mutants killed and one proven equivalent). Before this, four seeded names elaborated but were refused at compilation. No platform-libm bit parity is claimed (D21); `frExp`/`scaleB` stay typed-unsupported.
- **Checker performance on the TensorProduct.Associator family** (y8wc): typed-lane query memoization, a K1 free-variable memo, Quotient-frame reuse halving `rTensor_tensor`, and whnf copy elision worth another 18–26% (`3e76d26e`, `6d99e495`, `d568efe5`). Two experimental branches are retained in history but deliberately not enabled — one stalled Char.Ordinal, the other slowed `lTensor_tensor` 174 s → 574 s (`164afe4c`).
- **Measurement and CI**: the ordinary-Lean probe is checked in, scoring 3 of 27 Reference-accepted programs at `49b53289` (the corpus has since grown to 37 with no re-score); `contract-drift.yml` went green for the first time at `6d09e347`; `ci.yml` still has no successful run. README, IMPLEMENTATION_STATUS and this file were trued up on 10-05, and the stale status rows re-derived on 10-06 (`65c2f696`).

Caveat, in this file's standing spirit: `1375cc64` (parent coercions) landed untested and broke; part was repaired at `c3d1b35e`. Entries above are **landed**, and only the ones naming receipts or closures are verified.

## The combined frontier opens: suite admission, the seed freeze, and a 3.9× checker — 2026-09-26 → 2026-09-30 (America/New_York)

134 commits. The operator's FrankenSuite ruling landed, the dialect freeze became mechanical, and the first stdlib+Mathlib frontier runs exposed and then removed the checker's worst costs.

- **The FrankenSuite was admitted by operator decision (2026-09-27)**, settling `franken_lean-z8j.1.18` after eight weeks: plan D1, the README and AGENTS.md now state the same closed universe — std, the pinned nightly, the FrankenSuite and its reviewed, pinned, per-package-allowlisted closure; serde may enter only through asupersync's closure (`4dc0e265`, `a922f9eb`, `f02fe15b`). Admission is a decision, not a link: no suite crate is in `Cargo.lock`, and the bead stays open until the `fln-883f` allowlist mechanism enforces the rule.
- **The seed-dialect freeze is enforced, not remembered** (fln-ew20, `5e4a00bb`): a pin-free test refuses any corpus file without a Reference-differential ledger row and any new divergence, starting from a 66-row allowance that may only shrink; the weekly contract-drift lane now fails rather than skips when the pin is absent.
- **First combined frontier runs, S13 → S18** (fln-r0yh): S17/S18 accepted 3,235–3,236 of 11,023 decided modules; blocking causes (Aesop.Tree.Data, MLList.Basic, Plausible.Arbitrary, Udiv) were filed and fixed; frontier non-answers are reported `inconclusive`, never `failed` (`9d6d7c0e`, `7e726860`, `8e6bb10f`).
- **Checking got 3.93× faster across the 1,687 modules two runs both decided** (fln-kfdr, 89,515 s → 22,793 s with every verdict identical): per-declaration whole-environment logical roots, which nothing read, are no longer computed — `Mathlib.Logic.Basic` 488.6 s → 4.4 s, `Mathlib.Order.Basic` 726.8 s → 10.1 s (`2228f7bb`, `70d00c2d`). The S16 → S17 wall comparison (34,009 s → 17,176 s) is explicitly not controlled: two optimizations landed between the runs.
- **The checker's reduction engine became an environment machine with shared evaluation** (fln-5l4q, fln-32rr): the Plausible blocker — first-recorded for 7,283 of 7,339 blocked modules — went from no answer in 1,500 s to 1.6 s; shared subterms survive substitution and arena materialization; the `.olean` dependency walk presents each shared node once (`8072ef49`, `022c8ce3`, `dd5857a2`).
- **Checker admission coverage**: unsafe inductives through parameterized, mutual and nested families; mutual Prop-predicate blocks; Mathlib's `compile_inductive` blocks; partial definitions at the pin's safety level (`11922211`, `cd2813af`, `398e21b9`).
- **Definitional-equality parity with the pin**: lazy delta and projections per `try_unfold_proj_app`, the KR-317 K-gate falling back to bounded conversion, proof irrelevance tried before untyped conversion, Nat reduction over let-bound literals (`ec820d84`, `8446e25f`, `42106e04`).
- **The product gate works again** (z8j.1.21 ground, fln-ffce): after a 57-file rustfmt pass and clippy repairs the gate reaches its test step, exposing 70 failing source/runtime tests, triaged down to 40 within the window (`6a92b7bf`, `16fed644`, `da3fe305`).
- **Type classes from real artifacts**: class/instance extension journals and default simp journals decode from the pinned `.olean` format and activate for source elaboration only after the whole closure passes the council; scoped instances work across namespaces and imports; instance search backtracks on unresolved universes (`2b0ebe66`, `2496c9b3`, `9baf32c0`).
- **do-notation depth**: do-if and `unless` with scoped control joins, proof-carrying and wildcard `for` loops, guarded early returns and nonlocal returns from nested loops, refutable bindings with explicit failure branches (`fc583984`, `50e37de4`, `f725157f`).
- **Native builds**: `SourceModuleSession` produces real `.olean` files; warm builds are byte-identical to cold and roll back cleanly; Lake reuses checked dependencies across compatible targets (`d517f7b5`, `552a2ca6`).
- **Editor**: go-to-definition and global name completion through both front doors, with definition origins resolved from checked elaborator observations (`e845bbbd`, `46e05cf3`, `fe10c11b`).

Caveats: several feature commits state in their own messages that Rust was not compiled in the publishing session (`46e05cf3`, `2496c9b3`) — landed, not validated there; `12248800` published earlier-staged code.

## Course correction z8j.1, the first green gate, and the council reaches the stdlib — 2026-09-18 → 2026-09-25 (America/New_York)

465 commits. The week that found the project's fabrications, removed them, and made "green" mean something.

- **The z8j.1 reality check (09-23/24) found fake success paths and removed them.** Measured against release binaries and the pinned v4.32.0: `lake build` wrote a 24-byte placeholder `.olean` and exited 0 on garbage source; `fln build explain` invented "cached" decisions from mtimes and text matching; `fln doctor` always reported healthy; reserved verbs exited 0. Three of the four had been introduced in this same window (`de5d7c8e`, `ecbdd1a4`, `159d501f`). The repairs made every one refuse typed instead of faking success, gave `doctor` real checks, and opened epic z8j.1 with 30 children (`46f63974`, `ed45d4f0`, `1aa8a6dc`, `730267d1`). A new rig compares the source pipeline against the real Lean on 105 of the repository's own files — the origin of the Reference-differential ledger.
- **The first green hosted gate in the project's history**: the new product gate runs fmt, workspace clippy `-D warnings` and workspace tests, documents each named skip with its reason, and carries a floor on how many tests must run (7,526, raised to 7,765 after the first green) so it cannot be greened by skipping more (`d1edc56f`, `8205ea64`; GitHub's run history records the gate green on 2026-09-25 at `fbe57852`).
- **The council grew from Init.Prelude to the stdlib's edge**: all 2,314 Init.Prelude declarations through both checkers (09-19, `3e898188`); the chain reached 60 modules / 8,485 declarations; `check-olean --continue` gives per-module verdicts, parallel and deterministic against each module's own imports; first whole-Init run 167 of 601 modules accepted; nested inductive families admitted by the checker to cover every inductive block in the pinned stdlib (`e9a55d9d`, `1137a259`, `e24d10da`).
- **Shared-term (DAG) handling unblocked the proofs that are trees of 64M nodes but 7,419 distinct**: terms cross to the checker in shared form, checker work scales with shared size, and the kernel term store gained interning with sharing-aware equality and walks (z8j.1.13 ground, `ffd17e24`, `8d522eb8`).
- **Checker/kernel parity fixes**: structure, function and unit-like eta in the typed conversion lane (KR-312/315), Nat reduction before each delta step as in the pin, recursor-chain deferral, unsafe-declaration unfolding, correlated imax bounds (`3b158a14`, `f644e6ef`, `bc64f29d`).
- **`check-source` imports real Init `.olean`s**: an `import` with no local source resolves from LEAN_PATH or the pinned toolchain, the whole closure is rechecked by both engines first, and output reports `"trust":"recheck"` — `import Init.Prelude` in 19 s, Init.Core's 6 modules / 4,442 declarations in 39 s (`44da1153`, `3f5566f1`).
- **Elaborator depth**: higher-order pattern unification across scopes, tabled instance search with replay and polymorphic answer reuse, Prop forcing through max/imax (`be3ec83b`, `c1cf668d`, `f33ca3f2`).
- **Source language**: mutual inductive families admitted end-to-end, monadic `do` with `for`, local structural recursion, section variables, named arguments, quotients, `have`/`suffices`/`show` (`5ebe8d5d`, `7388e436`, `d45751c9`).
- **Tactics**: a checked `simp` family (Iff rewrites through propext, default rules, `simpa`, wildcard locations), `simp_all`, `solve_by_elim`, `calc` across mixed relations with Trans synthesis, computed `cases`/`induction` (`fb8db71e`, `83d84f4f`, `43e02899`).
- **Native execution**: higher-order callbacks, mutual recursors as closure groups, indexed families, proof erasure before execution, empty eliminators compiled to never-returning bytecode (`335a27f2`, `6d271b44`, `2d689747`).
- **CLI and codec**: the `lake` personality (`init`/`new`/`clean`, TOML parsing), `verify-capsule` (relabelled honestly: decodes certificates, does not replay them), the `goals` verb, `.olean` v3 payload rebuilds with explicit relocation framing, persistent extension graphs written (`f6119a16`, `763a6b4f`, `15d26357`).

Caveats: this window's landing pipeline left duplicate shas for several changes (cite one per change) and 34 commits authored by github-actions[bot]; some `feat`-labelled commits add only a workflow file with the code in a companion commit.

## The source-language frontend lands: unifier, inductives, match, tactics, and the first checked programs that run — 2026-09-09 → 2026-09-17 (America/New_York)

527 commits (author dates, America/New_York), almost all of them the native Lean source frontend: ~142 `feat(elab)`, 40 `feat(source)`, 19 `feat(tactics)`, plus ~60 new `docs/NATIVE_*.md` and ~70 `examples/native_*.lean`. Zero beads closed in the window; three were reopened — the week optimized for ground gained, and the corrections section below is part of the record.

- **`check-source`**: whole source theorem files admitted in order, all-or-nothing, through K1 and the independent checker; later files use earlier theorems; nothing is compiled or executed, and `import`/`#eval` are never silently ignored (`1bf0ef7d`, `a7bc6a12`).
- **A native unifier whose guesses must pass the kernel**: transactional Miller-pattern unification (`05fb1d92` — whose own message says tests were not claimed run that session), partial answers valid with holes unsolved (`145fbdb5`), implicit and universe argument inference (`1b266acb`), then function eta, recursor/iota, typed record eta, native Nat arithmetic and quotient reduction (`09e6cbda`, `97dbe432`, `f1776c0d`, `1915c97b`).
- **Inductives, records, structures**: `inductive` commands all-or-nothing including empty and indexed families, with the independent checker rebuilding recursors itself (`dd69d614`, `d4f07bdd`, `1083b35f`); inductive propositions and `Acc` elimination (`9b43b774`, `9e279ea7`); dependent records with literals, field notation, updates and defaults (`fc6160b0`, `56fad42b`); structure inheritance with checked parent coercions (`69ed4e0f`).
- **Pattern matching and recursion**: exhaustive constructor `match` compiled to checked eliminators (`d636164f`), structural recursion including changing and chosen decreasing arguments (`de64681b`, `60bdae3c`), indexed matches with index refinement (`4b54c093`, `130109fa`), equation-style declarations and pattern lambdas (`1914cf83`).
- **Tactics**: dependent `cases`/`induction` over indexed and constrained families (`8ae1959d`, `847f1291`); `subst`, injectivity/disjointness, contradiction, HEq transport (`429045b3`, `4acf358e`); `first`/`try`/`repeat` that undo failed attempts (`c4521727`); `apply` failing if it leaves instance goals open (`e24f98a5`); `rw … at h` dependency-safe, `simp` at hypotheses, native `calc`, simp-attribute commands with an immutable registry (`de2f535b`, `68661efe`, `1ebf2d71`, `aa0f95a8`).
- **Type classes and coercions**: native instance search with priorities, recursive dictionaries, output/semi-output parameters with backtracking, checked value/function/sort coercions, default instances by priority (`f8304960`, `fc6ce6ef`, `1e14d0cf`, `f95b05fe`).
- **Universes and namespaces**: explicit universe syntax, polymorphic definitions/proofs/families/instances, deterministic generalization, `namespace`/`section`/`open`/`universe` all-or-nothing with selective `open` refused rather than faked (`622d27ae`, `11b5f69c`, `11451a6a`, `cffca328`).
- **Checked programs run** (09-17): compiled to FLBC and executed through the installed CLI and by bytecode replay — lazy Boolean cases, proof-erased decisions, captured local helpers, Nat recursion, records, variants with VM constructor dispatch, recursive lists and trees (`bab7fcc1`, `a2afa7b9`, `73dbadb4`, `2fc53326` — whose own message disclaims any complete-runtime claim).
- **Kernel soundness, the week's most important fix**: the kernel accepted a constructor whose parent type was outside its admitted inductive block, skipping the per-parent typing and positivity checks; now rejected (`c349dc79`, `8179c017`). Also: vanishing type ascriptions (`1c71dbdd`), recursor majors must be fully applied (`667a6837`), capture-correct equality-cast reduction (`c80283a1`).
- **Corrections and retractions, kept visible**: the `.olean` adapter fabricated Reference/Verified evidence grades for itself — callers now supply the grade and local fixtures are Provisional (`4dc21588`); a blanket dismissal of 145 UBS warnings on the parser bead was withdrawn as unsupported (`7c849962`); `rw` must keep unproved premises as goals and `simp only` must not use ambient proofs nobody selected (`6001affe`); three beads reopened from closed (`a30db3f0`, `6ddc2c6a`, `7f289b54`); a full workspace run exiting 101 with 24 failing targets was recorded with no green claimed (`7c46041b`).
- **`.olean` conformance** (09-08/09 tail): complete v4.32.0 companion chains decode (exported/server/private), real Prelude tag attributes import, epoch mismatches refuse typed (`45e8590a`, `5e013d14`, `95125852`).

Process note, recorded because ~137 of the window's commits are it rather than product: changes landed through a checksummed-chunk transfer and per-feature verification pipeline before publication to main; those commits carry no product semantics of their own.

## Native proof automation — 2026-09-08 (America/New_York)

- `175bdcf7`: rewrite lemmas infer remaining explicit/implicit parameters and universes from goal occurrences; proved local side conditions can determine remaining parameters. Failed alternatives do not leak assignments.
- `3377252e`: source `simp only` repeatedly applies an explicit rule set and constructs actual transport proofs. It distinguishes a solved equality from a remaining goal and stops visibly on cycles or budget exhaustion.
- Explicit simplification lists can unfold selected safe definitions and local lets, preserving polymorphic arguments and local shadowing. Installed file-checking tests exercise `examples/native_simplification.lean` and multi-file failure atomicity.
- Independent-checker conversion now reduces applicable beta/delta/zeta heads before rejecting unequal arguments, and sees scoped let values during dependent body inference. No shared primary semantic code or second admission door was introduced.

Scope and verification boundaries: [Native source proofs](docs/NATIVE_SOURCE_PROOFS.md). This addition does not claim default-set simp, general instance synthesis, full Lean compatibility, or a full-workspace release gate.

## Timeline

| Milestone | Date | Summary |
|---|---|---|
| [`45e3bd2a`](https://github.com/Dicklesworthstone/franken_lean/commit/45e3bd2a79a0ea9cbcbb81ecaaa6ec296ca86e79) | 2026-07-21 | Project, comprehensive plan, README, AGENTS, license, and initial Beads graph. |
| [`3df0543d`](https://github.com/Dicklesworthstone/franken_lean/commit/3df0543d9537b0a930e7e72ba9b779bfa0e49ad5) | 2026-07-22 | Plan §21 Rust workspace, pinned nightly, and structural dependency gate. |
| [`9a8860ab`](https://github.com/Dicklesworthstone/franken_lean/commit/9a8860aba1bf88cf68d4c01785126e8dca6d9435) | 2026-08-19 | Bounded native `lean` personality, checker and olean reconstruction, and Golem source execution. |
| [`ea891c23`](https://github.com/Dicklesworthstone/franken_lean/commit/ea891c23fb4c44ac4d5020715d9c0121fdc90c32) | 2026-09-01 | Evidence-graded checker frontier, executable agent-control plane, and stateful Full-sync Lantern groundwork. |
| [`ab417cc9`](https://github.com/Dicklesworthstone/franken_lean/commit/ab417cc985dec40518d3e4318626c3a9bf4f0387) | 2026-09-02 | Modular Lantern dispatcher, diagnostic publication authority, bounded waits, and public framed transcripts. |
| [`c150fa9e`](https://github.com/Dicklesworthstone/franken_lean/commit/c150fa9e9c690f13303161bd3ab96b718ba125ef) | 2026-09-02 | Strict client lifecycle, method role and parameter contracts, replay preflight, and metadata-only inspection. |
| [`3cef4983`](https://github.com/Dicklesworthstone/franken_lean/commit/3cef498352964fd6512c79f5d303e3d92fc045a1) | 2026-09-02 | Document-semantic client sessions, structural server transcripts, and initial bidirectional ID correlation. |
| [`88d9970f`](https://github.com/Dicklesworthstone/franken_lean/commit/88d9970f9c8491f2a454516da8e01071a2f0db64) | 2026-09-02 | Cancellation-bound request identity, wait and cancellation evidence, response classification, and bounded ID retention. |
| [`0dae67c9`](https://github.com/Dicklesworthstone/franken_lean/commit/0dae67c9c800852dbd6af7527e97a9b493a2eac4) | 2026-09-02 | Method-bound response validation and exhaustive reconciliation with server result and error totals. |
| [`b528ee53`](https://github.com/Dicklesworthstone/franken_lean/commit/b528ee53b0a87816794d34ee3a9833bd8b44ecb3) | 2026-09-02 | Compiler-driven repair of the previously uncompiled Lantern tranche, stale lockfile repair, and diagnostic covenant enforcement. |
| [`6048fb9c`](https://github.com/Dicklesworthstone/franken_lean/commit/6048fb9c92ff6045bc221086a83bbb1fbeea6f18) | 2026-09-03 | Tree-wide rustfmt debt removed and formatting gate restored. |
| [`db4e3058`](https://github.com/Dicklesworthstone/franken_lean/commit/db4e30582303ee90b9f385634be96fe1fe7e9bc5) | 2026-09-03 | Exact unsaved source projection and real parser-error UTF-16 positions at installed LSP entry points. |
| [`852ca5af`](https://github.com/Dicklesworthstone/franken_lean/commit/852ca5af296e560f01187edc3a8bb98178a52efd) | 2026-09-03 | Bounded explicitly interleaved client/server timeline validation with record-order causality. |
| [`c349dc79`](https://github.com/Dicklesworthstone/franken_lean/commit/c349dc7976ab402544e3e1e2285074cfabe4c74c) | 2026-09-17 | Kernel rejects constructors outside their admitted inductive block; the source-frontend week closes with checked programs executing on Golem. |
| [`3e898188`](https://github.com/Dicklesworthstone/franken_lean/commit/3e8981886339907bda5ada6b24215991f71885ef) | 2026-09-19 | All 2,314 Init.Prelude declarations pass K1 and the independent checker. |
| [`46f63974`](https://github.com/Dicklesworthstone/franken_lean/commit/46f63974d791ac6d85280c78d9f55bd92952eba9) | 2026-09-23 | The z8j.1 course correction: fake lake `.olean` writes, fabricated `build explain` and the hard-coded `doctor` found and removed; typed refusals replace them. |
| [`fbe57852`](https://github.com/Dicklesworthstone/franken_lean/commit/fbe5785266da50de762d9759898ecd2aba7a9fd4) | 2026-09-25 | The product gate (fmt, clippy `-D warnings`, workspace tests with an executed-test floor) records its first green hosted run. |
| [`4dc0e265`](https://github.com/Dicklesworthstone/franken_lean/commit/4dc0e2655ad19a8565bc8a2f1743534d394b59df) | 2026-09-27 | Operator ruling admits the FrankenSuite into plan D1 (decision, not yet a link); the seed-dialect freeze becomes mechanical. |
| [`362ada2f`](https://github.com/Dicklesworthstone/franken_lean/commit/362ada2ff6bc1c4d28da772edf20d4f94d949b51) | 2026-10-05 | Every pinned stdlib module accepted by the council — 2,433 modules, 215,136 declarations, 0 failed; G1 splits into correctness and performance (`9c2a7e61`). |
| [`c43130c9`](https://github.com/Dicklesworthstone/franken_lean/commit/c43130c930a9687495a531ea001be66059a4f358) | 2026-10-06 | Combined frontier S25: 8,973 of 11,083 modules accepted, 0 failed, 11 inconclusive roots; Float/Float32 math executes on the owned numerics plane (`4a82e447`). |

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
- mutation campaigns around conversion, recursors, quotients, proof irrelevance, and binders.

Representative commits: [`7ed677c2`](https://github.com/Dicklesworthstone/franken_lean/commit/7ed677c294339e4ce15bca65d90a653493a035a8), [`8ece0b70`](https://github.com/Dicklesworthstone/franken_lean/commit/8ece0b7086d8dbdadd4a9fe7dc3e5ec35c0e5727), [`0f21aede`](https://github.com/Dicklesworthstone/franken_lean/commit/0f21aede1109f76719d579994858498721a90591), `06ba84b2`.

## 3. Marrow ABI twin, `.olean` plane, and Grimoire — 2026-07-22 → 2026-07-26

Landed:

- `lean_object` compatibility heap, tri-state RC, membrane, and ownership shadows;
- compacted-region mmap and relocation substrate used by artifact loading;
- persistent environment snapshots and bounded declaration admission;
- stack-safe term and level destruction plus deterministic traversal and encoding;
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
- FIR, FLBC, and the Golem interpreter substrate;
- governed ABI values, inline caches, heartbeat and check-system behavior, and bounded IO and task slices;
- independent checker admission for axioms, definitions, theorems, opaques, mutual blocks, inference, defeq, and selected inductive and recursor forms;
- owned deterministic libm baseline and additional ABI effects.

Representative commits: [`7c48295c`](https://github.com/Dicklesworthstone/franken_lean/commit/7c48295c0c58bf78862032ecf7445cdae80be26b), `be81a269`, `286d1f04`, `ea3bbbf6`, [`654edb49`](https://github.com/Dicklesworthstone/franken_lean/commit/654edb49c474f2af123e3a744c569f6d050fb8ed).

## 6. Native CLI, source execution, artifact reconstruction, and trust surfaces — 2026-08-10 → 2026-08-23

Landed:

- `fln run`, `fln flbc run`, `fln check-olean`, bounded inspect and diff, and related artifact commands;
- Golem execution for a growing closed Nat, Bool, and String subset;
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
- bounded `waitForDiagnostics`, exact cancellation, and deterministic close and shutdown completion;
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
- structural server transcript validation for notifications and result or error responses;
- known server notification payload checks;
- canonical request-ID correlation using exact number lexemes, decoded string identity, and deterministic re-escaping;
- bounded client request, server response, decoded metadata, and correlation indexes;
- exact one-to-one response joins with no missing, duplicate, or unsolicited responses.

Representative commits: [`025c4c86`](https://github.com/Dicklesworthstone/franken_lean/commit/025c4c86018484177a1ba1e02c908373bfd29fa3), [`c150fa9e`](https://github.com/Dicklesworthstone/franken_lean/commit/c150fa9e9c690f13303161bd3ab96b718ba125ef), `a1a4fa8f`, `c633fb62`, `53e2f14d`, `691b6d6b`, `f797d305`, `4c10c660`, `a17ae30e`.

## 11. Cancellation-bound and method-bound response evidence — 2026-09-02

Landed:

- `fln.lsp-client-session/3` with globally unique canonical request IDs and explicit count and byte limits;
- prior-request authority for every non-null cancellation target;
- duplicate cancellation refusal and diagnostic-wait versus other-request classification;
- covered-versus-future diagnostic-wait counts;
- cancellation state stored on the existing bounded request record rather than another copied-ID map;
- independent join-side reconstruction of request and cancellation indexes;
- eventual cancelled-target classification as `RequestCancelled`, normal result, or another valid error;
- `fln.lsp-client-server-correlation/5` plus `fln.lsp-method-response/1` outer response contracts for initialize, shutdown, waits, current no-information editor methods, unsupported RPC, and unknown methods;
- exact reconciliation of method-derived result and error classes with the structural server totals;
- installed-binary evidence proving that the correct ID with the wrong method behavior fails closed.

Separate streams still do not establish whether cancellation preceded the response.

Representative commits: [`5df76e2b`](https://github.com/Dicklesworthstone/franken_lean/commit/5df76e2b23d6d5a1b5591e6a7acaf6b47c535140), [`88d9970f`](https://github.com/Dicklesworthstone/franken_lean/commit/88d9970f9c8491f2a454516da8e01071a2f0db64), [`9c498a51`](https://github.com/Dicklesworthstone/franken_lean/commit/9c498a514593d25b000ffe8032d12235e95f346a), [`0dae67c9`](https://github.com/Dicklesworthstone/franken_lean/commit/0dae67c9c800852dbd6af7527e97a9b493a2eac4).

## 12. Compiler-driven Lantern repair and gate restoration — 2026-09-02 → 2026-09-03

A compiler-equipped review found that the large September 2 transcript tranche had never actually built in its authoring environment. The repair landed as its own evidence event rather than being hidden in later feature work.

Landed:

- named lifetime fixes in dispatch and JSON helper seams;
- format-argument and integer-inference repairs in transcript binaries;
- callback lifetime correction so synchronous test callbacks need not be `'static`;
- a refreshed `Cargo.lock` matching newly added workspace dependencies;
- strict four-part diagnostic outcome enforcement, including exact unsigned-zero count and omission on non-authoritative outcomes;
- corrected tests whose fixtures contradicted the documented covenant;
- mandatory `#![forbid(unsafe_code)]` on new test roots;
- tree-wide rustfmt normalization restoring the formatting gate.

Observed at the repair commit: workspace check and clippy passed, the focused `fln-server` and `fln-cli` suites reported 367 passing tests, and the subsequent formatting commit left those gates green.

Representative commits: [`b528ee53`](https://github.com/Dicklesworthstone/franken_lean/commit/b528ee53b0a87816794d34ee3a9833bd8b44ecb3), [`6048fb9c`](https://github.com/Dicklesworthstone/franken_lean/commit/6048fb9c92ff6045bc221086a83bbb1fbeea6f18), [`91f9fb3f`](https://github.com/Dicklesworthstone/franken_lean/commit/91f9fb3f9caf48a67842b3fbb330af69e4dcda65).

## 13. Source-aware installed LSP bridge and parser positions — 2026-09-03

Landed:

- one shared binary-side server adapter used by `fln serve-lsp` and `lean --server`;
- exact unsaved URI and text snapshots passed through `project_with_sources`;
- removal of substring-based rendered-message inspection and hand-built duplicate clearing from the installed path;
- exact arbitrary URI preservation, including already encoded file URIs and non-hierarchical schemes;
- a strict trailing-argument refusal for `fln serve-lsp`;
- parser `BytePos` propagation through the frontend and engine error facades;
- byte offset to `FileMap` position to LSP UTF-16 conversion against the exact unsaved source;
- installed-process regressions for `%2520` double-encoding and a second-line syntax error after a non-BMP character.

Observed by the compiler-equipped follow-up: the focused installed CLI LSP suite passed 4/4, and the parser, elaborator facade, engine, CLI, clippy, and formatting checks used by that tranche were green.

Elaboration and kernel failures remain mostly file-head diagnostics because those refusal and verdict paths do not yet carry source positions.

Representative commits: [`0aedf32b`](https://github.com/Dicklesworthstone/franken_lean/commit/0aedf32b9637d84d316054c4cb94540bcaead51a), [`f9da6fa4`](https://github.com/Dicklesworthstone/franken_lean/commit/f9da6fa4c81f6051e660a9156304521d36d0e69e), [`db4e3058`](https://github.com/Dicklesworthstone/franken_lean/commit/db4e30582303ee90b9f385634be96fe1fe7e9bc5), [`7e22255a`](https://github.com/Dicklesworthstone/franken_lean/commit/7e22255a573a056f1a15662358d4dbe846e0cbea).

## 14. Explicitly interleaved record-order causality — 2026-09-03

Landed:

- `fln-lsp-timeline TIMELINE` over typed outer frames using `fln.lsp-interleaved-event/1`;
- bounded projection back into the existing strict client-session and server-transcript validators;
- reuse of canonical request identity, cancellation authority, method-response contracts, and correlation schema v5 rather than introducing parallel protocol semantics;
- request-before-response and at-most-one-response enforcement;
- initialize-response-before-initialized and shutdown-response-before-exit enforcement;
- cancellation-before-target-response enforcement, including rejection of cancellation after response;
- duplicate cancellation and response refusal plus no-event-after-exit enforcement;
- `fln.lsp-interleaved-timeline/1` with `fln.lsp-cross-stream-causality/1`, lifecycle event indices, explicit ceilings and zero-violation counters, and the complete nested correlation receipt;
- unit and installed-binary regressions for positive ordering, response-before-request, lifecycle inversion, cancellation inversion, post-exit activity, wrapper typing, and argument handling;
- an operational specification in [`docs/LANTERN_WIRE_REPLAY.md`](docs/LANTERN_WIRE_REPLAY.md).

Evidence boundary: the timeline target and tests are repository-owned and landed, but the environment that authored them had no Rust toolchain and used no hosted Actions. No same-session compile or test success is claimed here.

The profile proves only recorder-defined `record-order-v1`. It does not establish wall-clock time, duration, scheduler execution, active computation cancellation, producer identity, or complete document-to-progress-to-publication episodes.

Representative commits: [`852ca5af`](https://github.com/Dicklesworthstone/franken_lean/commit/852ca5af296e560f01187edc3a8bb98178a52efd), [`c1efd3e6`](https://github.com/Dicklesworthstone/franken_lean/commit/c1efd3e679ffa07eec0369337bc7c40f4983fa36), [`d7f8d397`](https://github.com/Dicklesworthstone/franken_lean/commit/d7f8d397a1d1c0e2efc57c286f2e1ff91f7f61d0).

---

## Notes for agents

- The README is the 1.0 target-state specification; use [`IMPLEMENTATION_STATUS.md`](IMPLEMENTATION_STATUS.md) for current evidence claims.
- The tracker of record is [`.beads/issues.jsonl`](.beads/issues.jsonl); Beads IDs are not GitHub Issues.
- `franken_lean-v2p` remains in progress. Every commit in the latest Lantern tranche names that bead; do not close it while semantic editor methods, document episode causality, RPC, shared imports, active cancellation, and full parity remain open.
- The Reference is an oracle and fixture source only.
- Generated contracts such as `KERNEL_CONTRACT.md`, `ABI_CONTRACT.md`, and `OLEAN_CONTRACT.md` are compatibility authorities; do not hand-copy their facts into implementation code.
- A green synthetic fixture is not a pinned-artifact claim. Sequential compatibility work reports `last proven -> first non-success -> typed class`.
- Independent client and server recordings establish no event order. An interleaved timeline may establish only the ordering semantics its producer explicitly binds.
- Request identity, method classes, cancellation classes, and timeline record order are protocol facts, not proof of editor semantics, elapsed time, or active execution.
- Full semantic Lantern and RPC, mathlib-scale closure, and release-grade distribution remain active program work even though substantial bounded slices are live.
