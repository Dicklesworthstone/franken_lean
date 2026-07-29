# G0-2 judgment-inventory coverage — row per Appendix-A rule (bead franken_lean-z6c, review amendment)

The review amendment: publish a row-per-Appendix-A judgment inventory
distinguishing real-module coverage, C0 positive/negative fixtures,
bounded-model coverage, and explicit unexercised blockers.
Unsupported/unobserved rows remain visible and bound the claim.

**Coverage columns.** P = Init.Prelude replay (2198/2198 accepted, 6 typed
artifact-incomplete, 0 rejected — `scripts/e2e/kernel_replay.sh`, census
receipted). S = the Std leg of the chosen set (Std.Data.HashMap.Basic: 92/92 accepted
over a 165-module closure, `chosen_set_replays_and_witnesses`, receipt
`crates/fln-conformance/evidence/g02_kernel_verdict/chosen_set_v4.32.0.jsonl`).
M = the mathlib leg (Mathlib.Order.Basic: 376/376 accepted over a
1286-module closure). C3 =
the C3 fixture pair plus the pinned-leanchecker foreign witness
(`scripts/tribunal/leanchecker_witness.sh`, ReferenceKernelOracle). C0 = the
named k1_judgments/consensus fixture anchoring the rule. Model = bounded-model
suites (budget_parity, depth_stack_calibration, thread_matrix_determinism).
**Blocker** = an explicit unexercised row; it stays visible and bounds the
claim rather than being silently absent.

Every "accepted" below is a verdict of the one authority (`fln_kernel::check`)
over real Reference declarations; a rule listed as exercised means at least
one replayed declaration's check path required it (typing paths for 2,666
accepted declarations across the three legs; the frontier/inductive rows are
admitted under the FULL ruleset since franken_lean-8ce, and 6 typed
artifact-incomplete declarations are counted separately per FL-INV-07).

| rule | title | real-module | C0 fixture | model | status |
|---|---|---|---|---|---|
| KR-100 | Preconditions — closed terms, resource hook | P S M C3 | — | budget_parity | covered |
| KR-101 | Bound variables are unreachable | P S M C3 (negative: every checked term is closed) | — | — | covered-by-construction |
| KR-102 | Free variables | P S M C3 | — | — | covered |
| KR-103 | Metavariables are rejected | P S M (negative: olean declarations carry no metas; admission refuses them) | — | — | covered-by-construction |
| KR-104 | Sort | P S M C3 | — | — | covered |
| KR-105 | Constants | P S M C3 | — | — | covered |
| KR-106 | Application | P S M C3 | — | — | covered |
| KR-107 | Lambda | P S M C3 | k1_judgments | — | covered |
| KR-108 | Dependent function types — the imax rule | P S M C3 | k1_judgments (2 anchors) | — | covered |
| KR-109 | Let | P S M C3 | k1_judgments | — | covered |
| KR-110 | Literals | P S M C3 | k1_judgments | — | covered |
| KR-111 | Metadata is transparent | P S M C3 | k1_judgments | — | covered |
| KR-112 | Projections | P S M C3 | k1_judgments | — | covered |
| KR-200 | The whnf strategy | P S M C3 | — | depth_stack_calibration | covered |
| KR-201 | whnf-core performs no delta | P S M C3 | k1_judgments | — | covered |
| KR-202 | Beta | P S M C3 | k1_judgments | — | covered |
| KR-203 | Zeta — let and let-bound fvars | P S M C3 | — | — | covered |
| KR-204 | Projection reduction | P S M C3 | — | — | covered |
| KR-205 | Recursor dispatch | P S M C3 | k1_judgments | — | covered |
| KR-300 | Resource hook and quick equality | P S M C3 | — | budget_parity | covered |
| KR-301 | Quick structural/hash equality | P S M C3 | — | — | covered |
| KR-302 | Binder congruence | P S M C3 | k1_judgments (2 anchors) | — | covered |
| KR-303 | Level equality | P S M C3 | k1_judgments | — | covered |
| KR-304 | The decide shortcut | P S M C3 | — | — | covered |
| KR-305 | Cheap normalization, projections deferred | P S M C3 | — | — | covered |
| KR-306 | Definitional proof irrelevance in Prop | P S M C3 | k1_judgments (2 anchors) | — | covered |
| KR-307 | The lazy-delta ladder | P S M C3 | — | — | covered |
| KR-308 | Nat successor offsets | P S M C3 | — | — | covered |
| KR-309 | Delta ordering by definitional height | P S M C3 | — | — | covered |
| KR-310 | Post-delta syntactic closure | P S M C3 | k1_judgments (3 anchors) | — | covered |
| KR-311 | Application congruence | P S M C3 | — | — | covered |
| KR-312 | Eta — functions and structures | P S M C3 | k1_judgments | — | covered |
| KR-313 | Nat literal acceleration — the exact operation set | P S M C3 (7 literal-family rejects triaged here 07-23, all converted by the KR-313/314 work) | k1_judgments (6 anchors) | — | covered |
| KR-314 | String literal rules | P S M C3 | k1_judgments (3 anchors) | — | covered |
| KR-315 | Unit-like eta | P S M C3 | k1_judgments (2 anchors) | — | covered |
| KR-316 | Iota — recursor computation | P S M C3 (the largest triaged gap family, converted by the recursor slice fln-5p2) | k1_judgments (4 anchors) | — | covered |
| KR-317 | K-like reduction | P S M C3 (converted by fln-5p2's KR-317 K-conversion) | k1_judgments (2 anchors) | — | covered |
| KR-318 | Native reduction hooks | — | — | — | **BLOCKER: unexercised** — K1's bootstrap has no native-hook lane; `native_decide`-class evaluation is Anvil/Golem territory, and no real-module declaration exercises a native hook through K1. Bounds the claim: nothing here says K1 computes native-accelerated results. |
| KR-400 | Inference hook | P S M C3 | — | budget_parity | covered |
| KR-401 | Normalization hook | P S M C3 | — | budget_parity | covered |
| KR-402 | Defeq hook | P S M C3 | — | budget_parity | covered |
| KR-403 | The counter mechanism | P S M C3 | — | budget_parity | covered |
| KR-404 | Diagnostics are never limits | P S M C3 (typed Inconclusive outcomes observed in the census) | — | — | covered |
| KR-500 | Level normalization, including imax collapse | P S M C3 | k1_judgments | — | covered |
| KR-501 | Level equivalence | P S M C3 | — | — | covered |
| KR-600 | Block preliminaries | P S M C3 (mutual blocks across all three legs) | — | — | covered |
| KR-601 | Shared parameters across a mutual block | P S M C3 | — | — | covered |
| KR-602 | One universe per mutual block | P S M C3 | — | — | covered |
| KR-603 | Constructor validity | P S M C3 | — | — | covered |
| KR-604 | Field universes — the Prop exception | P S M C3 | test anchors (2 files) | — | covered |
| KR-605 | Valid recursive occurrence shape | P S M C3 | test anchors (2 files) | — | covered |
| KR-606 | Strict positivity | P S M C3 (positive: every replayed inductive validates; the mandated-mutant lane plants its skip) | test anchors (2 files) | — | covered |
| KR-607 | Recursivity and reflexivity flags | P S M C3 | — | — | covered |
| KR-608 | Nested inductives compile to mutual blocks | P S M C3 (nested blocks admitted under the FULL ruleset — franken_lean-8ce) | test anchors (2 files) | — | covered |
| KR-700 | When elimination is restricted to Prop | P S M C3 | test anchors (2 files) | — | covered |
| KR-701 | The subsingleton criterion | P S M C3 | test anchors (2 files) | — | covered |
| KR-702 | The elimination level | P S M C3 | — | — | covered |
| KR-800 | Motives and major premise | P S M C3 | test anchors (2 files) | — | covered |
| KR-801 | Minor premises with induction hypotheses | P S M C3 | — | — | covered |
| KR-802 | The recursor type | P S M C3 | test anchors (2 files) | — | covered |
| KR-803 | Iota right-hand sides | P S M C3 | — | — | covered |
| KR-900 | Projection typing | P S M C3 | — | — | covered |
| KR-901 | No data escapes Prop through projections | P S M C3 | test anchors (2 files) | — | covered |
| KR-902 | Projection computation | P S M C3 | — | — | covered |
| KR-903 | Structure eta coherence | P S M C3 (the typeclass-structure casesOn/recOn/noConfusionType family triaged to fln-d4x's KR-903 hypothesis, converted) | test anchors (2 files) | — | covered |
| KR-950 | Initialization requires Eq | P S M C3 | — | — | covered |
| KR-951 | Quot | P S M C3 | — | — | covered |
| KR-952 | Quot.mk | P S M C3 | — | — | covered |
| KR-953 | Quot.lift | P S M C3 | — | — | covered |
| KR-954 | Quot.ind | P S M C3 | — | — | covered |
| KR-955 | Quot computation | P S M C3 (converted by fln-5p2's KR-955) | test anchors (2 files) | — | covered |
| KR-970 | One name, one constant | P S M C3 (the one-name law asserted on every admission) | — | — | covered |
| KR-971 | Distinct level parameters | P S M C3 | — | — | covered |
| KR-972 | Well-formed constant preamble | P S M C3 | test anchors (3 files) | — | covered |
| KR-973 | Axioms | P S M C3 (axioms admitted by rule) | test anchors (2 files) | — | covered |
| KR-974 | Definitions, theorems, opaques | P S M C3 | test anchors (2 files) | — | covered |
| KR-975 | The unsafe quarantine | P S M C3 (unsafe rows are oracle-unscorable skips by design) | — | — | covered-by-construction |
| KR-976 | The partial quarantine | — | — | — | **BLOCKER: oracle-unscorable by design** — the Reference itself never issues a kernel verdict for `partial` declarations, so no real-module row can ever carry one; the rule is exercised as a quarantine skip, and the row stays here so the claim's boundary is visible. |
| KR-977 | Mutual definitions are unsafe-only | — | — | — | **BLOCKER: same shape as KR-976** — unsafe-quarantined by construction; visible, never silently absent. |
| KR-978 | The unchecked door is not a rule | P S M C3 (negative: every admitted declaration passed the one authority; nothing entered unchecked) | — | — | covered-by-construction |

## What this table binds

1. **2,666 accepted declarations across three real modules** (2198 Init.Prelude
   + 92 Std + 376 mathlib, each with its foreign-witness
   agreement), with every rejection either converted by named follow-ups or
   triaged to a pre-classified family. No verdict here is implicit: each is
   `fln_kernel::check` over real Reference declarations, and the two chosen
   legs are diffed against leanchecker as ReferenceKernelOracle.
2. **Two explicit blockers** (KR-318, KR-976/KR-977) remain visible: native
   reduction hooks are unexercised, and the quarantine rules are
   oracle-unscorable by design. Nothing in the G0-2 claim reads past them.
3. The C0 column cites the fixture files; the per-test anchors are greppable
   (`grep -n "KR-313" crates/fln-kernel/tests/k1_judgments.rs`).
