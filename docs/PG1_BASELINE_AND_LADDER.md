# PG-1 Baseline & Throughput Ladder (`fln-kfdr`)

- **Claim state / class:** `OBSERVED` (`bounded_model`, shared unqualified host — NOT bare-metal ratified under Plan §19.1; bare-metal ratification remains open under `fln-544`).
- **Machine-readable raw sample bundle:** [`crates/fln-conformance/evidence/pg1_baseline/v4.32.0.json`](../crates/fln-conformance/evidence/pg1_baseline/v4.32.0.json)
- **Pin:** Reference `leanprover/lean4` `v4.32.0` (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`); Corpus `mathlib4` `v4.32.0` (`81a5d257c8e410db227a6665ed08f64fea08e997`).
- **Host & cache state:** `Linux sensedemobox 7.0.0-43-generic #43-Ubuntu SMP PREEMPT_DYNAMIC x86_64`, 2 × 16-core AMD EPYC 7282 (64 hardware threads, 2 NUMA nodes), 251 GiB RAM (~124 GiB warm OS page cache; cold in-process `Environment`, `WhnfMemo`, and `ArgumentMemo` per invocation).
- **Host-qualification failures disclosed (Plan §19.2 & §22.2):**
  1. Shared multi-agent development box (observed 1-min loadavg `3.1–18.2` across 64 threads during captures).
  2. `perf_event_paranoid = 4` disallows hardware PMU counters; stack profiling used 120-sample `gdb` parent stack sampling (`0.45 s` interval) on release symbols.
  3. Parallel Reference `leanchecker` was measured across all 2,433 stdlib modules (`59.4 GiB` peak RSS); it was not run in a single process over all 8,650+ Mathlib modules because `LeanChecker.lean` spawns all module tasks concurrently (which would exceed 251 GiB RAM). Mathlib Reference baselines were therefore measured per-module sequentially via `Lean.Environment.replay` over full tripartite `.olean` / `.olean.server` / `.olean.private` parts.

---

## 1. Corpus-Scale Baselines vs. Live Reference (`v4.32.0`)

| Corpus & Engine | Modules | Decls | Wall | CPU / Summed | Peak RSS | Throughput | Ratio vs. Ref |
|---|---:|---:|---:|---:|---:|---:|---:|
| **Ref `leanchecker Init Std Lean` (parallel, tripartite)** | 2,433 | 215,136 | **`116.37 s`** | `982.65 s` user + `769.98 s` sys | `59.4 GiB` | `1,848.7 decls/s` | `1.00×` |
| **Ref `leanchecker --fresh Init` (1t, public `Init`)** | — | — | **`86.07 s`** | `84.38 s` user + `1.67 s` sys | `516.8 MiB` | — | — |
| **FrankenLean K1-only stdlib (`corpus_thread_matrix`, 1t)** | 2,433 | 206,867 units | `1,299.9 s` | `1,299.9 s` | — | `159.1 units/s` | **`1.32×`** Ref user CPU |
| **FrankenLean K1-only stdlib (`corpus_thread_matrix`, 32t)** | 2,433 | 206,867 units | `234.5 s` | — | — | `882.2 units/s` | **`2.02×`** Ref wall (`5.54×` scaling) |
| **FrankenLean council stdlib (`v4.32.0.json`, `--jobs 16`)** | 2,433 | 215,136 | `3,908 s` | `12,812.2 s` summed | — | `55.1 decls/s` | **`33.6×`** Ref wall (`13.0×` Ref user) |
| **FrankenLean council combined (`S26.json`, `--jobs 24`)** | 11,083 (9,131 acc) | 695,958 acc | `9,267 s` | `91,038.3 s` Mathlib sum | `92.8 GiB` | `75.1 decls/s` | — |

**Key structural finding:** On the full stdlib, K1 single-thread CPU (`1,299.9 s`) is already within **`1.32×`** of the Reference C++ kernel's user CPU (`982.65 s`), whereas the full council (`12,812.2 s` summed) spends **~90% of its total compute inside `fln-checker`**, dominated by extreme defeq/WHNF search outliers.

---

## 2. Top-20 Slowest Modules vs. Live Reference (`Lean.Environment.replay`)

### 2a. Stdlib Top-20 (`44.0%` of total stdlib compute = `5,639.7 s / 12,812.2 s`) + `Init.Prelude`

| Module | Decls | Ref `replay_ms` | `v4.32.0.json` `elapsedMs` | Ratio |
|---|---:|---:|---:|---:|
| `Init.Prelude` | 2,314 | 244 ms | 4,612 ms | 18.9× |
| `Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Expr` | 61 | 3,999 ms | 973,718 ms | 243.5× |
| `Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Operations.Udiv` | 27 | 674 ms | 784,434 ms | **1,163.8×** |
| `Init.Data.Array.Extract` | 123 | 4,395 ms | 466,210 ms | 106.1× |
| `Init.Data.BitVec.Lemmas` | 2,040 | 9,916 ms | 434,478 ms | 43.8× |
| `Init.Data.Vector.Extract` | 69 | 2,811 ms | 374,092 ms | 133.1× |
| `Std.Data.DHashMap.Lemmas` | 1,100 | 1,233 ms | 346,068 ms | 280.7× |
| `Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr` | 258 | 2,807 ms | 344,819 ms | 122.8× |
| `Std.Data.DTreeMap.Internal.Balancing` | 369 | 4,192 ms | 235,697 ms | 56.2× |
| `Std.Data.DTreeMap.Lemmas` | 1,419 | 991 ms | 228,720 ms | 230.8× |
| `Init.Data.BitVec.Bitblast` | 795 | 4,439 ms | 196,679 ms | 44.3× |
| `Std.Data.ExtDHashMap.Lemmas` | 867 | 1,824 ms | 174,653 ms | 95.8× |
| `Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas` | 5 | 40 ms | 152,743 ms | **3,818.6×** |
| `Std.Data.HashMap.Lemmas` | 750 | 1,030 ms | 152,139 ms | 147.7× |
| `Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Substructure` | 50 | 140 ms | 143,828 ms | **1,027.3×** |
| `Init.Data.Int.DivMod.Lemmas` | 957 | 2,420 ms | 123,384 ms | 51.0× |
| `Std.Data.DTreeMap.Internal.Operations` | 744 | 1,993 ms | 111,388 ms | 55.9× |
| `Init.Data.String.Lemmas.Pattern.String.ForwardSearcher` | 229 | 1,545 ms | 101,575 ms | 65.7× |
| `Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Cpop` | 168 | 1,200 ms | 99,210 ms | 82.7× |
| `Init.Data.Dyadic.Basic` | 301 | 1,022 ms | 98,080 ms | 96.0× |
| `Std.Data.HashMap.RawLemmas` | 736 | 858 ms | 97,798 ms | 114.0× |

### 2b. Mathlib Top-20 from `S26.json` (`26.9%` of Mathlib compute = `24,503.8 s / 91,038.3 s`)

| Module | Decls | S26 Verdict | Ref `replay_ms` | S26 `elapsedMs` | Ratio |
|---|---:|---|---:|---:|---:|
| `Mathlib.Algebra.Category.Ring.Limits` | 380 | inconclusive | 7,812 ms | 2,909,882 ms | 372.5× |
| `Mathlib.RingTheory.TensorProduct.Maps` | 283 | inconclusive | 6,716 ms | 2,830,971 ms | 421.5× |
| `Mathlib.LinearAlgebra.CliffordAlgebra.Contraction` | 87 | inconclusive | 987 ms | 2,771,568 ms | **2,808.1×** |
| `Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory` | 175 | accepted | 1,339 ms | 2,546,312 ms | **1,901.7×** |
| `Mathlib.LinearAlgebra.TensorProduct.Tower` | 296 | accepted | 5,126 ms | 1,918,046 ms | 374.2× |
| `Mathlib.FieldTheory.IntermediateField.Basic` | 314 | accepted | 1,624 ms | 1,914,912 ms | **1,179.1×** |
| `Mathlib.LinearAlgebra.CliffordAlgebra.EvenEquiv` | 57 | accepted | 900 ms | 1,153,627 ms | **1,281.8×** |
| `Mathlib.RingTheory.Coalgebra.TensorProduct` | 88 | accepted | 2,637 ms | 1,117,379 ms | 423.7× |
| `Mathlib.FieldTheory.IntermediateField.Adjoin.Defs` | 213 | accepted | 1,255 ms | 1,016,762 ms | 810.2× |
| `Mathlib.CategoryTheory.Monoidal.Multifunctor` | 102 | accepted | 1,982 ms | 751,495 ms | 379.2× |
| `Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward` | 27 | accepted | 2,750 ms | 728,778 ms | 265.0× |
| `Mathlib.LinearAlgebra.TensorProduct.Associator` | 91 | accepted | 3,086 ms | 677,078 ms | 219.4× |
| `Mathlib.Algebra.Category.Grp.Limits` | 347 | accepted | 2,346 ms | 574,883 ms | 245.0× |
| `Mathlib.LinearAlgebra.CliffordAlgebra.Even` | 80 | accepted | 1,231 ms | 550,860 ms | 447.5× |
| `Mathlib.RingTheory.PiTensorProduct` | 114 | accepted | 1,241 ms | 520,438 ms | 419.4× |
| `Mathlib.CategoryTheory.Limits.Cones` | 796 | accepted | 3,626 ms | 518,082 ms | 142.9× |
| `Mathlib.RingTheory.Coalgebra.Convolution` | 67 | inconclusive | 888 ms | 516,453 ms | 581.6× |
| `Mathlib.LinearAlgebra.TensorProduct.Quotient` | 79 | accepted | 1,181 ms | 498,950 ms | 422.5× |
| `Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence` | 54 | accepted | 376 ms | 495,040 ms | **1,316.6×** |
| `Mathlib.Combinatorics.SimpleGraph.Regularity.Chunk` | 56 | inconclusive | 2,229 ms | 492,318 ms | 220.9× |

---

## 3. Phase Breakdown & 120-Sample Release Stack Profile

Using [`crates/fln-admission/tests/pg1_phase_profile.rs`](../crates/fln-admission/tests/pg1_phase_profile.rs) (release build, same host):

- **`Init.Prelude` (2,314 decls, baseline median `3,407.8 ms`, live Ref `286 ms`):**
  decode primary `4.1%` (`140.0 ms`), decode checker `5.1%` (`174.2 ms`), plan `0.9%` (`29.6 ms`), K1 kernel `36.2%` (`1,234.8 ms`, `1,348,805` steps), `fln-checker`+proj+pub `53.9%` (`1,835.4 ms`).
- **`Init.Data.Array.Extract` (123 decls, baseline `149,599.4 ms`, live Ref `4,096 ms`):**
  decode primary `0.1%` (`137.4 ms`), decode checker `0.1%` (`204.9 ms`), plan `0.0%` (`33.4 ms`), K1 kernel `10.8%` (`16,114.2 ms`, `23,504,368` steps — `3.93×` Ref), **`fln-checker`+proj+pub `89.0%` (`133,109.5 ms` — `32.5×` Ref)**.
- **120-sample `gdb` stack profile on `Init.Data.Array.Extract` (Wave 1 binary):**
  - Inclusive stack share: `fln-checker::admit` **`84.2%`** (`defeq::regular_same_head_apps_def_eq` **`70.8%`** → `whnf` **`64.2%`** → `Reducer::finish` **`39.2%`** → `Composer::copy_cursor` **`27.5%`** + `term::Transformer::run` **`18.3%`**); K1 `TypeChecker::infer_core_mode` **`10.8%`**.
  - Self (leaf) hotspots: allocator (`malloc`/`free`/`realloc`/`finish_grow`) **`14.2%`**, SipHash + `RandomState::hash_one::<&u64>` **`8.3%`**, `fln_core::Expr::drop` **`6.7%`** (>60% of K1's remaining share), `expression_owned_units` **`5.0%`**, `term::Transformer::run` **`5.0%`**, `Composer::copy_cursor` **`5.0%`**, `Composer::push_expression_charged` **`4.2%`**.

---

## 4. Measured Optimization Deltas (Same-Invocation A/B/C vs. Live Reference)

Zero lines added to `fln-kernel` (`11,105 / 12,000` LOC unchanged); bit-identical K1 step counts (`1,348,805` on `Init.Prelude`, `23,504,368` on `Init.Data.Array.Extract`).

| Workload & Metric | Live Ref `replay_ms` | Baseline (`1871ec08`) | Wave 1 (`fdae8e3ee`) | Wave 2 (`52be87f73`) | Total Delta |
|---|---:|---:|---:|---:|---:|
| **`Init.Prelude` total (3× median)** | `286 ms` | `3,407.8 ms` (`11.9×`) | `3,184.1 ms` (`-6.6%`) | **`3,110.9 ms`** (`10.9×`) | **`-8.7%`** |
| `Init.Prelude` K1 kernel | `286 ms` | `1,234.8 ms` (`4.32×`) | `980.9 ms` (`-20.6%`) | **`975.5 ms`** (`3.41×`) | **`-21.0%`** |
| `Init.Prelude` `fln-checker`+proj+pub | `286 ms` | `1,835.4 ms` | `1,847.3 ms` (`+0.6%`) | **`1,751.0 ms`** | **`-4.6%`** |
| **`Init.Data.Array.Extract` 139-dep closure (16t)** | — | `179.9 s` | `175.2 s` (`-2.6%`) | **`149.3 s`** | **`-17.0%`** |
| **`Init.Data.Array.Extract` total** | `4,096 / 4,475 ms` | `149,599.4 ms` (`36.5×`) | `141,429.4 ms` (`-5.5%`) | **`120,324.5 ms`** (`26.9×`) | **`-19.6%`** |
| `Init.Data.Array.Extract` K1 kernel | `4,096 / 4,475 ms` | `16,114.2 ms` (`3.93×`) | `12,399.6 ms` (`-23.1%`) | **`13,234.8 ms`** (`2.96×`) | **`-17.9%`** |
| `Init.Data.Array.Extract` `fln-checker`+proj+pub | `4,096 / 4,475 ms` | `133,109.5 ms` (`32.5×`) | `128,664.7 ms` (`-3.3%`) | **`106,728.4 ms`** (`23.8×`) | **`-19.8%`** |
| Top #1 unit (`Array.extract_append._proof_1_1` chk) | — | `25,821.2 ms` | `25,694.0 ms` | **`20,345.6 ms`** | **`-21.2%`** |

> **Honest loss recorded & reverted (Rule 0.5):** An inline `[Option<Arc<ExprNode>>; 8]` small stack in `fln-core::expr::Expr::drop` was tested alongside Wave 2 and **regressed K1 by `+7.4%` on `Init.Prelude` (`947.5 -> 1,017.5 ms`) and `+19.0%` on `Init.Data.Array.Extract` (`12,399.6 -> 14,757.4 ms`)** because zeroing 64 bytes of stack + drop-glue penalized the 95% shared-clone drop fast path. It was immediately reverted prior to `52be87f73`.

---

## 5. Ordered PG-1 Optimization Lever Ladder

| Rung | Status | Lever | Measured / Projected Gain | Tracking |
|---:|---|---|---|---|
| **1** | **LANDED** (`fdae8e3ee`) | Pointer-identity structural equality & inline stack worklists in `fln-core` (`Expr`/`Level`/`Name`) + single-`Arc` precomputed-hash `WireExpr`/`WireName` | **Measured:** K1 `-20.6%` to `-23.1%` (0 kernel LOC) | `fln-kfdr` |
| **2** | **LANDED** (`52be87f73`) | `fln-checker` WHNF double-copy elimination (`Reducer::finish`), zero-copy `run_at` quick-eq in `regular_same_head_apps_def_eq`, sparse/dense `SlotMap` & `Visited::CopySparse`, single-source sharing bypass, `PrehashedMap`/`FastHashMap` removing SipHash/`RandomState`, shared `WhnfMemo` in `Inferer::proof_conversion` | **Measured:** `fln-checker` `-19.8%` on `Init.Data.Array.Extract`, 139-module parallel closure `-17.0%` (0 kernel LOC) | `fln-kfdr` |
| **3** | **NEXT** | Plan §8.3c `standard` council policy (content-seeded checker sample + high-risk forms) **and/or** conversion-witness replay so `fln-checker` verifies K1 conversion DAGs instead of re-searching | **Projected: 5×–15×** aggregate council wall reduction; collapses 100×–3,800× BVDecide & Mathlib checker outliers | `fln-9908`, `fln-r15-decision-vgwl` |
| **4** | **OPEN** | Shared immutable `Environment` image across frontier jobs + cross-module decode reuse + intra-module declaration-DAG parallelism | **Projected:** removes `92.8 GiB` RSS ceiling (unlocks 32+ jobs) and removes per-module barriers (`5.54×` → near-linear 32t scaling) | `fln-f0ux`, `fln-frontier-rows-depend-on-jobs-2g96` |
| **5** | **OPEN** | Global hash-consed term interning + interned-id WHNF/defeq caches + cold-path `Expr::drop` drain (entered only after `Arc::into_inner` succeeds) | **Projected: 2×–3×** K1 speedup (bringing K1 from `1.3×–3.0×` Reference CPU to parity/faster) | `franken_lean-z8j.1.13` |
