# Kernel ↔ Reference differential: discrepancies, coverage, provenance

Companion to `tests/reference_differential.rs`. Three things a conformance
harness must state and this one does: what we knowingly diverge on, what is and
is not covered, and where the oracle verdicts came from.

## Provenance

| Field | Value |
|---|---|
| Reference pin | `leanprover/lean4` v4.32.0 |
| Oracle binary | `~/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean` |
| Invocation | `lean <case>.lean`, one temp file per case |
| Verdict source | **Executed**, per run — no Reference expectation is hard-coded |
| Absent-pin behaviour | typed SKIP with the reason printed, never a silent pass |

The pin path is hard-coded to the tag rather than resolved from `PATH`, so a
machine carrying a *different* Lean cannot quietly supply oracle verdicts from
the wrong Reference. RCH workers do not carry the pin: this suite must be run
locally (`cargo test --locked -p fln-kernel`).

## Discrepancies (D23 carve-outs)

**None. `CARVE_OUTS` in the harness is empty.**

A carve-out is not a convenience. AGENTS.md permits exactly one shape of
knowing divergence — soundness beats bug-parity (D23) — and the harness encodes
that asymmetry structurally rather than by convention:

| Direction | Meaning | Carve-out possible? |
|---|---|---|
| We **accept**, Reference **rejects** | Unsoundness — we admit what the trusted checker refuses | **Never.** `Divergence::classify` has no path that excuses it, and the failure text says so. |
| We **reject**, Reference **accepts** | Incompleteness | Only via an explicit `CARVE_OUTS` row naming the case and its justification. |
| Either side gives no answer | Unscorable (FL-INV-07 non-answer, or a non-verdict from the pin) | Never — a non-answer agrees with nothing, so the case fails rather than passing. |

Adding a row to `CARVE_OUTS` is a public statement that FrankenLean knowingly
disagrees with the Reference. It belongs in a commit that explains why, and it
should be mirrored here with a review date.

## Coverage accounting

> **RULE-SHAPE COVERAGE, NOT CORPUS COVERAGE.** The generator crosses sorts,
> binders and admission kinds. That says nothing about whether the pinned stdlib
> agrees with us — that is bead `fln-lst4`, it needs decoded `.olean`
> declarations and therefore `fln-conformance`, and it is the harder and more
> valuable half. A growing case count here does not discharge the Corpus
> obligation.

> **Two numbers that get quoted together, kept apart.** `kernel_replay` reports
> `checked=2198`, and those 2198 declarations are ONE module (`Init.Prelude`) —
> that is the differential's real corpus coverage today. The 158,608 constants
> across 2433 modules it also reports are a DECODE cross-check: evidence that we
> can read what the Reference wrote, not that our kernel and its kernel agree on
> a verdict.

Corpus: **23 generated cases** (was 7 hand-paired), 10 accept-direction and 13
reject-direction, across 9 distinct rule shapes, all agreeing. The suite prints
that as a summary line each run, because the count is the claim.

| Direction | Cases | Rule shapes exercised |
|---|:--:|---|
| Reference accepts → we must accept | 10 | KR-972 (type is a sort, × Prop/Type/Type 1), KR-974 (theorem type is a Prop + body matches), KR-974 (definition body matches, × 3 sorts), KR-107/974 (function type inhabited by a lambda, × 3 sorts) |
| Reference rejects → we must reject | 13 | KR-972 (type is not a sort, × 3), KR-974 (theorem type not a proposition, × 2), KR-974 (body type mismatch, × 3), KR-302 (binder domain differs, × 3), KR-105 (unknown constant), KR-107 (binder domain not a type) |

Most rules are now crossed against all three sorts rather than sampled at one,
which is what the matrix buys: when the KR-974 theorem check was deliberately
broken to re-verify the guard, it surfaced as **two** release-blocking findings
rather than one.

Self-asserting floors in the harness, so a corpus that quietly stopped running
cannot report a clean pass: both directions must be non-empty, the case count
must not collapse below 20, and the distinct rule-shape count must not fall
below 7.

### What is NOT covered — the honest half

* **Scale.** Twenty-three generated cases, not a corpus. The hand-pairing risk
  is now closed — each case is described once and both halves are derived from
  that description, so a transcription slip can no longer make a case vacuous —
  but the corpus is still synthetic declarations over axioms, not the pinned
  stdlib.
* **Whole-module replay.** Decoding real `.olean` declarations needs `fln-olean`,
  which is outside fln-kernel's `allow-direct` covenant (fln-core, fln-hash,
  fln-bignum, fln-env). That path belongs in `fln-conformance`, which already
  owns `kernel_replay`. This file does not pretend to it.
* **Kernel-only isolation.** `lean` runs the elaborator, so a rejection may be
  refused before the kernel sees it (`unknownIdentifier` is elaboration, not
  kernel). The comparison is therefore at the *declaration-admissibility* level,
  not strictly the kernel boundary. `leanchecker` ships in the pin and would
  give kernel-only verdicts over `.olean` input — the natural next step, and it
  needs the olean path above.
* **Rules with no case.** Everything outside the nine shapes above: KR-100..112
  beyond 105/107/972/974, all of whnf, defeq beyond the KR-302 domain check,
  inductive blocks, recursors, quotients. Adding an axis to `corpus()` is now
  cheap; adding a rule the generator cannot express still needs a new shape.

## Maintenance

* Regenerating is not a thing here — verdicts are executed per run, so a pin bump
  changes the oracle automatically and any resulting disagreement surfaces as a
  finding rather than as a stale fixture.
* A new case is a `Case` value in `corpus()`, described once. Build types and
  terms only through the `t_*`/`m_*` constructors — they emit the Lean rendering
  and the `Expr` together, which is the property that makes a case impossible to
  mis-pair. If a shape cannot be expressed that way, add a constructor rather
  than hand-writing one half.
* `harness_detects_divergence_when_our_side_is_broken` and
  `oracle_does_not_mistake_a_codegen_error_for_a_kernel_verdict` are load-bearing.
  They are the reason to believe a green run. Do not weaken them into smoke tests.
