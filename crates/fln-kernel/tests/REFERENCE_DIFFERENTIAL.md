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

Corpus: 7 cases, all MUST-level, all agreeing.

| Direction | Cases | Rules exercised |
|---|:--:|---|
| Reference accepts → we must accept | 3 | KR-972 (type is a sort), KR-974 (theorem type is a Prop + body matches), KR-974 (definition body matches) |
| Reference rejects → we must reject | 4 | KR-974 (theorem type not a proposition), KR-974 (body type mismatch), KR-105 (unknown constant), KR-107 (binder domain not a type) |

Self-asserting floors in the harness, so a corpus that quietly stopped running
cannot report a clean pass: the case count is checked against `CASES.len()`, and
both directions must be non-empty.

### What is NOT covered — the honest half

* **Scale.** Seven hand-paired cases, not a corpus. Every case is a Lean source
  text and the `Declaration` it denotes, written side by side, and that pairing
  is the harness's weak point: a transcription error makes a case vacuous rather
  than wrong.
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
* **Rules with no case.** Everything outside the seven rows: KR-100..112 beyond
  105/107, all of whnf and defeq, inductive blocks, recursors, quotients.

## Maintenance

* Regenerating is not a thing here — verdicts are executed per run, so a pin bump
  changes the oracle automatically and any resulting disagreement surfaces as a
  finding rather than as a stale fixture.
* A new case needs both halves: the Lean source **and** the `Declaration`. If you
  cannot write the second half confidently, the case belongs in `fln-conformance`
  against decoded declarations instead of here.
* `harness_detects_divergence_when_our_side_is_broken` and
  `oracle_does_not_mistake_a_codegen_error_for_a_kernel_verdict` are load-bearing.
  They are the reason to believe a green run. Do not weaken them into smoke tests.
