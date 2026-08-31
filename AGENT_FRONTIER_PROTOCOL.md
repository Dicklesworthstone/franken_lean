# FrankenLean Agent Frontier Protocol

**Schema:** `fln.agent-frontier/1`
**Status:** proposed constitutional design extension
**Purpose:** make parallel agent work schedule-independent, evidence-preserving, collision-resistant, and monotonically accretive.

---

## 1. The control problem

FrankenLean is being built by many agents against a rapidly moving `main`, a dependency-shaped bead graph, pinned external artifacts, strict evidence law, and a large tower of semantic subsystems. The limiting resource is no longer code generation. It is **correct shared situational awareness**.

Without a machine-legible frontier, agents repeatedly pay for the same discovery:

- a code snapshot is mistaken for current `main`;
- a committed JSONL projection is mistaken for live bead state;
- a synthetic green is mistaken for pinned-artifact evidence;
- an old hypothesis is retried because its failure is buried in prose;
- two agents modify the same semantic seam under different task labels;
- a passing test is quoted without the exact tree, artifact, command, or first-failure boundary;
- broad engine changes are attempted when a named seed or codec shape is the actual frontier.

The remedy is not more ceremony. It is one compact, typed object that every agent can load before acting and enrich after learning: the **Frontier Capsule**.

---

## 2. System model

The agent operating system is a closed loop over five planes:

1. **Intent plane** — the comprehensive plan, invariants, compatibility contract, and bead acceptance criteria.
2. **State plane** — immutable Git objects, live bead state, ownership leases, dependency readiness, and current first failure.
3. **Experiment plane** — one bounded hypothesis, protected surfaces, exact command, and observed result.
4. **Evidence plane** — local gates, pinned-artifact runs, council receipts, Tribunal differentials, and negative evidence.
5. **Decision plane** — advance, split, defer, revert, close, or nominate the next frontier.

Every plane addresses the same semantic object through stable identifiers. A code change without a bead and capsule is an orphan. A bead closure without evidence object identifiers is an unsupported claim. An experiment without a recorded differentiator is non-accretive work.

---

## 3. Frontier Capsule

Every `in_progress` bead that changes code or evidence MUST have one current capsule in its live bead comments. The capsule is a fenced JSON object with schema `fln.agent-frontier/1`; prose may follow it, but agents must be able to parse the object without interpreting prose.

### 3.1 Minimal schema

```json
{
  "schema": "fln.agent-frontier/1",
  "bead": "fln-51y8",
  "state": "in_progress",
  "owner": "agent-or-session-id",
  "lease_observed_at": "2026-08-31T20:15:37Z",
  "anchor": {
    "branch": "main",
    "commit": "<40-hex>",
    "tree": "<40-hex>",
    "tracked_blobs": {
      "crates/fln-checker/src/admit.rs": "<40-hex>"
    }
  },
  "frontier": {
    "artifact": "Init.Prelude.olean@SUITE.lock",
    "pipeline": "decode -> reconstruct -> council K1",
    "last_proven": "declarations 1-14",
    "first_failure": "declaration 15: HEq",
    "failure_class": "structural-seed-mismatch",
    "actual_fingerprint": "sha256:<hex>",
    "expected_fingerprint": "sha256:<hex>"
  },
  "hypothesis": {
    "statement": "HEq reflexive motive is missing its type argument",
    "smallest_experiment": "change only HEq expected recursor/rule builders and fixture",
    "protected_surfaces": [
      "generic inference",
      "defeq",
      "non-HEq admission routes"
    ]
  },
  "last_green": {
    "commit": "<40-hex>",
    "commands": ["cargo test -p fln-checker"],
    "receipts": ["path-or-digest"],
    "scope": "synthetic checker suite only"
  },
  "negative_evidence": [
    {
      "attempt": "<commit-or-experiment-id>",
      "hypothesis": "collapsed hygienic values",
      "outcome": "reverted",
      "reason": "broke exact HEq fixture",
      "differentiator_required": "outer-left and inner-right locals must remain distinct"
    }
  ],
  "next": {
    "command": "<exact reproduction>",
    "success": "HEq admitted and real frontier advances",
    "failure_capture": "dual canonical tree and first divergent path"
  },
  "closure": {
    "criteria": ["bead acceptance criteria copied or referenced exactly"],
    "still_missing": ["real pinned council receipt"]
  }
}
```

### 3.2 Update rule

Update the capsule only on a **state transition**:

- ownership acquired, transferred, or released;
- anchor changed;
- first failure changed;
- hypothesis changed;
- experiment completed;
- evidence envelope expanded;
- closure predicate satisfied or disproved.

Do not append diary entries for ordinary edits. The capsule is the current control state; detailed logs belong in receipts and comments linked by digest.

### 3.3 Immutable anchoring

A capsule never says merely “current main.” It records:

- commit SHA;
- tree SHA;
- blob SHA for each claimed or edited semantic seam;
- pinned artifact identity or digest;
- exact command and mode.

Before editing, an agent compares all tracked blob hashes with live `main`. A mismatch is a rebase event, not permission to apply stale line-oriented changes.

---

## 4. Negative evidence as a first-class asset

A failed attempt is valuable only when it makes repetition harder.

Each negative-evidence row records:

- immutable attempt identifier;
- precise hypothesis;
- exact observation that falsified it;
- changed and protected surfaces;
- whether the change was reverted;
- the differentiator a future attempt must state.

An agent MUST NOT repeat a recorded failed hypothesis unless its capsule names a concrete differentiator. “Try again more carefully” is not a differentiator. Examples that are:

- a new pinned artifact or decoded telescope;
- a corrected binder scope;
- a narrower change surface;
- a new counterexample or refusal cell;
- a different scheduler seed exposing a distinct causal path.

This turns the repository into a cumulative reasoning system rather than a sequence of amnesiac coding sessions.

---

## 5. Frontier selection

Choose ready work by maximizing semantic unlock per unit of evidence cost, not by title order or code size.

A robot selector should rank ready beads by:

```text
priority
+ critical-path descendants
+ number of blocked acceptance criteria released
+ reuse of already-loaded context
+ isolation of the semantic seam
- ownership/collision risk
- expected evidence cost
- breadth of trusted-surface change
- uncertainty not reducible by one bounded experiment
```

Hard filters precede scoring:

1. dependencies are closed or explicitly waived by the bead;
2. no live ownership conflict;
3. the acceptance criterion is falsifiable;
4. a first failing boundary or discovery experiment is named;
5. required artifacts and toolchain are available;
6. the experiment does not violate the Oracle-Only Law or dependency doctrine.

When two tasks score similarly, prefer the task that produces reusable instrumentation, canonical representations, or refusal cells. Those lower the cost of every later bead.

---

## 6. One-variable experiments

Every implementation cycle should answer one question.

A valid experiment states:

- **observation:** the smallest current mismatch;
- **hypothesis:** one causal explanation;
- **intervention:** the smallest code or fixture change that distinguishes it;
- **protected surfaces:** what must not change;
- **positive cell:** exact result expected if correct;
- **negative cell:** exact forged or counterexample result that must still fail;
- **measurement:** canonical diff, typed verdict, or receipt;
- **promotion rule:** which evidence permits commit, bead advancement, or closure.

Broad refactors are separate beads unless the current acceptance criterion requires them. A local seed mismatch does not authorize generic inference surgery; a synthetic green does not authorize a compatibility claim.

---

## 7. Evidence envelopes

Every green is labeled by its envelope:

- **S0 — static:** formatting, compile, lint, structural guards.
- **S1 — synthetic:** unit/property/refusal cells generated inside the repository.
- **S2 — pinned local artifact:** exact Reference/Corpus artifact under `SUITE.lock`.
- **S3 — council:** independent seats agree under the specified policy.
- **S4 — Tribunal:** differential and metamorphic evidence across the declared matrix.
- **S5 — release:** clean-tree, reproducible, packaged, provenance-bound evidence.

Higher envelopes include lower ones only when the receipt explicitly binds the same tree and configuration. A remote green for another SHA is not evidence for the working tree. A test count without command, tree, and scope is metadata, not a receipt.

The capsule's `last_green.scope` must make overclaiming syntactically awkward.

---

## 8. First-failure monotonicity

Long compatibility pipelines report one canonical frontier:

```text
last proven unit -> first failing unit -> typed failure class
```

After every candidate change, record whether the frontier:

- advanced;
- stayed fixed with a changed failure class;
- regressed;
- became inconclusive;
- became unobservable because evidence tooling failed.

Only “advanced” is progress on a sequential conformance bead. A larger passing test count with the same first failure is useful supporting evidence but not frontier advancement.

For structured objects, store canonical fingerprints and the first divergent path rather than full dumps when possible. Full dumps remain addressable receipts.

---

## 9. Collision control

### 9.1 Semantic ownership

Ownership is declared over semantic seams, not merely files:

```text
fln-checker / Init.HEq expected recursor reconstruction
fln-server / LSP text synchronization capability surface
```

Two agents may safely edit one file only when their seams and tests are disjoint and the build-gate protocol permits it. Two different files may still conflict if they alter the same claim or artifact contract.

### 9.2 Pre-commit revalidation

Immediately before commit:

1. refresh live `main`;
2. compare tracked blob hashes;
3. inspect intervening commits touching the seam, tests, tracker, or architecture graph;
4. rerun the bounded experiment;
5. run the required local gate envelope;
6. update the capsule with the tested commit/tree;
7. commit one coherent claim.

A stale but clean patch is not safe merely because Git applies it.

### 9.3 Incremental commits

Commit boundaries follow evidence claims:

- instrumentation/refusal cell;
- semantic fix;
- real-artifact advancement;
- tracker/projection refresh;
- design protocol.

Do not combine independent claims to reduce commit count. Small immutable claims make bisecting, reverting, and multi-agent reconciliation cheaper.

---

## 10. Agent-facing control surfaces

The target ergonomic surface is one bounded read before action and one bounded write after learning.

### 10.1 Proposed robot commands

```text
fln frontier ready --robot
fln frontier show fln-51y8 --robot
fln frontier claim fln-51y8 --owner <id> --lease 45m
fln frontier verify-anchor fln-51y8
fln frontier record-experiment fln-51y8 --receipt <path>
fln frontier advance fln-51y8 --first-failure <unit>
fln frontier release fln-51y8
fln frontier audit --all --robot
```

These commands should compose existing `br`, Git, claim-matrix, Ledger, Palimpsest, and Tribunal data. They must not create a second tracker.

### 10.2 One-page agent view

`frontier show` returns, in this order:

1. acceptance criterion and dependency state;
2. immutable anchor and ownership lease;
3. last proven/first failing boundary;
4. current hypothesis and protected surfaces;
5. top negative-evidence differentiators;
6. exact next command;
7. closure evidence still missing.

Everything else is linked by digest. This ordering minimizes context load while preserving drill-down.

### 10.3 Generated projections

Human dashboards, JSONL exports, coverage views, and overlap maps are projections. They declare:

- source snapshot/digest;
- generation time;
- completeness state;
- freshness relative to live beads and `main`.

No projection silently impersonates authority.

---

## 11. Integration with the FrankenLean tower

The protocol should reuse the product's own abstractions:

- **Ledger** stores content-addressed capsules, commands, and receipts.
- **Palimpsest** links hypotheses, interventions, regressions, reverts, and first-failure movement into a causal graph.
- **Tribunal** produces evidence-envelope receipts and differential rows.
- **Synod/council** binds seat policy and agreement to exact candidate digests.
- **Envoy/MCP** exposes frontier read/claim/record operations to agents.
- **Bloodhound** retrieves prior failures by semantic fingerprints, not only text.
- **Folio** renders human-readable histories and architecture implications.
- **Lantern** displays ownership, stale anchors, blocked dependencies, and frontier motion.

The project thereby dogfoods the same provenance, determinism, and trust semantics it promises to users.

---

## 12. Guards

A lightweight `frontier-guard` should fail locally and in CI when:

- an `in_progress` code bead lacks a parseable capsule;
- the capsule anchor does not contain the claimed blob hashes;
- closure is requested with non-empty `still_missing` evidence;
- a new attempt repeats a negative-evidence hypothesis without a differentiator;
- a commit changes an authoritative semantic seam but names no bead;
- a projection is stale but rendered as complete/current;
- the reported first failure regresses without an explicit regression record;
- two unexpired ownership leases overlap on one semantic seam;
- evidence claims refer to a different tree than the code being promoted.

The guard should be read-only under the build gate and produce typed, actionable failures. It must never mutate beads, Git state, or receipts implicitly.

---

## 13. Migration

Adopt without stopping ongoing work:

1. Require capsules only for newly claimed or newly transitioned `in_progress` beads.
2. Seed capsules for the current critical-path frontier beads from their existing comments.
3. Add a parser/auditor before adding mutation commands.
4. Generate a read-only overlap/freshness report.
5. Bind capsule digests into council and Tribunal receipts.
6. Add closure guard only after the parser has survived real multi-agent use.

No historical backfill is required unless an old bead becomes active again.

---

## 14. Success criteria

The protocol succeeds when:

- a fresh agent can identify the exact current frontier and reproduce it from one bounded object;
- every repeated failed hypothesis names a genuine differentiator;
- evidence claims are automatically tied to immutable code and artifact identities;
- task selection favors critical semantic unlocks over disconnected type-shell growth;
- ownership collisions are visible before edits begin;
- handoffs preserve what was learned, not merely what was changed;
- the repository's collective understanding increases monotonically even when experiments fail.

That is the agent-accretive property: each unit of work leaves the next agent with a smaller, sharper, more trustworthy search space.
