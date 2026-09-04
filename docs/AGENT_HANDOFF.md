# Deterministic agent handoffs

`scripts/agent_handoff.py` turns the repository’s existing Git, Beads, frontier-capsule, and evidence surfaces into one bounded read before an agent edits anything.

It is a **projection**, never a second tracker. Beads remains authoritative for task state, Git remains authoritative for code identity, and `fln.agent-frontier/1` comments remain authoritative for owned semantic seams.

## Create a handoff

```bash
python3 scripts/agent_handoff.py snapshot --strict > /tmp/franken-lean.handoff.json
```

The `fln.agent-handoff/2` document contains:

- the attached branch, commit, tree, and clean-tree state;
- Git blob identities for the core control documents and selector;
- the exact Beads JSONL digest, status counts, active work, deterministic ready ranking, and selected candidate;
- the latest parseable `fln.agent-frontier/1` capsule for each active bead;
- capsule freshness as `current`, `reusable`, `stale`, or `invalid`;
- tracked-blob ownership collisions visible across reusable capsules;
- Git identities and sizes for repository-owned frontier evidence;
- recent commits, tree identities, and `Bead:` trailers;
- typed warnings rather than optimistic omission.

No generation timestamp is included. Recent commit records use NUL-delimited Git output, so a commit message containing an ordinary record-separator byte cannot split or forge a history row. For the same clean repository state and options, the default output is byte-deterministic. `--include-environment` adds explicitly observational host telemetry and therefore may vary across machines.

`--strict` requires an attached clean `main` and requires every tracked control surface to be a regular Git blob rather than a symlink or another object kind. It does not require every historical `in_progress` bead to have been migrated to a capsule. Use `--require-capsules` only after the migration boundary is intentionally enforced; it refuses missing, malformed, stale, or conflicting active capsules. `--selection-strict` is separate: it asks the existing selector to exclude candidates whose non-Beads hard-filter facts remain unknown.

The snapshot reuses `scripts/frontier_select.py` rather than reimplementing task ranking. The handoff independently parses the Beads bytes with duplicate-key rejection and requires both passes to agree on the exact SHA-256 digest.

## Nomination is not a claim

For a smaller scheduling-only read, use the same production selector that the handoff imports:

```bash
python3 scripts/frontier_select.py --owner agent-session --limit 10
```

This command always emits JSON. Supplying `--owner` only permits exact matches to recorded assignments; it does not claim open work or resolve the owner of an unassigned `in_progress` bead. Such an in-progress bead remains excluded as `unowned_in_progress`. Empty/whitespace caller identities and malformed recorded assignees fail closed.

With an explicitly observed facts overlay, `--strict` on the selector (or `--selection-strict` on the handoff) excludes unknown non-Beads facts. Complete facts set the candidate's `eligibility_complete`, never its `promotion_authority`. The selector's top-level JSON also reports `read_only: true`, `live_state_verified: false`, `owner`, `strict`, and the exact issue/overlay byte digests. No overlay is represented by null overlay path/digest, not by an invented empty-file identity.

A nomination is advisory even when its input hashes are exact. Refresh live Beads readiness, the recorded assignee, and semantic-seam ownership before an explicit claim; then bind experiments and receipts to the actual Git/artifact anchor. Neither this read nor a successful handoff verification performs that state transition. The detailed implemented contract and its relationship to the proposed command surface are in [Agent Frontier Protocol §10.4](../AGENT_FRONTIER_PROTOCOL.md#104-implemented-read-only-selection-contract).

## Ranking and input boundaries

`critical_path_descendants` counts distinct non-closed descendants reachable
through non-closed blocking dependents. A closed intermediate cuts traversal:
work beyond it already has that prerequisite satisfied and is not an unlock
attributable to the candidate. Alternative live paths still count; diamond
joins count once. Reopening a prerequisite restores the live path from the
current tracker snapshot, without a separate graph or status authority.

This is potential downstream work, not a promise that one closure makes every
descendant ready. `direct_unlocks` is narrower: direct dependents whose only
unresolved blocker is the candidate. Neither score overrides a hard filter.

Both selector inputs reject duplicate decoded JSON keys within every object,
including issue fields, nested dependency records, the overlay issue-ID map,
and hard-filter facts. Escaped-equivalent spellings are the same key. Equal
repeated values are also refused; repeated names in distinct objects and key-like
text inside strings remain valid. The selector never chooses first-wins or
last-wins semantics that could erase an owner, blocker, or unavailable-toolchain
fact. Its CLI emits the existing structured refusal on stderr, exits 2, and
emits no successful selection on stdout for such inputs.

Each input is still hashed and parsed from one captured byte read. Unique keys
and exact hashes remove ambiguity; they do not turn supplied availability facts
into measured availability or grant live ownership or promotion authority.

## Verify a handoff

```bash
python3 scripts/agent_handoff.py verify --current /tmp/franken-lean.handoff.json
```

Use `-` to read from standard input:

```bash
python3 scripts/agent_handoff.py snapshot --strict \
  | python3 scripts/agent_handoff.py verify --current -
```

All verification first checks the immutable anchor: the commit must exist, its tree must match, every recorded control-file entry must match that tree, and the Beads digest is recomputed from the tracker blob stored in that anchor. An old handoff can be verified as historical evidence after current Beads has moved when it still matches the verifier's reconstruction contract. Verification uses the current verifier selector; a selector/schema change may therefore reject an older handoff. Regenerate after the ownership/eligibility contract change rather than relabeling an old payload as current.

`--current` additionally requires:

- the recorded commit and tree to equal current `HEAD`;
- branch `main`;
- a clean working tree;
- the current working-tree Beads file to retain the exact anchored digest.

A snapshot that verifies historically but not with `--current` is evidence of what an earlier agent saw, not permission to apply stale line-oriented edits. Generate a new snapshot and inspect the intervening commits.

## Capsule freshness

For each active bead with a parseable capsule:

- `current`: capsule commit is `HEAD`, its tree is exact, and all tracked blobs match;
- `reusable`: capsule commit is an ancestor of `HEAD` and all tracked blobs are unchanged;
- `stale`: the commit is not an ancestor or at least one tracked blob changed or disappeared;
- `invalid`: the capsule, anchor, tree, or declared anchor blob is malformed or unavailable.

A capsule must name its own bead and current bead state, an owner, a 40-hex commit/tree pair, and at least one normalized repository-relative tracked blob. The auditor verifies each declared blob against the capsule’s own anchor before comparing it with current `HEAD`.

Exact tracked-path overlap between reusable capsules is reported as a collision. This is intentionally narrower than semantic-seam overlap: absence of a path collision is not proof that two conceptual changes commute.

## Resource and publication rules

The tool is standard-library-only and bounds:

- Beads input: 64 MiB;
- one scanned comment: 2 MiB;
- parsed capsules: 4,096;
- tracked blobs per capsule: 256;
- recent commits: 64;
- ranked candidates: 100;
- frontier evidence files: 512;
- emitted or verified handoff: 4 MiB.

The output is a projection. With the current production selector, `tracker.selection_authority` and `authority.promotion_authority` remain false even for strict, clean snapshots: complete scheduling facts do not grant a lease, satisfy a bead's acceptance criteria, or prove a theorem. Inspect the selected candidate's `eligibility_complete` and `unknown_hard_filter_facts` for scheduling readiness instead.

`--output` uses create-new semantics and never replaces an existing path. The complete JSON bytes are constructed before the destination is opened. Verification binds an observation to the intended tree; it does not replace the required acceptance, evidence, and closure gates.

## Repository check

```bash
scripts/check_agent_handoff.sh
```

The check first runs both production-selector suites, then the handoff regression suites, builds a strict snapshot of the current tree, and verifies that exact stream immediately through stdin. It mutates neither Beads nor Git.

The focused unit suite covers deterministic bytes, strict dirty-tree refusal, no-clobber output, current and historical verification, anchored-versus-current tracker movement, tracker duplicate IDs and duplicate JSON keys, missing capsule enforcement, capsule reuse becoming stale when its tracked blob changes, and commit-message separator bytes that must not forge history records.

Some handoff unit tests intentionally use a simplified selector fixture to exercise reconstruction and tamper refusal. Their green result is not evidence that the production selector's ownership/eligibility semantics are covered. The check therefore runs the production-selector suites explicitly before the handoff suites. To run only that focused subset:

```bash
python3 -m unittest discover -s scripts -p 'test_frontier_select*.py'
```

The selector boundary suite covers closed prerequisites, live and reopened diamond paths, all 1,024 four-node DAG/status combinations, duplicate JSON keys, real CLI refusals, and valid-input controls. These are synthetic scheduling/input regressions, not real-corpus, kernel, live-tracker, or full handoff-integration evidence.
