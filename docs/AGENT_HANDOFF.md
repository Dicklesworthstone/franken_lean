# Deterministic agent handoffs

`scripts/agent_handoff.py` turns the repository’s existing Git, Beads, frontier-capsule, and evidence surfaces into one bounded read before an agent edits anything.

It is a **projection**, never a second tracker. Beads remains authoritative for task state, Git remains authoritative for code identity, and `fln.agent-frontier/1` comments remain authoritative for owned semantic seams.

## Create a handoff

```bash
python3 scripts/agent_handoff.py snapshot --strict > /tmp/franken-lean.handoff.json
```

The `fln.agent-handoff/1` document contains:

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

## Verify a handoff

```bash
python3 scripts/agent_handoff.py verify --current /tmp/franken-lean.handoff.json
```

Use `-` to read from standard input:

```bash
python3 scripts/agent_handoff.py snapshot --strict \
  | python3 scripts/agent_handoff.py verify --current -
```

All verification first checks the immutable anchor: the commit must exist, its tree must match, every recorded control-file entry must match that tree, and the Beads digest is recomputed from the tracker blob stored in that anchor. This means an old handoff can still be verified as historical evidence after current Beads has moved.

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

The default output is a projection. `promotion_authority` becomes true only when the snapshot is strict, the selected frontier carries strict selection authority, and no stale/invalid capsule or visible tracked-blob conflict undermines the observation.

`--output` uses create-new semantics and never replaces an existing path. The complete JSON bytes are constructed before the destination is opened. A handoff is not promotion evidence until it passes verification against the intended tree.

## Repository check

```bash
scripts/check_agent_handoff.sh
```

The check runs the hermetic regression suite, builds a strict snapshot of the current tree, and verifies that exact stream immediately through stdin. It creates no repository files and mutates neither Beads nor Git.

The focused unit suite covers deterministic bytes, strict dirty-tree refusal, no-clobber output, current and historical verification, anchored-versus-current tracker movement, tracker duplicate IDs and duplicate JSON keys, missing capsule enforcement, capsule reuse becoming stale when its tracked blob changes, and commit-message separator bytes that must not forge history records.
