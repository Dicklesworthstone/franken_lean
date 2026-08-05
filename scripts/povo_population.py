#!/usr/bin/env -S python3 -I -S
"""Derive the non-durable terminal citation population, using the validator's OWN instruments.

Bead `franken_lean-ephemeral-manifest-artifact-povo`. Prints two lines a caller can parse:

    povo-adopted: yes|no
    povo-nondurable-terminal: <n>

BOTH instruments must be the producer's, and that is not a style preference — it is the only way
this number has ever come out right. A hand-rolled scan reported 154 by treating tracked
directories as missing. The real classifier driven with a HAND-BUILT authority reported 430,
because passing an empty `reachable_commits` forced all 154 commit citations to classify
`unreachable_commit`. Same code, fabricated input, confident wrong answer.
"""

import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("/data/projects/franken_lean")

spec = importlib.util.spec_from_file_location("ev", ROOT / "scripts" / "evidence.py")
ev = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ev)

manifest = ROOT / "ci" / "VERIFICATION_MANIFEST.jsonl"
rows = [json.loads(line) for line in manifest.read_text().splitlines() if line.strip()]
artifacts = [a for r in rows for a in (r.get("artifacts") or [])]

authority = ev.build_verification_artifact_authority(manifest, artifacts)
states = ev.bead_tracker_projection(str(ROOT / ".beads" / "issues.jsonl"))

beads = {}
for line in (ROOT / ".beads" / "issues.jsonl").read_text().splitlines():
    if line.strip():
        record = json.loads(line)
        beads[record["id"]] = record

DURABLE = {"tracked_file", "bead_comment", "bead", "commit", "receipt", "test_function_claim"}

count = 0
for row in rows:
    bead = row.get("bead")
    if not bead:
        continue
    if beads.get(bead, {}).get("status") not in ("closed", "tombstone"):
        continue
    for artifact in row.get("artifacts") or []:
        try:
            kind = ev.verification_artifact_classification(
                bead, artifact, bead_states=states, authority=authority, receipts={}
            )
        except Exception:  # noqa: BLE001 — an unclassifiable citation is non-durable by definition
            kind = "unclassifiable"
        if kind not in DURABLE:
            count += 1

registry = ROOT / "ci" / "VERIFICATION_EVIDENCE_RECEIPTS.jsonl"
print(f"povo-adopted: {'yes' if registry.exists() else 'no'}")
print(f"povo-nondurable-terminal: {count}")
