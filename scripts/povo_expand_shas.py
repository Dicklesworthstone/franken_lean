#!/usr/bin/env -S python3 -I -S
"""Expand one owner's short commit citations to full shas — the mechanical 30% of `povo`.

Bead `franken_lean-ephemeral-manifest-artifact-povo`. The non-durable citation population is not
one problem: measured on 2026-08-05 it was 262 citations, of which **78 are `short_commit`** — the
single largest class and the only one repairable without judgement. This is that repair, scoped to
one owner so nobody edits a row they do not own.

    scripts/povo_expand_shas.py --owner cc_1              # dry run: report, change nothing
    scripts/povo_expand_shas.py --owner cc_1 --write      # rewrite that owner's rows in place

EVERY REPLACEMENT IS VERIFIED TWICE BEFORE IT IS WRITTEN, and the second check is the one that
matters. A short sha is non-durable because it can become ambiguous as the object store grows, so
widening it is only safe if it still denotes what it denoted:

  1. the short form resolves to a **commit object** — `git rev-parse <short>^{commit}`;
  2. the full form is an **ancestor of HEAD** — `git merge-base --is-ancestor <full> HEAD`.

**Without (2) this tool would launder an unreachable commit into a durable-looking citation.** That
is the neighbouring defect (`unreachable_commit`) wearing this repair as a disguise, and it would
be invisible afterwards: the citation would classify `commit` and look repaired. A short sha that
fails either check is REPORTED AND LEFT ALONE, never guessed at.

Two deliberate limits, so this is not mistaken for a migration:

* it touches **terminal** rows only, because those are the ones the durability rule judges;
* it edits **one line per row, in place**, and refuses if any other line would change — the
  manifest is a shared file with a mixed serialization history and re-serializing it reformats
  every other pane's row under your hand.
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ci" / "VERIFICATION_MANIFEST.jsonl"
TRACKER = ROOT / ".beads" / "issues.jsonl"
TERMINAL = {"closed", "tombstone"}


def git(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", "-C", str(ROOT), *args], capture_output=True, text=True, check=False
    )


def widen(short: str) -> tuple[str | None, str]:
    """The full sha, or None and the reason this one must be left alone."""
    resolved = git("rev-parse", f"{short}^{{commit}}")
    if resolved.returncode != 0:
        return None, "does not resolve to a commit object"
    full = resolved.stdout.strip()
    if git("merge-base", "--is-ancestor", full, "HEAD").returncode != 0:
        return None, f"resolves to {full[:12]} which is NOT an ancestor of HEAD"
    return full, "verified: resolves to a commit and is an ancestor of HEAD"


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--owner", required=True, help="only rows whose owner field is this")
    parser.add_argument(
        "--write",
        action="store_true",
        help="rewrite the rows; without it this reports and changes nothing",
    )
    args = parser.parse_args(argv)

    statuses = {}
    for line in TRACKER.read_text(encoding="utf-8").splitlines():
        if line.strip():
            record = json.loads(line)
            statuses[record["id"]] = record.get("status")

    original = MANIFEST.read_text(encoding="utf-8").splitlines(keepends=True)
    out: list[str] = []
    widened = skipped = rows_touched = 0
    for line in original:
        if not line.strip():
            out.append(line)
            continue
        row = json.loads(line)
        if (
            row.get("kind") != "coverage"
            or row.get("owner") != args.owner
            or statuses.get(row.get("bead")) not in TERMINAL
        ):
            out.append(line)
            continue

        artifacts, changed = [], False
        for artifact in row.get("artifacts") or []:
            short = artifact[len("commit:") :] if artifact.startswith("commit:") else ""
            if (
                short
                and len(short) < 40
                and all(c in "0123456789abcdef" for c in short)
            ):
                full, why = widen(short)
                if full is None:
                    print(f"  SKIP  {row['bead']}  commit:{short} — {why}")
                    skipped += 1
                else:
                    print(f"  WIDEN {row['bead']}  commit:{short} -> {full[:12]}…")
                    artifact = f"commit:{full}"
                    widened += 1
                    changed = True
            artifacts.append(artifact)
        if changed:
            row["artifacts"] = sorted(set(artifacts))
            line = json.dumps(row, sort_keys=True, separators=(", ", ": ")) + "\n"
            rows_touched += 1
        out.append(line)

    print(
        f"\n{args.owner}: {widened} citations widenable across {rows_touched} rows, "
        f"{skipped} left alone"
    )
    if not args.write:
        print("dry run — nothing was written. Re-run with --write to apply.")
        return 0
    if rows_touched == 0:
        print("nothing to write.")
        return 0

    untouched = sum(1 for a, b in zip(original, out) if a == b)
    if untouched != len(original) - rows_touched:
        print(
            f"REFUSING: {len(original) - rows_touched - untouched} lines other than the "
            f"{rows_touched} matched rows would change",
            file=sys.stderr,
        )
        return 2
    MANIFEST.write_text("".join(out), encoding="utf-8")
    print(f"written: {rows_touched} rows rewritten in place, {untouched} lines byte-identical")
    print("Now run validate-verification-manifest and commit the row edits with your disclosure.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
