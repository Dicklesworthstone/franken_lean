#!/usr/bin/env python3
"""Run the exact shared dsimp fixtures with the pinned test-only Lean oracle.

No download, runtime delegation, golden regeneration, or repository mutation.
A timeout, missing fixture, wrong Reference, or spawn failure is never counted
as an expected theorem refusal. Invoke with --lean /path/to/lean-4.32.0/bin/lean.
"""
from __future__ import annotations

import argparse
import os
from pathlib import Path
import subprocess
import sys

PIN = "8c9756b28d64dab099da31a4c09229a9e6a2ef35"
ACCEPTED = {
    "beta_zeta", "selected_definitions", "dependent_binders", "locations",
    "wildcard", "data_location", "closure", "default_rules",
    "explicit_rfl_rule", "untagged_rfl_rule", "default_transparency_rule",
    "partial_application", "rollback", "projection_eta", "local_equality",
    "erasure", "local_definition", "repeat_no_progress", "structure_projection",
    "ascription_beta",
}
REFUSED = {
    "false", "nonreflexive", "no_progress", "unknown_rule", "unknown_location",
    "late_invalid_location", "class_projection",
    "ascription_no_progress",
}


def run(command: list[str], *, env: dict[str, str], timeout: int) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, capture_output=True, text=True, env=env, timeout=timeout, check=False)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", required=True, type=Path)
    args = parser.parse_args()
    lean = args.lean.resolve(strict=True)
    root = Path(__file__).resolve().parents[1]
    fixtures = root / "crates/fln/tests/source_dsimp"
    env = {k: v for k, v in os.environ.items() if k not in {"LEAN_PATH", "LEAN_SYSROOT", "LEAN_SRC_PATH"}}
    pin = run([str(lean), "--githash"], env=env, timeout=30)
    if pin.returncode != 0 or pin.stdout.strip() != PIN:
        raise RuntimeError(f"wrong Reference: expected {PIN}, got {pin.stdout!r} {pin.stderr!r}")
    failures: list[str] = []
    count = 0
    for group, inventory, expected in [("accept", ACCEPTED, True), ("refuse", REFUSED, False)]:
        directory = fixtures / group
        observed = {path.stem for path in directory.glob("*.lean")}
        if observed != inventory:
            raise RuntimeError(f"{group} fixture inventory changed: {observed ^ inventory}")
        for name in sorted(inventory):
            path = directory / f"{name}.lean"
            result = run([str(lean), str(path)], env=env, timeout=120)
            if result.returncode not in (0, 1):
                raise RuntimeError(f"{path}: abnormal exit {result.returncode}; {result.stderr}")
            matched = (result.returncode == 0) == expected
            print(f"{group}/{name}: exit={result.returncode} matched={matched}", flush=True)
            if result.stdout:
                print(result.stdout, end="")
            if result.stderr:
                print(result.stderr, end="", file=sys.stderr)
            if not matched:
                failures.append(f"{group}/{name}")
            count += 1
    print(f"Reference {PIN}: {count - len(failures)}/{count} fixture verdicts matched")
    if failures:
        print("Mismatches: " + ", ".join(failures), file=sys.stderr)
    return bool(failures)


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        print(f"Reference check did not complete: {error}", file=sys.stderr)
        raise SystemExit(2) from error
