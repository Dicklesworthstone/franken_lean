from __future__ import annotations

import argparse
import sys
from pathlib import Path
from typing import Iterable

from .common import (
    HandoffError,
    MAX_OUTPUT_BYTES,
    SCHEMA,
    VERIFY_SCHEMA,
    canonical_json,
    die,
    repository_root,
    write_no_clobber,
)
from .snapshot import build_snapshot, verify_snapshot


def parser() -> argparse.ArgumentParser:
    root = argparse.ArgumentParser(
        description="Build or verify one bounded, deterministic FrankenLean agent handoff."
    )
    subparsers = root.add_subparsers(dest="command", required=True)
    snapshot = subparsers.add_parser("snapshot")
    snapshot.add_argument("--repo", type=Path, default=Path("."))
    snapshot.add_argument("--issues", type=Path, default=Path(".beads/issues.jsonl"))
    snapshot.add_argument("--overlay", type=Path)
    snapshot.add_argument("--owner")
    snapshot.add_argument("--limit", type=int, default=10)
    snapshot.add_argument("--recent", type=int, default=12)
    snapshot.add_argument("--strict", action="store_true")
    snapshot.add_argument("--selection-strict", action="store_true")
    snapshot.add_argument("--require-capsules", action="store_true")
    snapshot.add_argument("--include-environment", action="store_true")
    snapshot.add_argument("--output", type=Path)
    verify = subparsers.add_parser("verify")
    verify.add_argument("capsule", help="Snapshot path, or '-' for stdin")
    verify.add_argument("--repo", type=Path, default=Path("."))
    verify.add_argument("--current", action="store_true")
    return root


def main(argv: Iterable[str] | None = None) -> int:
    args = parser().parse_args(list(argv) if argv is not None else None)
    try:
        repo = repository_root(args.repo)
        if args.command == "snapshot":
            payload = canonical_json(build_snapshot(args, repo))
            if len(payload) > MAX_OUTPUT_BYTES:
                raise HandoffError(
                    f"handoff output exceeds the {MAX_OUTPUT_BYTES}-byte ceiling"
                )
            if args.output is None:
                sys.stdout.buffer.write(payload)
            else:
                write_no_clobber(args.output, payload)
            return 0
        sys.stdout.buffer.write(canonical_json(verify_snapshot(args, repo)))
        return 0
    except HandoffError as exc:
        schema = VERIFY_SCHEMA if args.command == "verify" else SCHEMA
        return die(str(exc), schema=schema)
