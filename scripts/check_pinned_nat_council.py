#!/usr/bin/env python3
"""Run the real pinned Init.Nat two-checker council regression locally.

This is intentionally a thin launcher around the Rust test. It exists so an
agent does not have to remember the elan path spelling, the ignored-test
invocation, or which environment variable binds the Reference library.
"""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import re
import subprocess
import sys

REFERENCE_RE = re.compile(r"^v[0-9]+\.[0-9]+\.[0-9]+(?:[.-][A-Za-z0-9.-]+)?$")
TEST_NAME = "pinned_init_nat_completes_the_two_checker_council"


def repo_root() -> Path:
    return Path(__file__).resolve().parent.parent


def reference_tag(root: Path) -> str:
    rows: list[str] = []
    for raw in (root / "SUITE.lock").read_text(encoding="utf-8").splitlines():
        line = raw.split("#", 1)[0].strip()
        if line.startswith("reference "):
            rows.append(line)
    if len(rows) != 1:
        raise ValueError(f"SUITE.lock must contain exactly one reference row; found {len(rows)}")
    fields = {}
    for token in rows[0].split()[1:]:
        if "=" in token:
            key, value = token.split("=", 1)
            fields[key] = value
    tag = fields.get("tag")
    if tag is None or REFERENCE_RE.fullmatch(tag) is None:
        raise ValueError(f"SUITE.lock reference tag is missing or invalid: {tag!r}")
    return tag


def default_reference_lib(tag: str) -> Path:
    home = Path.home()
    return home / ".elan" / "toolchains" / f"leanprover--lean4---{tag}" / "lib" / "lean"


def require_prelude_chain(lib: Path) -> None:
    if not lib.is_dir():
        raise FileNotFoundError(f"Reference library is not a directory: {lib}")
    base = lib / "Init" / "Prelude.olean"
    required = [base, base.with_suffix(".olean.server"), base.with_suffix(".olean.private")]
    missing = [str(path) for path in required if not path.is_file()]
    if missing:
        raise FileNotFoundError("pinned Init.Prelude companion chain is incomplete: " + ", ".join(missing))


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Run the exact pinned Init.Nat block through FrankenLean's K1 + independent checker council"
    )
    parser.add_argument(
        "--reference-lib",
        type=Path,
        help="override the Reference library directory (otherwise FLN_REFERENCE_LIB or SUITE.lock + elan is used)",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = repo_root()
    tag = reference_tag(root)
    if args.reference_lib is not None:
        lib = args.reference_lib.expanduser().resolve()
    elif os.environ.get("FLN_REFERENCE_LIB"):
        lib = Path(os.environ["FLN_REFERENCE_LIB"]).expanduser().resolve()
    else:
        lib = default_reference_lib(tag)
    require_prelude_chain(lib)

    env = os.environ.copy()
    env["FLN_REFERENCE_LIB"] = str(lib)
    command = [
        "cargo",
        "test",
        "--locked",
        "-p",
        "fln-conformance",
        "--test",
        "pinned_nat_council",
        TEST_NAME,
        "--",
        "--ignored",
        "--exact",
        "--nocapture",
    ]
    print(f"fln.pinned-nat-council/1 reference_tag={tag} reference_lib={lib}", flush=True)
    print("command=" + " ".join(command), flush=True)
    completed = subprocess.run(command, cwd=root, env=env, check=False)
    if completed.returncode != 0:
        print(
            f"fln.pinned-nat-council/1 verdict=refused cargo_exit={completed.returncode}",
            file=sys.stderr,
            flush=True,
        )
        return completed.returncode
    print("fln.pinned-nat-council/1 verdict=pass", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (FileNotFoundError, OSError, ValueError) as error:
        print(f"fln.pinned-nat-council/1 verdict=refused reason={error}", file=sys.stderr)
        raise SystemExit(2)
