#!/usr/bin/env python3
"""Install the reviewed IR graph command increment in an isolated test checkout.

The live command is changed only after the codec exports exist. Conflicting
source edits are a stop, never overwritten. Publication belongs to the caller,
which must run both package suites, Clippy and workspace checks first.
"""
from pathlib import Path
import hashlib

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / ".github/patches/ir-graph-cli"
TARGETS = {
    "fln-ir-check.rs": "crates/fln-olean/src/bin/fln-ir-check.rs",
    "fln-ir-graph.rs": "crates/fln-olean/src/bin/fln-ir-graph.rs",
    "ir_support.rs": "crates/fln-olean/src/bin/ir_support/mod.rs",
    "ir_archive_cli.rs": "crates/fln-olean/tests/ir_archive_cli.rs",
}
BLOBS = {
    "fln-ir-check.rs": "3536116b7f00475b77e568d874bbab2dcd8bb829",
    "fln-ir-graph.rs": "0633a3073ace803d1300b5611bf01359a8b68205",
    "ir_support.rs": "6a9b600ed6920a26bc6a78c662c6e6225b66b98b",
    "ir_archive_cli.rs": "c046e94d55fd2971f11abe37bd583638d1cc76df",
}


def blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()


def main() -> None:
    if "pub mod ir_archive;" not in (ROOT / "crates/fln-olean/src/lib.rs").read_text():
        raise SystemExit("register the graph codec before installing its consumers")
    old = ROOT / TARGETS["fln-ir-check.rs"]
    if old.is_symlink():
        raise SystemExit("command path is a symlink")
    old_bytes = old.read_bytes()
    if b"use fln_olean::ir_archive::" in old_bytes:
        for destination in TARGETS.values():
            target = ROOT / destination
            if target.is_symlink() or not target.is_file():
                raise SystemExit(f"incomplete command installation: {destination}")
        # Existing active source is not overwritten from a staged copy. The
        # caller still runs the complete suites and checks any formatting diff.
        print("already-installed")
        return
    if blob_sha(old_bytes) != "2f7901267aa757d8e85988399d55487edf90df27":
        raise SystemExit("fln-ir-check changed concurrently; reconcile instead of replacing it")
    payloads = {}
    for filename, destination in TARGETS.items():
        source = SOURCE / filename
        if source.is_symlink() or not source.is_file():
            raise SystemExit(f"missing regular source payload: {filename}")
        data = source.read_bytes()
        if blob_sha(data) != BLOBS[filename]:
            raise SystemExit(f"source payload identity changed: {filename}")
        target = ROOT / destination
        if filename != "fln-ir-check.rs" and (target.exists() or target.is_symlink()):
            raise SystemExit(f"new destination is already occupied: {destination}")
        payloads[target] = data
    for target, data in payloads.items():
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    print("installed")


if __name__ == "__main__":
    main()
