from __future__ import annotations

import os
import re
import subprocess
from pathlib import Path
from typing import Any

from .common import (
    BEAD_TRAILER,
    CONTROL_PATHS,
    HEX40,
    HandoffError,
    MAX_EVIDENCE_FILES,
    MAX_RECENT_COMMITS,
    git,
    safe_relative_path,
)


def current_anchor(repo: Path) -> dict[str, Any]:
    commit = git(repo, "rev-parse", "HEAD").stdout.strip()
    tree = git(repo, "rev-parse", "HEAD^{tree}").stdout.strip()
    branch_process = git(
        repo, "symbolic-ref", "--quiet", "--short", "HEAD", check=False
    )
    branch = branch_process.stdout.strip() if branch_process.returncode == 0 else None
    status = git(repo, "status", "--porcelain=v1", "--untracked-files=all").stdout
    if not HEX40.fullmatch(commit) or not HEX40.fullmatch(tree):
        raise HandoffError("git returned a malformed HEAD commit or tree identity")
    return {"branch": branch, "commit": commit, "tree": tree, "clean": not bool(status)}


def tree_entry(repo: Path, commit: str, path: str) -> dict[str, str] | None:
    safe_relative_path(path, "tracked path")
    line = git(repo, "ls-tree", commit, "--", path).stdout.rstrip("\n")
    if not line:
        return None
    if "\n" in line or "\t" not in line:
        raise HandoffError(f"git returned an ambiguous tree entry for {path}")
    metadata, observed_path = line.split("\t", 1)
    fields = metadata.split()
    if len(fields) != 3 or observed_path != path:
        raise HandoffError(f"git returned a malformed tree entry for {path}")
    mode, kind, sha = fields
    if not HEX40.fullmatch(sha):
        raise HandoffError(f"git returned a malformed object identity for {path}")
    return {"mode": mode, "kind": kind, "blob": sha}


def blob_bytes(
    repo: Path, commit: str, path: str, limit: int, label: str
) -> bytes:
    entry = tree_entry(repo, commit, path)
    if entry is None or entry["kind"] != "blob":
        raise HandoffError(f"{label} is not a regular tracked blob at {commit}: {path}")
    try:
        size = int(git(repo, "cat-file", "-s", entry["blob"]).stdout.strip())
    except ValueError as exc:
        raise HandoffError(f"git returned a malformed size for {label}: {path}") from exc
    if size > limit:
        raise HandoffError(f"{label} exceeds the {limit}-byte ceiling: {path}")
    environment = os.environ.copy()
    environment.update({"LC_ALL": "C", "LANG": "C"})
    try:
        process = subprocess.run(
            ["git", "cat-file", "blob", entry["blob"]],
            cwd=repo,
            env=environment,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=20,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise HandoffError(f"cannot read anchored {label}: {exc}") from exc
    if process.returncode != 0:
        detail = process.stderr.decode("utf-8", "replace").strip() or "unknown git failure"
        raise HandoffError(f"cannot read anchored {label}: {detail}")
    if len(process.stdout) != size:
        raise HandoffError(
            f"anchored {label} size changed while reading: expected {size}, observed {len(process.stdout)}"
        )
    return process.stdout


def control_file_records(repo: Path, commit: str) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for path in CONTROL_PATHS:
        entry = tree_entry(repo, commit, path)
        if entry is None:
            records.append({"path": path, "state": "missing"})
        else:
            records.append({"path": path, "state": "tracked", **entry})
    return records


def recent_commits(repo: Path, limit: int) -> list[dict[str, Any]]:
    if not 1 <= limit <= MAX_RECENT_COMMITS:
        raise HandoffError(f"--recent must be in [1, {MAX_RECENT_COMMITS}]")
    raw = git(
        repo,
        "log",
        "-z",
        f"-n{limit}",
        "--format=%H%x00%T%x00%cI%x00%s%x00%b",
    ).stdout
    fields = raw.split("\x00")
    if fields and fields[-1] == "":
        fields.pop()
    if len(fields) % 5:
        raise HandoffError("git log emitted a malformed NUL-delimited record set")
    records: list[dict[str, Any]] = []
    for offset in range(0, len(fields), 5):
        commit, tree, committed_at, subject, body = fields[offset : offset + 5]
        if not HEX40.fullmatch(commit) or not HEX40.fullmatch(tree):
            raise HandoffError("git log emitted a malformed commit or tree identity")
        beads: list[str] = []
        for line in body.splitlines():
            match = BEAD_TRAILER.match(line.strip())
            if match:
                beads.extend(
                    part.strip()
                    for part in re.split(r"[,\s]+", match.group(1))
                    if part.strip()
                )
        records.append(
            {
                "commit": commit,
                "tree": tree,
                "committed_at": committed_at,
                "subject": subject,
                "beads": sorted(set(beads)),
            }
        )
    return records


def evidence_frontiers(repo: Path, commit: str) -> list[dict[str, Any]]:
    result = git(repo, "ls-tree", "-r", "-l", commit, "--", "evidence/frontiers")
    records: list[dict[str, Any]] = []
    for line in result.stdout.splitlines():
        if "\t" not in line:
            raise HandoffError("git returned a malformed frontier evidence entry")
        metadata, path = line.split("\t", 1)
        fields = metadata.split()
        if len(fields) != 4:
            raise HandoffError("git returned malformed frontier evidence metadata")
        mode, kind, sha, size_text = fields
        if kind != "blob":
            continue
        if len(records) >= MAX_EVIDENCE_FILES:
            raise HandoffError(
                f"frontier evidence exceeds the {MAX_EVIDENCE_FILES}-file ceiling"
            )
        if size_text == "-":
            size = None
        else:
            try:
                size = int(size_text)
            except ValueError as exc:
                raise HandoffError(
                    f"git returned a malformed frontier evidence size for {path}"
                ) from exc
        records.append({"path": path, "mode": mode, "blob": sha, "bytes": size})
    records.sort(key=lambda record: record["path"])
    return records
