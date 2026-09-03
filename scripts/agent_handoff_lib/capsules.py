from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path
from typing import Any

from .common import (
    CAPSULE_SCHEMA,
    DECODER,
    HEX40,
    HandoffError,
    MAX_CAPSULE_COMMENT_BYTES,
    MAX_CAPSULES,
    MAX_TRACKED_BLOBS,
    git,
    require_string,
    safe_relative_path,
)
from .git_state import tree_entry


def scan_capsules(text: str) -> list[dict[str, Any]]:
    if len(text.encode("utf-8")) > MAX_CAPSULE_COMMENT_BYTES:
        raise HandoffError(
            f"one Beads comment exceeds the {MAX_CAPSULE_COMMENT_BYTES}-byte capsule scan ceiling"
        )
    capsules: list[dict[str, Any]] = []
    cursor = 0
    while cursor < len(text):
        start = text.find("{", cursor)
        if start < 0:
            break
        try:
            value, end = DECODER.raw_decode(text, start)
        except (json.JSONDecodeError, HandoffError):
            cursor = start + 1
            continue
        cursor = max(end, start + 1)
        if isinstance(value, dict) and value.get("schema") == CAPSULE_SCHEMA:
            capsules.append(value)
            if len(capsules) > MAX_CAPSULES:
                raise HandoffError(
                    f"capsule count exceeds the {MAX_CAPSULES}-capsule ceiling"
                )
    return capsules


def latest_capsule(row: dict[str, Any]) -> dict[str, Any] | None:
    comments = row.get("comments", [])
    if comments is None:
        return None
    if not isinstance(comments, list):
        raise HandoffError(f"{row.get('id', '<unknown>')}.comments must be an array")
    found: list[tuple[str, int, dict[str, Any]]] = []
    for index, comment in enumerate(comments):
        if not isinstance(comment, dict):
            raise HandoffError(
                f"{row.get('id', '<unknown>')}.comments[{index}] must be an object"
            )
        text = comment.get("text", "")
        created = comment.get("created_at", "")
        if not isinstance(text, str) or not isinstance(created, str):
            raise HandoffError(
                f"{row.get('id', '<unknown>')}.comments[{index}] has invalid text or created_at"
            )
        for capsule in scan_capsules(text):
            found.append((created, index, capsule))
    if not found:
        return None
    found.sort(key=lambda item: (item[0], item[1]))
    return found[-1][2]


def validate_capsule(
    repo: Path,
    head: str,
    issue_id: str,
    issue_status: str,
    capsule: dict[str, Any],
) -> dict[str, Any]:
    try:
        bead = require_string(capsule.get("bead"), f"{issue_id} capsule.bead")
        if bead != issue_id:
            raise HandoffError(f"{issue_id} capsule names bead {bead!r}")
        state = require_string(capsule.get("state"), f"{issue_id} capsule.state")
        if state != issue_status:
            raise HandoffError(
                f"{issue_id} capsule state {state!r} does not match issue state {issue_status!r}"
            )
        owner = require_string(capsule.get("owner"), f"{issue_id} capsule.owner")
        anchor = capsule.get("anchor")
        if not isinstance(anchor, dict):
            raise HandoffError(f"{issue_id} capsule.anchor must be an object")
        branch = require_string(anchor.get("branch"), f"{issue_id} capsule.anchor.branch")
        commit = require_string(anchor.get("commit"), f"{issue_id} capsule.anchor.commit")
        tree = require_string(anchor.get("tree"), f"{issue_id} capsule.anchor.tree")
        if not HEX40.fullmatch(commit) or not HEX40.fullmatch(tree):
            raise HandoffError(
                f"{issue_id} capsule anchor must use lowercase 40-hex identities"
            )
        tracked = anchor.get("tracked_blobs")
        if not isinstance(tracked, dict) or not tracked:
            raise HandoffError(
                f"{issue_id} capsule.anchor.tracked_blobs must be a non-empty object"
            )
        if len(tracked) > MAX_TRACKED_BLOBS:
            raise HandoffError(
                f"{issue_id} capsule tracks more than {MAX_TRACKED_BLOBS} blobs"
            )
        normalized: dict[str, str] = {}
        for raw_path, raw_sha in tracked.items():
            path = safe_relative_path(raw_path, f"{issue_id} tracked blob path")
            if not isinstance(raw_sha, str) or not HEX40.fullmatch(raw_sha):
                raise HandoffError(
                    f"{issue_id} tracked blob {path} has a malformed identity"
                )
            normalized[path] = raw_sha
        if git(repo, "cat-file", "-e", f"{commit}^{{commit}}", check=False).returncode != 0:
            raise HandoffError(f"{issue_id} capsule anchor commit is unavailable")
        actual_tree = git(repo, "rev-parse", f"{commit}^{{tree}}").stdout.strip()
        if actual_tree != tree:
            raise HandoffError(
                f"{issue_id} capsule tree {tree} does not match anchor commit tree {actual_tree}"
            )
        stale_paths: list[str] = []
        for path, declared_blob in sorted(normalized.items()):
            anchored = tree_entry(repo, commit, path)
            if anchored is None or anchored["kind"] != "blob" or anchored["blob"] != declared_blob:
                raise HandoffError(
                    f"{issue_id} capsule tracked blob {path} does not match its anchor commit"
                )
            current = tree_entry(repo, head, path)
            if current is None or current["kind"] != "blob" or current["blob"] != declared_blob:
                stale_paths.append(path)
        ancestor_result = git(
            repo, "merge-base", "--is-ancestor", commit, head, check=False
        )
        if ancestor_result.returncode not in (0, 1):
            raise HandoffError(f"cannot compare {issue_id} capsule anchor with HEAD")
        ancestor = ancestor_result.returncode == 0
        anchor_branch_matches = branch == "main"
        if commit == head and not stale_paths and anchor_branch_matches:
            freshness = "current"
        elif ancestor and not stale_paths and anchor_branch_matches:
            freshness = "reusable"
        else:
            freshness = "stale"
        return {
            "bead": issue_id,
            "owner": owner,
            "state": state,
            "anchor_branch": branch,
            "anchor_commit": commit,
            "anchor_tree": tree,
            "freshness": freshness,
            "anchor_is_ancestor": ancestor,
            "anchor_branch_matches": anchor_branch_matches,
            "tracked_blobs": normalized,
            "stale_paths": stale_paths,
        }
    except HandoffError as exc:
        return {
            "bead": issue_id,
            "freshness": "invalid",
            "reason": str(exc),
            "tracked_blobs": {},
            "stale_paths": [],
        }


def capsule_records(
    repo: Path, head: str, rows: list[dict[str, Any]]
) -> tuple[list[dict[str, Any]], list[str], list[dict[str, Any]]]:
    records: list[dict[str, Any]] = []
    missing: list[str] = []
    by_path: dict[str, list[tuple[str, str]]] = defaultdict(list)
    for row in rows:
        issue_id = row.get("id")
        status = row.get("status")
        if not isinstance(issue_id, str) or status not in {"open", "in_progress"}:
            continue
        capsule = latest_capsule(row)
        if capsule is None:
            if status == "in_progress":
                missing.append(issue_id)
            continue
        if len(records) >= MAX_CAPSULES:
            raise HandoffError(
                f"active capsule count exceeds the {MAX_CAPSULES}-capsule ceiling"
            )
        record = validate_capsule(repo, head, issue_id, status, capsule)
        records.append(record)
        if record["freshness"] in {"current", "reusable"}:
            owner = str(record.get("owner", ""))
            for path in record["tracked_blobs"]:
                by_path[path].append((issue_id, owner))
    conflicts: list[dict[str, Any]] = []
    for path, claimants in sorted(by_path.items()):
        unique = sorted(set(claimants))
        if len(unique) > 1:
            conflicts.append(
                {
                    "path": path,
                    "claimants": [
                        {"bead": bead, "owner": owner} for bead, owner in unique
                    ],
                }
            )
    records.sort(key=lambda record: (record["freshness"], record["bead"]))
    return records, sorted(missing), conflicts
