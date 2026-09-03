from __future__ import annotations

import json
import re
from collections import defaultdict
from datetime import datetime
from pathlib import Path
from typing import Any

from .common import (
    CAPSULE_SCHEMA,
    DECODER,
    HEX40,
    HandoffError,
    MAX_ACTIVE_PATH_CLAIMS,
    MAX_ACTIVE_SEAM_CLAIMS,
    MAX_CAPSULE_COMMENT_BYTES,
    MAX_CAPSULES,
    MAX_NEGATIVE_EVIDENCE,
    MAX_SEMANTIC_SEAMS,
    MAX_TRACKED_BLOBS,
    git,
    require_string,
    require_string_list,
    safe_relative_path,
)
from .git_state import tree_entry

CAPSULE_MARKER = re.compile(r'"schema"\s*:\s*"fln\.agent-frontier/1"')


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
    latest: dict[str, Any] | None = None
    for index, comment in enumerate(comments):
        if not isinstance(comment, dict):
            raise HandoffError(
                f"{row.get('id', '<unknown>')}.comments[{index}] must be an object"
            )
        text = comment.get("text", "")
        if not isinstance(text, str):
            raise HandoffError(
                f"{row.get('id', '<unknown>')}.comments[{index}].text must be a string"
            )
        found = scan_capsules(text)
        if found:
            latest = found[-1]
        elif CAPSULE_MARKER.search(text):
            latest = {
                "schema": CAPSULE_SCHEMA,
                "__scan_error__": f"{row.get('id', '<unknown>')}.comments[{index}] contains an unreadable frontier capsule",
            }
    return latest


def require_timestamp(value: Any, label: str) -> str:
    text = require_string(value, label)
    candidate = text[:-1] + "+00:00" if text.endswith("Z") else text
    try:
        parsed = datetime.fromisoformat(candidate)
    except ValueError as exc:
        raise HandoffError(f"{label} must be an RFC3339 timestamp") from exc
    if parsed.tzinfo is None:
        raise HandoffError(f"{label} must include a timezone")
    return text


def semantic_seams(value: Any, label: str) -> list[str]:
    if value is None:
        return []
    seams = require_string_list(
        value,
        label,
        maximum=MAX_SEMANTIC_SEAMS,
        allow_empty=True,
    )
    normalized: list[str] = []
    for index, seam in enumerate(seams):
        if len(seam.encode("utf-8")) > 512:
            raise HandoffError(f"{label}[{index}] exceeds the 512-byte ceiling")
        if any(character in seam for character in ("\x00", "\n", "\r", "\t")):
            raise HandoffError(f"{label}[{index}] contains a forbidden control character")
        parts = [" ".join(part.split()) for part in seam.split("/")]
        if any(not part for part in parts):
            raise HandoffError(f"{label}[{index}] has an empty hierarchy segment")
        normalized.append(" / ".join(parts))
    if len(set(normalized)) != len(normalized):
        raise HandoffError(f"{label} contains duplicate normalized seams")
    return sorted(normalized)


def validate_frontier(issue_id: str, value: Any) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise HandoffError(f"{issue_id} capsule.frontier must be an object")
    result = {
        "artifact": require_string(value.get("artifact"), f"{issue_id} capsule.frontier.artifact"),
        "pipeline": require_string(value.get("pipeline"), f"{issue_id} capsule.frontier.pipeline"),
        "last_proven": require_string(value.get("last_proven"), f"{issue_id} capsule.frontier.last_proven"),
        "first_failure": require_string(value.get("first_failure"), f"{issue_id} capsule.frontier.first_failure"),
        "failure_class": require_string(value.get("failure_class"), f"{issue_id} capsule.frontier.failure_class"),
    }
    for key in ("actual_fingerprint", "expected_fingerprint"):
        raw = value.get(key)
        if raw is not None:
            result[key] = require_string(raw, f"{issue_id} capsule.frontier.{key}")
    return result


def validate_hypothesis(issue_id: str, value: Any) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise HandoffError(f"{issue_id} capsule.hypothesis must be an object")
    return {
        "statement": require_string(value.get("statement"), f"{issue_id} capsule.hypothesis.statement"),
        "smallest_experiment": require_string(
            value.get("smallest_experiment"),
            f"{issue_id} capsule.hypothesis.smallest_experiment",
        ),
        "protected_surfaces": require_string_list(
            value.get("protected_surfaces"),
            f"{issue_id} capsule.hypothesis.protected_surfaces",
            maximum=256,
            allow_empty=False,
        ),
    }


def validate_last_green(repo: Path, issue_id: str, anchor_commit: str, value: Any) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise HandoffError(f"{issue_id} capsule.last_green must be an object")
    commit = require_string(value.get("commit"), f"{issue_id} capsule.last_green.commit")
    if not HEX40.fullmatch(commit):
        raise HandoffError(f"{issue_id} capsule.last_green.commit must be lowercase 40-hex")
    if git(repo, "cat-file", "-e", f"{commit}^{{commit}}", check=False).returncode != 0:
        raise HandoffError(f"{issue_id} capsule.last_green.commit is unavailable")
    ancestor = git(repo, "merge-base", "--is-ancestor", commit, anchor_commit, check=False)
    if ancestor.returncode not in (0, 1):
        raise HandoffError(f"cannot compare {issue_id} last-green commit with its anchor")
    if ancestor.returncode != 0:
        raise HandoffError(f"{issue_id} capsule.last_green.commit is not an ancestor of its anchor")
    return {
        "commit": commit,
        "commands": require_string_list(
            value.get("commands"),
            f"{issue_id} capsule.last_green.commands",
            maximum=128,
            allow_empty=False,
        ),
        "receipts": require_string_list(
            value.get("receipts", []),
            f"{issue_id} capsule.last_green.receipts",
            maximum=256,
            allow_empty=True,
        ),
        "scope": require_string(value.get("scope"), f"{issue_id} capsule.last_green.scope"),
    }


def validate_negative_evidence(issue_id: str, value: Any) -> list[dict[str, str]]:
    if not isinstance(value, list):
        raise HandoffError(f"{issue_id} capsule.negative_evidence must be an array")
    if len(value) > MAX_NEGATIVE_EVIDENCE:
        raise HandoffError(
            f"{issue_id} capsule.negative_evidence exceeds the {MAX_NEGATIVE_EVIDENCE}-item ceiling"
        )
    rows: list[dict[str, str]] = []
    for index, item in enumerate(value):
        if not isinstance(item, dict):
            raise HandoffError(
                f"{issue_id} capsule.negative_evidence[{index}] must be an object"
            )
        rows.append(
            {
                key: require_string(
                    item.get(key),
                    f"{issue_id} capsule.negative_evidence[{index}].{key}",
                )
                for key in (
                    "attempt",
                    "hypothesis",
                    "outcome",
                    "reason",
                    "differentiator_required",
                )
            }
        )
    return rows


def validate_next(issue_id: str, value: Any) -> dict[str, str]:
    if not isinstance(value, dict):
        raise HandoffError(f"{issue_id} capsule.next must be an object")
    return {
        key: require_string(value.get(key), f"{issue_id} capsule.next.{key}")
        for key in ("command", "success", "failure_capture")
    }


def validate_closure(issue_id: str, value: Any) -> dict[str, list[str]]:
    if not isinstance(value, dict):
        raise HandoffError(f"{issue_id} capsule.closure must be an object")
    return {
        "criteria": require_string_list(
            value.get("criteria"),
            f"{issue_id} capsule.closure.criteria",
            maximum=256,
            allow_empty=False,
        ),
        "still_missing": require_string_list(
            value.get("still_missing"),
            f"{issue_id} capsule.closure.still_missing",
            maximum=256,
            allow_empty=True,
        ),
    }


def validate_capsule(
    repo: Path,
    head: str,
    issue_id: str,
    issue_status: str,
    capsule: dict[str, Any],
) -> dict[str, Any]:
    try:
        if "__scan_error__" in capsule:
            raise HandoffError(require_string(capsule["__scan_error__"], f"{issue_id} capsule scan error"))
        if capsule.get("schema") != CAPSULE_SCHEMA:
            raise HandoffError(f"{issue_id} capsule has an unsupported schema")
        bead = require_string(capsule.get("bead"), f"{issue_id} capsule.bead")
        if bead != issue_id:
            raise HandoffError(f"{issue_id} capsule names bead {bead!r}")
        state = require_string(capsule.get("state"), f"{issue_id} capsule.state")
        if state != issue_status:
            raise HandoffError(
                f"{issue_id} capsule state {state!r} does not match issue state {issue_status!r}"
            )
        owner = require_string(capsule.get("owner"), f"{issue_id} capsule.owner")
        lease_observed_at = require_timestamp(
            capsule.get("lease_observed_at"),
            f"{issue_id} capsule.lease_observed_at",
        )
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
        frontier = validate_frontier(issue_id, capsule.get("frontier"))
        hypothesis = validate_hypothesis(issue_id, capsule.get("hypothesis"))
        last_green = validate_last_green(
            repo,
            issue_id,
            commit,
            capsule.get("last_green"),
        )
        negative_evidence = validate_negative_evidence(
            issue_id, capsule.get("negative_evidence")
        )
        next_step = validate_next(issue_id, capsule.get("next"))
        closure = validate_closure(issue_id, capsule.get("closure"))
        seams = semantic_seams(
            capsule.get("semantic_seams"),
            f"{issue_id} capsule.semantic_seams",
        )
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
            "lease_observed_at": lease_observed_at,
            "anchor_branch": branch,
            "anchor_commit": commit,
            "anchor_tree": tree,
            "freshness": freshness,
            "anchor_is_ancestor": ancestor,
            "anchor_branch_matches": anchor_branch_matches,
            "tracked_blobs": normalized,
            "semantic_seams": seams,
            "stale_paths": stale_paths,
            "frontier": frontier,
            "hypothesis": hypothesis,
            "last_green": last_green,
            "negative_evidence": negative_evidence,
            "next": next_step,
            "closure": closure,
        }
    except HandoffError as exc:
        return {
            "bead": issue_id,
            "freshness": "invalid",
            "reason": str(exc),
            "tracked_blobs": {},
            "semantic_seams": [],
            "stale_paths": [],
        }


def capsule_records(
    repo: Path, head: str, rows: list[dict[str, Any]]
) -> tuple[
    list[dict[str, Any]],
    list[str],
    list[dict[str, Any]],
    list[dict[str, Any]],
]:
    records: list[dict[str, Any]] = []
    missing: list[str] = []
    by_path: dict[str, list[tuple[str, str]]] = defaultdict(list)
    by_seam: dict[tuple[str, ...], list[tuple[str, str]]] = defaultdict(list)
    path_claim_count = 0
    seam_claim_count = 0
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
                path_claim_count += 1
                if path_claim_count > MAX_ACTIVE_PATH_CLAIMS:
                    raise HandoffError(
                        f"active tracked-blob claims exceed the {MAX_ACTIVE_PATH_CLAIMS}-claim ceiling"
                    )
                by_path[path].append((issue_id, owner))
            for seam in record["semantic_seams"]:
                seam_claim_count += 1
                if seam_claim_count > MAX_ACTIVE_SEAM_CLAIMS:
                    raise HandoffError(
                        f"active semantic-seam claims exceed the {MAX_ACTIVE_SEAM_CLAIMS}-claim ceiling"
                    )
                by_seam[tuple(seam.split(" / "))].append((issue_id, owner))

    def exact_conflicts(
        source: dict[str, list[tuple[str, str]]], key: str
    ) -> list[dict[str, Any]]:
        result: list[dict[str, Any]] = []
        for identity, claimants in sorted(source.items()):
            unique = sorted(set(claimants))
            if len(unique) > 1:
                result.append(
                    {
                        key: identity,
                        "claimants": [
                            {"bead": bead, "owner": owner} for bead, owner in unique
                        ],
                    }
                )
        return result

    seam_conflicts: dict[tuple[str, ...], set[tuple[str, str]]] = defaultdict(set)
    for seam, claimants in by_seam.items():
        unique = set(claimants)
        if len(unique) > 1:
            seam_conflicts[seam].update(unique)
        for width in range(1, len(seam)):
            prefix = seam[:width]
            prefix_claimants = set(by_seam.get(prefix, ()))
            if prefix_claimants and prefix_claimants != unique:
                combined = prefix_claimants | unique
                if len(combined) > 1:
                    seam_conflicts[prefix].update(combined)
    rendered_seam_conflicts = [
        {
            "seam": " / ".join(seam),
            "claimants": [
                {"bead": bead, "owner": owner}
                for bead, owner in sorted(claimants)
            ],
        }
        for seam, claimants in sorted(seam_conflicts.items())
    ]

    records.sort(key=lambda record: (record["freshness"], record["bead"]))
    return (
        records,
        sorted(missing),
        exact_conflicts(by_path, "path"),
        rendered_seam_conflicts,
    )
