from __future__ import annotations

import hashlib
import importlib.util
import sys
from collections import Counter
from pathlib import Path
from typing import Any

from .capsules import capsule_records
from .common import (
    HEX40,
    HandoffError,
    MAX_ISSUES_BYTES,
    MAX_READY_CANDIDATES,
    bounded_read,
    environment_facts,
    git,
    issue_rows,
    load_json_bytes,
    require_string,
    safe_relative_path,
)
from .git_state import (
    blob_bytes,
    control_file_records,
    current_anchor,
    evidence_frontiers,
    recent_commits,
    tree_entry,
)


def load_frontier_module(repo: Path) -> Any:
    module_path = repo / "scripts" / "frontier_select.py"
    if not module_path.is_file() or module_path.is_symlink():
        raise HandoffError("scripts/frontier_select.py must be a regular file")
    specification = importlib.util.spec_from_file_location(
        "fln_frontier_select", module_path
    )
    if specification is None or specification.loader is None:
        raise HandoffError("cannot load scripts/frontier_select.py")
    module = importlib.util.module_from_spec(specification)
    sys.modules[specification.name] = module
    try:
        specification.loader.exec_module(module)
    except Exception as exc:
        raise HandoffError(
            f"cannot import scripts/frontier_select.py: {exc}"
        ) from exc
    required = ("load_issues", "load_overlays", "rank", "Overlay", "FrontierError")
    for name in required:
        if not hasattr(module, name):
            raise HandoffError(f"scripts/frontier_select.py lacks required API {name}")
    return module


def tracker_summary(
    repo: Path,
    issues_path: Path,
    owner: str | None,
    overlay_path: Path | None,
    strict_selection: bool,
    limit: int,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    if not 1 <= limit <= MAX_READY_CANDIDATES:
        raise HandoffError(f"--limit must be in [1, {MAX_READY_CANDIDATES}]")
    module = load_frontier_module(repo)
    try:
        issues, digest = module.load_issues(issues_path)
        overlays = module.load_overlays(overlay_path, set(issues))
        candidates, excluded = module.rank(
            issues, overlays, owner=owner, strict=strict_selection
        )
    except module.FrontierError as exc:
        raise HandoffError(f"frontier selection refused the tracker: {exc}") from exc
    rows, raw_digest = issue_rows(issues_path)
    if digest != raw_digest:
        raise HandoffError(
            "frontier selector and handoff pass disagree on the Beads store digest"
        )
    status_counts = Counter(str(row.get("status", "<missing>")) for row in rows)
    priority_counts = Counter(str(row.get("priority", "<missing>")) for row in rows)
    active = [
        {
            "id": issue.id,
            "title": issue.title,
            "status": issue.status,
            "priority": issue.priority,
            "issue_type": issue.issue_type,
            "assignee": issue.assignee,
            "blockers": list(issue.blockers),
        }
        for issue in issues.values()
        if issue.status in {"open", "in_progress"}
    ]
    active.sort(key=lambda row: (row["priority"], row["status"], row["id"]))
    return (
        {
            "path": issues_path.relative_to(repo).as_posix(),
            "sha256": digest,
            "issue_count": len(issues),
            "status_counts": dict(sorted(status_counts.items())),
            "priority_counts": dict(sorted(priority_counts.items())),
            "active_count": len(active),
            "active": active[:MAX_READY_CANDIDATES],
            "active_truncated": len(active) > MAX_READY_CANDIDATES,
            "candidate_count": len(candidates),
            "excluded": excluded,
            "selected": candidates[0] if candidates else None,
            "candidates": candidates[:limit],
            "selection_strict": strict_selection,
            "selection_authority": bool(
                candidates and candidates[0].get("promotion_authority")
            ),
        },
        rows,
    )


def build_snapshot(args: Any, repo: Path) -> dict[str, Any]:
    anchor = current_anchor(repo)
    if args.strict and anchor["branch"] != "main":
        raise HandoffError(
            f"strict snapshot requires branch 'main', observed {anchor['branch']!r}"
        )
    if args.strict and not anchor["clean"]:
        raise HandoffError("strict snapshot requires a clean working tree")
    issues_path = (repo / args.issues).resolve()
    try:
        issues_path.relative_to(repo)
    except ValueError as exc:
        raise HandoffError("--issues must stay inside the repository") from exc
    if not issues_path.is_file() or issues_path.is_symlink():
        raise HandoffError("--issues must name a regular file inside the repository")
    overlay_path = None
    if args.overlay is not None:
        overlay_path = (repo / args.overlay).resolve()
        try:
            overlay_path.relative_to(repo)
        except ValueError as exc:
            raise HandoffError("--overlay must stay inside the repository") from exc
        if not overlay_path.is_file() or overlay_path.is_symlink():
            raise HandoffError("--overlay must name a regular file inside the repository")
    tracker, rows = tracker_summary(
        repo,
        issues_path,
        args.owner,
        overlay_path,
        args.selection_strict,
        args.limit,
    )
    capsules, missing, conflicts = capsule_records(repo, anchor["commit"], rows)
    invalid = [record for record in capsules if record["freshness"] == "invalid"]
    stale = [record for record in capsules if record["freshness"] == "stale"]
    if args.require_capsules and (missing or invalid or stale or conflicts):
        pieces = []
        for name, values in (
            ("missing", missing),
            ("invalid", invalid),
            ("stale", stale),
            ("conflicts", conflicts),
        ):
            if values:
                pieces.append(f"{name}={len(values)}")
        raise HandoffError("capsule requirement failed: " + ", ".join(pieces))
    warnings: list[str] = []
    if missing:
        warnings.append(f"{len(missing)} in-progress beads have no frontier capsule")
    if invalid:
        warnings.append(f"{len(invalid)} frontier capsules are invalid")
    if stale:
        warnings.append(f"{len(stale)} frontier capsules have stale anchors")
    if conflicts:
        warnings.append(
            f"{len(conflicts)} tracked-blob ownership conflicts are visible"
        )
    if not anchor["clean"]:
        warnings.append("working tree is dirty; this snapshot is observational only")
    if anchor["branch"] != "main":
        warnings.append(
            "HEAD is not attached to main; this snapshot is observational only"
        )
    controls = control_file_records(repo, anchor["commit"])
    non_blobs = [
        record["path"]
        for record in controls
        if record["state"] == "tracked"
        and (record.get("kind") != "blob" or record.get("mode") == "120000")
    ]
    if args.strict and non_blobs:
        raise HandoffError(
            "strict snapshot requires regular control-file blobs: "
            + ", ".join(non_blobs)
        )
    document: dict[str, Any] = {
        "schema": "fln.agent-handoff/1",
        "outcome": "complete",
        "authority": {
            "kind": "repository-observation",
            "promotion_authority": bool(
                args.strict
                and anchor["clean"]
                and anchor["branch"] == "main"
                and tracker["selection_authority"]
                and not invalid
                and not stale
                and not conflicts
                and (not args.require_capsules or not missing)
            ),
        },
        "anchor": anchor,
        "control_files": controls,
        "tracker": tracker,
        "capsules": {
            "records": capsules,
            "missing_in_progress": missing,
            "conflicts": conflicts,
        },
        "frontier_evidence": evidence_frontiers(repo, anchor["commit"]),
        "recent_commits": recent_commits(repo, args.recent),
        "warnings": warnings,
    }
    if args.include_environment:
        document["environment"] = environment_facts()
        document["authority"]["environment_is_telemetry"] = True
    return document


def read_verification_input(path: str) -> bytes:
    from .common import MAX_VERIFY_BYTES

    if path == "-":
        data = sys.stdin.buffer.read(MAX_VERIFY_BYTES + 1)
        if len(data) > MAX_VERIFY_BYTES:
            raise HandoffError(
                f"verification input exceeds the {MAX_VERIFY_BYTES}-byte ceiling"
            )
        return data
    return bounded_read(Path(path), MAX_VERIFY_BYTES, "handoff capsule")


def verify_snapshot(args: Any, repo: Path) -> dict[str, Any]:
    document = load_json_bytes(
        read_verification_input(args.capsule), "handoff capsule"
    )
    if not isinstance(document, dict):
        raise HandoffError("handoff capsule root must be an object")
    if document.get("schema") != "fln.agent-handoff/1" or document.get("outcome") != "complete":
        raise HandoffError("handoff capsule has an unsupported schema or outcome")
    anchor = document.get("anchor")
    if not isinstance(anchor, dict):
        raise HandoffError("handoff capsule anchor must be an object")
    commit = require_string(anchor.get("commit"), "handoff anchor.commit")
    tree = require_string(anchor.get("tree"), "handoff anchor.tree")
    if not HEX40.fullmatch(commit) or not HEX40.fullmatch(tree):
        raise HandoffError("handoff anchor identities must be lowercase 40-hex")
    if git(repo, "cat-file", "-e", f"{commit}^{{commit}}", check=False).returncode != 0:
        raise HandoffError("handoff anchor commit is unavailable")
    if git(repo, "rev-parse", f"{commit}^{{tree}}").stdout.strip() != tree:
        raise HandoffError("handoff anchor tree does not match its commit")
    controls = document.get("control_files")
    if not isinstance(controls, list):
        raise HandoffError("handoff control_files must be an array")
    for index, record in enumerate(controls):
        if not isinstance(record, dict):
            raise HandoffError(f"control_files[{index}] must be an object")
        path = safe_relative_path(record.get("path"), f"control_files[{index}].path")
        actual = tree_entry(repo, commit, path)
        if record.get("state") == "missing":
            if actual is not None:
                raise HandoffError(f"control file {path} was recorded missing but exists")
            continue
        if record.get("state") != "tracked" or actual is None:
            raise HandoffError(f"control file {path} has inconsistent state")
        for key in ("mode", "kind", "blob"):
            if record.get(key) != actual[key]:
                raise HandoffError(f"control file {path} {key} does not match anchor")
    tracker = document.get("tracker")
    if not isinstance(tracker, dict):
        raise HandoffError("handoff tracker must be an object")
    tracker_path = safe_relative_path(tracker.get("path"), "tracker.path")
    anchored_tracker = blob_bytes(
        repo, commit, tracker_path, MAX_ISSUES_BYTES, "Beads issue store"
    )
    tracker_digest = hashlib.sha256(anchored_tracker).hexdigest()
    if tracker_digest != tracker.get("sha256"):
        raise HandoffError("anchored Beads store digest differs from the handoff capsule")
    current = current_anchor(repo)
    current_tracker_matches = False
    current_tracker_path = repo / tracker_path
    if current_tracker_path.is_file() and not current_tracker_path.is_symlink():
        current_tracker = bounded_read(
            current_tracker_path, MAX_ISSUES_BYTES, "current Beads issue store"
        )
        current_tracker_matches = hashlib.sha256(current_tracker).hexdigest() == tracker_digest
    if args.current:
        if current["commit"] != commit or current["tree"] != tree:
            raise HandoffError("handoff capsule does not describe current HEAD")
        if current["branch"] != "main":
            raise HandoffError("current verification requires branch main")
        if not current["clean"]:
            raise HandoffError("current verification requires a clean working tree")
        if not current_tracker_matches:
            raise HandoffError("current Beads store digest differs from the handoff capsule")
    return {
        "schema": "fln.agent-handoff-verification/1",
        "outcome": "verified",
        "anchor_commit": commit,
        "anchor_tree": tree,
        "current_head_required": args.current,
        "current_head_matches": current["commit"] == commit and current["tree"] == tree,
        "tracker_sha256": tracker_digest,
        "current_tracker_matches": current_tracker_matches,
        "control_file_count": len(controls),
    }
