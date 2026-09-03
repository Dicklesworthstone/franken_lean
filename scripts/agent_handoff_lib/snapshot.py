from __future__ import annotations

import hashlib
import importlib.util
import sys
import tempfile
from collections import Counter
from pathlib import Path
from typing import Any

from .capsules import capsule_records
from .common import (
    CONTROL_PATHS,
    HEX40,
    HandoffError,
    MAX_ISSUES_BYTES,
    MAX_OVERLAY_BYTES,
    MAX_READY_CANDIDATES,
    MAX_RECENT_COMMITS,
    MAX_SELECTOR_BYTES,
    bounded_read,
    canonical_json,
    environment_facts,
    git,
    issue_rows,
    load_json_bytes,
    require_bool,
    require_int,
    require_optional_string,
    require_string,
    safe_relative_path,
    sha256_hex,
)
from .git_state import (
    blob_bytes,
    control_file_records,
    current_anchor,
    evidence_frontiers,
    recent_commits,
    worktree_blob_bytes,
)

REQUEST_KEYS = {
    "issues",
    "overlay",
    "owner",
    "limit",
    "recent",
    "strict",
    "selection_strict",
    "require_capsules",
    "include_environment",
}
ANCHOR_KEYS = {"branch", "commit", "tree", "clean"}


def load_frontier_module(module_path: Path, identity: str) -> Any:
    if not module_path.is_file() or module_path.is_symlink():
        raise HandoffError("frontier selector must be a regular file")
    specification = importlib.util.spec_from_file_location(
        f"fln_frontier_select_{identity}", module_path
    )
    if specification is None or specification.loader is None:
        raise HandoffError("cannot load frontier selector")
    module = importlib.util.module_from_spec(specification)
    sys.modules[specification.name] = module
    try:
        specification.loader.exec_module(module)
    except Exception as exc:
        raise HandoffError(f"cannot import frontier selector: {exc}") from exc
    required = ("load_issues", "load_overlays", "rank", "Overlay", "FrontierError")
    for name in required:
        if not hasattr(module, name):
            raise HandoffError(f"frontier selector lacks required API {name}")
    return module


def tracker_summary(
    module_path: Path,
    module_identity: str,
    issues_path: Path,
    issues_display_path: str,
    owner: str | None,
    overlay_path: Path | None,
    strict_selection: bool,
    limit: int,
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    if not 1 <= limit <= MAX_READY_CANDIDATES:
        raise HandoffError(f"snapshot limit must be in [1, {MAX_READY_CANDIDATES}]")
    module = load_frontier_module(module_path, module_identity)
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
            "path": issues_display_path,
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


def normalized_repo_path(repo: Path, value: Path, label: str) -> tuple[str, Path]:
    if value.is_absolute():
        try:
            relative = value.resolve().relative_to(repo)
        except (OSError, ValueError) as exc:
            raise HandoffError(f"{label} must stay inside the repository") from exc
        path = safe_relative_path(relative.as_posix(), label)
    else:
        path = safe_relative_path(value.as_posix(), label)
    candidate = repo / path
    cursor = repo
    for part in Path(path).parts:
        cursor = cursor / part
        if cursor.is_symlink():
            raise HandoffError(f"{label} must not traverse a symbolic link: {path}")
    if not candidate.is_file():
        raise HandoffError(f"{label} must name a regular file inside the repository")
    return path, candidate


def request_from_args(args: Any, repo: Path) -> tuple[dict[str, Any], Path, Path | None]:
    issues, issues_path = normalized_repo_path(repo, args.issues, "--issues")
    overlay: str | None = None
    overlay_path: Path | None = None
    if args.overlay is not None:
        overlay, overlay_path = normalized_repo_path(repo, args.overlay, "--overlay")
    owner = None if args.owner is None else require_string(args.owner, "--owner")
    request = {
        "issues": issues,
        "overlay": overlay,
        "owner": owner,
        "limit": require_int(args.limit, "--limit", 1, MAX_READY_CANDIDATES),
        "recent": require_int(args.recent, "--recent", 1, MAX_RECENT_COMMITS),
        "strict": bool(args.strict),
        "selection_strict": bool(args.selection_strict),
        "require_capsules": bool(args.require_capsules),
        "include_environment": bool(args.include_environment),
    }
    return request, issues_path, overlay_path


def validate_request(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != REQUEST_KEYS:
        raise HandoffError("handoff request has an invalid key set")
    return {
        "issues": safe_relative_path(value.get("issues"), "request.issues"),
        "overlay": (
            None
            if value.get("overlay") is None
            else safe_relative_path(value.get("overlay"), "request.overlay")
        ),
        "owner": require_optional_string(value.get("owner"), "request.owner"),
        "limit": require_int(
            value.get("limit"), "request.limit", 1, MAX_READY_CANDIDATES
        ),
        "recent": require_int(
            value.get("recent"), "request.recent", 1, MAX_RECENT_COMMITS
        ),
        "strict": require_bool(value.get("strict"), "request.strict"),
        "selection_strict": require_bool(
            value.get("selection_strict"), "request.selection_strict"
        ),
        "require_capsules": require_bool(
            value.get("require_capsules"), "request.require_capsules"
        ),
        "include_environment": require_bool(
            value.get("include_environment"), "request.include_environment"
        ),
    }


def validate_anchor(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != ANCHOR_KEYS:
        raise HandoffError("handoff anchor has an invalid key set")
    branch = value.get("branch")
    if branch is not None:
        branch = require_string(branch, "handoff anchor.branch")
    commit = require_string(value.get("commit"), "handoff anchor.commit")
    tree = require_string(value.get("tree"), "handoff anchor.tree")
    if not HEX40.fullmatch(commit) or not HEX40.fullmatch(tree):
        raise HandoffError("handoff anchor identities must be lowercase 40-hex")
    return {
        "branch": branch,
        "commit": commit,
        "tree": tree,
        "clean": require_bool(value.get("clean"), "handoff anchor.clean"),
    }


def control_defects(records: list[dict[str, Any]]) -> tuple[list[str], list[str]]:
    missing = [record["path"] for record in records if record["state"] == "missing"]
    non_blobs = [
        record["path"]
        for record in records
        if record["state"] == "tracked"
        and (record.get("kind") != "blob" or record.get("mode") == "120000")
    ]
    return missing, non_blobs


def build_document(
    repo: Path,
    anchor: dict[str, Any],
    request: dict[str, Any],
    selector_path: Path,
    selector_identity: str,
    issues_path: Path,
    overlay_path: Path | None,
    *,
    include_environment: bool,
) -> dict[str, Any]:
    tracker, rows = tracker_summary(
        selector_path,
        selector_identity,
        issues_path,
        request["issues"],
        request["owner"],
        overlay_path,
        request["selection_strict"],
        request["limit"],
    )
    capsules, missing, path_conflicts, seam_conflicts = capsule_records(
        repo, anchor["commit"], rows
    )
    invalid = [record for record in capsules if record["freshness"] == "invalid"]
    stale = [record for record in capsules if record["freshness"] == "stale"]
    if request["require_capsules"] and (
        missing or invalid or stale or path_conflicts or seam_conflicts
    ):
        pieces = []
        for name, values in (
            ("missing", missing),
            ("invalid", invalid),
            ("stale", stale),
            ("path_conflicts", path_conflicts),
            ("seam_conflicts", seam_conflicts),
        ):
            if values:
                pieces.append(f"{name}={len(values)}")
        raise HandoffError("capsule requirement failed: " + ", ".join(pieces))

    controls = control_file_records(repo, anchor["commit"])
    missing_controls, non_blob_controls = control_defects(controls)
    if request["strict"] and missing_controls:
        raise HandoffError(
            "strict snapshot requires every control path: " + ", ".join(missing_controls)
        )
    if request["strict"] and non_blob_controls:
        raise HandoffError(
            "strict snapshot requires regular control-file blobs: "
            + ", ".join(non_blob_controls)
        )

    warnings: list[str] = []
    if missing:
        warnings.append(f"{len(missing)} in-progress beads have no frontier capsule")
    if invalid:
        warnings.append(f"{len(invalid)} frontier capsules are invalid")
    if stale:
        warnings.append(f"{len(stale)} frontier capsules have stale anchors")
    if path_conflicts:
        warnings.append(
            f"{len(path_conflicts)} tracked-blob ownership conflicts are visible"
        )
    if seam_conflicts:
        warnings.append(
            f"{len(seam_conflicts)} semantic-seam ownership conflicts are visible"
        )
    if missing_controls:
        warnings.append(f"{len(missing_controls)} control paths are missing")
    if non_blob_controls:
        warnings.append(f"{len(non_blob_controls)} control paths are not regular blobs")
    if not anchor["clean"]:
        warnings.append("working tree is dirty; this snapshot is observational only")
    if anchor["branch"] != "main":
        warnings.append(
            "HEAD is not attached to main; this snapshot is observational only"
        )

    canonical_inputs = (
        request["issues"] == ".beads/issues.jsonl" and request["overlay"] is None
    )
    if not canonical_inputs:
        warnings.append(
            "custom tracker or overlay input is observational and cannot carry promotion authority"
        )

    promotion_authority = bool(
        canonical_inputs
        and request["strict"]
        and anchor["clean"]
        and anchor["branch"] == "main"
        and tracker["selection_authority"]
        and not invalid
        and not stale
        and not path_conflicts
        and not seam_conflicts
        and not missing_controls
        and not non_blob_controls
        and (not request["require_capsules"] or not missing)
    )
    document: dict[str, Any] = {
        "schema": "fln.agent-handoff/2",
        "outcome": "complete",
        "request": request,
        "authority": {
            "kind": "repository-observation",
            "promotion_authority": promotion_authority,
        },
        "anchor": anchor,
        "control_files": controls,
        "tracker": tracker,
        "capsules": {
            "records": capsules,
            "missing_in_progress": missing,
            "path_conflicts": path_conflicts,
            "semantic_conflicts": seam_conflicts,
        },
        "frontier_evidence": evidence_frontiers(repo, anchor["commit"]),
        "recent_commits": recent_commits(
            repo, anchor["commit"], request["recent"]
        ),
        "warnings": warnings,
    }
    if request["include_environment"]:
        document["authority"]["environment_is_telemetry"] = True
    immutable = canonical_json(document)
    document["integrity"] = {
        "schema": "fln.agent-handoff-projection/1",
        "sha256": sha256_hex(immutable),
    }
    if include_environment:
        document["environment"] = environment_facts()
    return document


def build_snapshot(args: Any, repo: Path) -> dict[str, Any]:
    anchor = current_anchor(repo)
    if args.strict and anchor["branch"] != "main":
        raise HandoffError(
            f"strict snapshot requires branch 'main', observed {anchor['branch']!r}"
        )
    if args.strict and not anchor["clean"]:
        raise HandoffError("strict snapshot requires a clean working tree")
    request, issues_path, overlay_path = request_from_args(args, repo)
    selector_bytes = worktree_blob_bytes(
        repo,
        anchor["commit"],
        "scripts/frontier_select.py",
        MAX_SELECTOR_BYTES,
        "frontier selector",
    )
    issues_bytes = worktree_blob_bytes(
        repo,
        anchor["commit"],
        request["issues"],
        MAX_ISSUES_BYTES,
        "Beads issue store",
    )
    if bounded_read(issues_path, MAX_ISSUES_BYTES, "Beads issue store") != issues_bytes:
        raise HandoffError("Beads issue store changed during snapshot construction")
    if overlay_path is not None:
        overlay_bytes = worktree_blob_bytes(
            repo,
            anchor["commit"],
            request["overlay"],
            MAX_OVERLAY_BYTES,
            "frontier overlay",
        )
        if bounded_read(overlay_path, MAX_OVERLAY_BYTES, "frontier overlay") != overlay_bytes:
            raise HandoffError("frontier overlay changed during snapshot construction")
    return build_document(
        repo,
        anchor,
        request,
        repo / "scripts/frontier_select.py",
        sha256_hex(selector_bytes),
        issues_path,
        overlay_path,
        include_environment=request["include_environment"],
    )


def read_verification_input(path: str) -> bytes:
    from .common import MAX_VERIFY_BYTES

    if path == "-":
        data = sys.stdin.buffer.read(MAX_VERIFY_BYTES + 1)
        if len(data) > MAX_VERIFY_BYTES:
            raise HandoffError(
                f"verification input exceeds the {MAX_VERIFY_BYTES}-byte ceiling"
            )
        return data
    return bounded_read(Path(path), MAX_VERIFY_BYTES, "handoff snapshot")


def materialize_anchored_inputs(
    repo: Path,
    commit: str,
    request: dict[str, Any],
    root: Path,
) -> tuple[Path, Path | None]:
    issues_bytes = blob_bytes(
        repo,
        commit,
        request["issues"],
        MAX_ISSUES_BYTES,
        "Beads issue store",
    )
    issues = root / "issues.jsonl"
    issues.write_bytes(issues_bytes)
    overlay: Path | None = None
    if request["overlay"] is not None:
        overlay_bytes = blob_bytes(
            repo,
            commit,
            request["overlay"],
            MAX_OVERLAY_BYTES,
            "frontier overlay",
        )
        overlay = root / "overlay.json"
        overlay.write_bytes(overlay_bytes)
    return issues, overlay


def verifier_selector() -> tuple[Path, str]:
    path = Path(__file__).resolve().parents[1] / "frontier_select.py"
    if not path.is_file() or path.is_symlink():
        raise HandoffError("verifier frontier selector must be a regular file")
    data = bounded_read(path, MAX_SELECTOR_BYTES, "verifier frontier selector")
    return path, sha256_hex(data)


def compare_reconstruction(document: dict[str, Any], expected: dict[str, Any]) -> None:
    actual_keys = set(document)
    expected_keys = set(expected)
    if actual_keys != expected_keys:
        missing = sorted(expected_keys - actual_keys)
        extra = sorted(actual_keys - expected_keys)
        raise HandoffError(
            f"handoff top-level keys differ from anchored reconstruction: missing={missing}, extra={extra}"
        )
    for key in sorted(expected):
        if document[key] != expected[key]:
            raise HandoffError(
                f"handoff section {key!r} does not match anchored reconstruction"
            )


def verify_snapshot(args: Any, repo: Path) -> dict[str, Any]:
    document = load_json_bytes(
        read_verification_input(args.capsule), "handoff snapshot"
    )
    if not isinstance(document, dict):
        raise HandoffError("handoff snapshot root must be an object")
    if document.get("schema") != "fln.agent-handoff/2" or document.get("outcome") != "complete":
        raise HandoffError("handoff snapshot has an unsupported schema or outcome")
    request = validate_request(document.get("request"))
    anchor = validate_anchor(document.get("anchor"))
    commit = anchor["commit"]
    tree = anchor["tree"]
    if git(repo, "cat-file", "-e", f"{commit}^{{commit}}", check=False).returncode != 0:
        raise HandoffError("handoff anchor commit is unavailable")
    if git(repo, "rev-parse", f"{commit}^{{tree}}").stdout.strip() != tree:
        raise HandoffError("handoff anchor tree does not match its commit")

    environment = document.pop("environment", None)
    if request["include_environment"]:
        if not isinstance(environment, dict):
            raise HandoffError("handoff environment telemetry is missing or malformed")
    elif environment is not None:
        raise HandoffError("handoff carries environment telemetry that was not requested")

    current = current_anchor(repo)
    if args.current:
        if current["commit"] != commit or current["tree"] != tree:
            raise HandoffError("handoff snapshot does not describe current HEAD")
        if current["branch"] != "main":
            raise HandoffError("current verification requires branch main")
        if not current["clean"]:
            raise HandoffError("current verification requires a clean working tree")

    selector, identity = verifier_selector()
    with tempfile.TemporaryDirectory(prefix="fln-handoff-verify-") as directory:
        issues, overlay = materialize_anchored_inputs(
            repo, commit, request, Path(directory)
        )
        expected = build_document(
            repo,
            anchor,
            request,
            selector,
            identity,
            issues,
            overlay,
            include_environment=False,
        )
    compare_reconstruction(document, expected)

    current_tracker_matches = False
    current_tracker_path = repo / request["issues"]
    if current_tracker_path.is_file() and not current_tracker_path.is_symlink():
        current_tracker = bounded_read(
            current_tracker_path, MAX_ISSUES_BYTES, "current Beads issue store"
        )
        current_tracker_matches = hashlib.sha256(current_tracker).hexdigest() == document[
            "tracker"
        ]["sha256"]
    if args.current and not current_tracker_matches:
        raise HandoffError("current Beads store digest differs from the handoff snapshot")

    main_result = git(repo, "merge-base", "--is-ancestor", commit, "refs/heads/main", check=False)
    anchor_on_current_main = main_result.returncode == 0
    if main_result.returncode not in (0, 1, 128):
        raise HandoffError("cannot compare handoff anchor with refs/heads/main")
    return {
        "schema": "fln.agent-handoff-verification/2",
        "outcome": "verified",
        "verification_scope": "anchored-reconstruction",
        "verified_sections": [
            "authority",
            "capsules",
            "control_files",
            "frontier_evidence",
            "integrity",
            "recent_commits",
            "request",
            "tracker",
            "warnings",
        ],
        "environment_telemetry_verified": False,
        "anchor_commit": commit,
        "anchor_tree": tree,
        "anchor_on_current_main": anchor_on_current_main,
        "current_head_required": args.current,
        "current_head_matches": current["commit"] == commit and current["tree"] == tree,
        "tracker_sha256": document["tracker"]["sha256"],
        "current_tracker_matches": current_tracker_matches,
        "control_file_count": len(document["control_files"]),
    }
