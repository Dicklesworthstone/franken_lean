#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

SCHEMA = "fln.frontier-selection/1"
ACTIVE = {"open", "in_progress"}
TERMINAL = {"closed"}
BLOCKING_DEPENDENCY = "blocks"


class FrontierError(Exception):
    pass


@dataclass(frozen=True)
class Issue:
    id: str
    title: str
    status: str
    priority: int
    issue_type: str
    assignee: str | None
    acceptance_criteria: str
    description: str
    labels: tuple[str, ...]
    blockers: tuple[str, ...]


@dataclass(frozen=True)
class Overlay:
    context_reuse: int = 0
    seam_isolation: int = 0
    evidence_cost: int = 0
    collision_risk: int = 0
    trusted_surface_breadth: int = 0
    irreducible_uncertainty: int = 0
    first_failure_named: bool | None = None
    artifacts_available: bool | None = None
    toolchain_available: bool | None = None
    oracle_only_compliant: bool | None = None


def die(message: str, code: int = 2) -> None:
    print(
        json.dumps(
            {"schema": SCHEMA, "outcome": "refused", "reason": message},
            sort_keys=True,
        ),
        file=sys.stderr,
    )
    raise SystemExit(code)


def expect_dict(value: Any, where: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise FrontierError(f"{where} must be an object")
    return value


def expect_string(value: Any, where: str, *, allow_empty: bool = False) -> str:
    if not isinstance(value, str) or (not allow_empty and not value.strip()):
        qualifier = "possibly empty " if allow_empty else ""
        raise FrontierError(f"{where} must be a {qualifier}string")
    return value


def expect_int(
    value: Any,
    where: str,
    *,
    minimum: int = 0,
    maximum: int = 100,
) -> int:
    if (
        isinstance(value, bool)
        or not isinstance(value, int)
        or not minimum <= value <= maximum
    ):
        raise FrontierError(f"{where} must be an integer in [{minimum}, {maximum}]")
    return value


def expect_optional_bool(value: Any, where: str) -> bool | None:
    if value is None:
        return None
    if not isinstance(value, bool):
        raise FrontierError(f"{where} must be boolean or null")
    return value


def reject_duplicate_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise FrontierError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def load_issues(path: Path) -> tuple[dict[str, Issue], str]:
    try:
        raw = path.read_bytes()
    except OSError as exc:
        raise FrontierError(f"cannot read issues file {path}: {exc}") from exc
    digest = hashlib.sha256(raw).hexdigest()
    issues: dict[str, Issue] = {}
    for line_number, raw_line in enumerate(raw.splitlines(), 1):
        if not raw_line.strip():
            continue
        try:
            row = expect_dict(
                json.loads(raw_line, object_pairs_hook=reject_duplicate_pairs),
                f"line {line_number}",
            )
        except (UnicodeDecodeError, json.JSONDecodeError, FrontierError) as exc:
            raise FrontierError(f"invalid issue row at line {line_number}: {exc}") from exc
        issue_id = expect_string(row.get("id"), f"line {line_number}.id")
        if issue_id in issues:
            raise FrontierError(f"duplicate issue id {issue_id!r} at line {line_number}")
        status = expect_string(row.get("status"), f"{issue_id}.status")
        if status not in ACTIVE | TERMINAL:
            raise FrontierError(f"{issue_id}.status has unsupported value {status!r}")
        priority = expect_int(row.get("priority"), f"{issue_id}.priority", maximum=4)
        dependencies = row.get("dependencies", [])
        if not isinstance(dependencies, list):
            raise FrontierError(f"{issue_id}.dependencies must be an array")
        blockers: list[str] = []
        for index, dependency_value in enumerate(dependencies):
            dependency = expect_dict(
                dependency_value,
                f"{issue_id}.dependencies[{index}]",
            )
            dependency_type = expect_string(
                dependency.get("type"),
                f"{issue_id}.dependencies[{index}].type",
            )
            if dependency_type != BLOCKING_DEPENDENCY:
                continue
            source = expect_string(
                dependency.get("issue_id"),
                f"{issue_id}.dependencies[{index}].issue_id",
            )
            if source != issue_id:
                raise FrontierError(
                    f"{issue_id}.dependencies[{index}] names source {source!r}; "
                    f"expected {issue_id!r}"
                )
            blockers.append(
                expect_string(
                    dependency.get("depends_on_id"),
                    f"{issue_id}.dependencies[{index}].depends_on_id",
                )
            )
        labels_value = row.get("labels", [])
        if not isinstance(labels_value, list) or not all(
            isinstance(label, str) and label for label in labels_value
        ):
            raise FrontierError(
                f"{issue_id}.labels must be an array of non-empty strings"
            )
        assignee_value = row.get("assignee")
        assignee = (
            None
            if assignee_value in (None, "")
            else expect_string(assignee_value, f"{issue_id}.assignee")
        )
        issues[issue_id] = Issue(
            id=issue_id,
            title=expect_string(row.get("title"), f"{issue_id}.title"),
            status=status,
            priority=priority,
            issue_type=expect_string(
                row.get("issue_type"),
                f"{issue_id}.issue_type",
            ),
            assignee=assignee,
            acceptance_criteria=expect_string(
                row.get("acceptance_criteria", ""),
                f"{issue_id}.acceptance_criteria",
                allow_empty=True,
            ),
            description=expect_string(
                row.get("description", ""),
                f"{issue_id}.description",
                allow_empty=True,
            ),
            labels=tuple(sorted(set(labels_value))),
            blockers=tuple(sorted(set(blockers))),
        )
    if not issues:
        raise FrontierError("issues file contains no issue rows")
    for issue in issues.values():
        for blocker in issue.blockers:
            if blocker not in issues:
                raise FrontierError(f"{issue.id} has dangling blocker {blocker!r}")
    validate_block_graph_acyclic(issues)
    return issues, digest


def validate_block_graph_acyclic(issues: dict[str, Issue]) -> None:
    reverse = reverse_block_graph(issues)
    indegree = {issue.id: len(issue.blockers) for issue in issues.values()}
    ready = deque(
        sorted(issue_id for issue_id, degree in indegree.items() if degree == 0)
    )
    visited = 0
    while ready:
        issue_id = ready.popleft()
        visited += 1
        for child in reverse.get(issue_id, ()):
            indegree[child] -= 1
            if indegree[child] == 0:
                ready.append(child)
    if visited == len(issues):
        return

    remaining = {issue_id for issue_id, degree in indegree.items() if degree > 0}
    start = min(remaining)
    path: list[str] = []
    positions: dict[str, int] = {}
    current = start
    while current not in positions:
        positions[current] = len(path)
        path.append(current)
        candidates = sorted(set(issues[current].blockers) & remaining)
        if not candidates:
            raise FrontierError(
                "blocking graph is cyclic but no cycle witness was recoverable "
                f"from {start!r}"
            )
        current = candidates[0]
    cycle = path[positions[current] :] + [current]
    raise FrontierError(f"blocking dependency cycle: {' -> '.join(cycle)}")


def load_overlays(path: Path | None, issue_ids: set[str]) -> dict[str, Overlay]:
    overlays, _ = load_overlay_snapshot(path, issue_ids)
    return overlays


def load_overlay_snapshot(
    path: Path | None, issue_ids: set[str]
) -> tuple[dict[str, Overlay], str | None]:
    if path is None:
        return {}, None
    try:
        raw = path.read_bytes()
        root = expect_dict(
            json.loads(
                raw.decode("utf-8"),
                object_pairs_hook=reject_duplicate_pairs,
            ),
            "overlay root",
        )
    except (OSError, UnicodeDecodeError, json.JSONDecodeError, FrontierError) as exc:
        raise FrontierError(f"cannot load overlay {path}: {exc}") from exc
    unknown = sorted(set(root) - issue_ids)
    if unknown:
        raise FrontierError(f"overlay names unknown issues: {', '.join(unknown)}")
    overlays: dict[str, Overlay] = {}
    numeric = (
        "context_reuse",
        "seam_isolation",
        "evidence_cost",
        "collision_risk",
        "trusted_surface_breadth",
        "irreducible_uncertainty",
    )
    boolean = (
        "first_failure_named",
        "artifacts_available",
        "toolchain_available",
        "oracle_only_compliant",
    )
    for issue_id, value in root.items():
        row = expect_dict(value, f"overlay.{issue_id}")
        allowed = set(numeric) | set(boolean)
        extra = sorted(set(row) - allowed)
        if extra:
            raise FrontierError(
                f"overlay.{issue_id} has unknown fields: {', '.join(extra)}"
            )
        values = {
            field: expect_int(
                row.get(field, 0),
                f"overlay.{issue_id}.{field}",
                maximum=10,
            )
            for field in numeric
        }
        values.update(
            {
                field: expect_optional_bool(
                    row.get(field),
                    f"overlay.{issue_id}.{field}",
                )
                for field in boolean
            }
        )
        overlays[issue_id] = Overlay(**values)
    return overlays, hashlib.sha256(raw).hexdigest()


def unresolved(issue: Issue, issues: dict[str, Issue]) -> tuple[str, ...]:
    return tuple(
        blocker for blocker in issue.blockers if issues[blocker].status != "closed"
    )


def reverse_block_graph(issues: dict[str, Issue]) -> dict[str, tuple[str, ...]]:
    reverse: dict[str, list[str]] = defaultdict(list)
    for issue in issues.values():
        for blocker in issue.blockers:
            reverse[blocker].append(issue.id)
    return {
        issue_id: tuple(sorted(children))
        for issue_id, children in reverse.items()
    }


def descendant_count(
    issue_id: str,
    reverse: dict[str, tuple[str, ...]],
    issues: dict[str, Issue],
) -> int:
    seen: set[str] = set()
    pending = deque(reverse.get(issue_id, ()))
    while pending:
        child = pending.popleft()
        if child in seen or issues[child].status == "closed":
            continue
        seen.add(child)
        pending.extend(reverse.get(child, ()))
    return len(seen)


def score(
    issue: Issue,
    descendants: int,
    direct_unlocks: int,
    overlay: Overlay,
) -> tuple[int, dict[str, int]]:
    components = {
        "priority": (4 - issue.priority) * 1000,
        "critical_path_descendants": descendants * 100,
        "direct_unlocks": direct_unlocks * 40,
        "context_reuse": overlay.context_reuse * 20,
        "seam_isolation": overlay.seam_isolation * 20,
        "evidence_cost": -overlay.evidence_cost * 25,
        "collision_risk": -overlay.collision_risk * 40,
        "trusted_surface_breadth": -overlay.trusted_surface_breadth * 30,
        "irreducible_uncertainty": -overlay.irreducible_uncertainty * 35,
    }
    return sum(components.values()), components


def rank(
    issues: dict[str, Issue],
    overlays: dict[str, Overlay],
    *,
    owner: str | None,
    strict: bool,
) -> tuple[list[dict[str, Any]], dict[str, int]]:
    if owner is not None:
        expect_string(owner, "owner")
    reverse = reverse_block_graph(issues)
    excluded: dict[str, int] = defaultdict(int)
    candidates: list[dict[str, Any]] = []
    for issue in issues.values():
        if issue.status == "closed":
            excluded["closed"] += 1
            continue
        blockers = unresolved(issue, issues)
        if blockers:
            excluded["blocked_dependencies"] += 1
            continue
        if issue.assignee and issue.assignee != owner:
            excluded["owned_by_other"] += 1
            continue
        if issue.status == "in_progress" and issue.assignee is None:
            excluded["unowned_in_progress"] += 1
            continue
        if not issue.acceptance_criteria.strip():
            excluded["missing_acceptance_criteria"] += 1
            continue
        overlay = overlays.get(issue.id, Overlay())
        hard_facts = {
            "first_failure_named": overlay.first_failure_named,
            "artifacts_available": overlay.artifacts_available,
            "toolchain_available": overlay.toolchain_available,
            "oracle_only_compliant": overlay.oracle_only_compliant,
        }
        false_facts = sorted(
            name for name, value in hard_facts.items() if value is False
        )
        if false_facts:
            excluded["declared_hard_filter_failure"] += 1
            continue
        unknown_facts = sorted(
            name for name, value in hard_facts.items() if value is None
        )
        if strict and unknown_facts:
            excluded["unknown_hard_filter_facts"] += 1
            continue
        descendants = descendant_count(issue.id, reverse, issues)
        direct_unlocks = sum(
            issues[child].status != "closed"
            and unresolved(issues[child], issues) == (issue.id,)
            for child in reverse.get(issue.id, ())
        )
        total, components = score(issue, descendants, direct_unlocks, overlay)
        candidates.append(
            {
                "id": issue.id,
                "title": issue.title,
                "status": issue.status,
                "priority": issue.priority,
                "issue_type": issue.issue_type,
                "assignee": issue.assignee,
                "labels": list(issue.labels),
                "critical_path_descendants": descendants,
                "direct_unlocks": direct_unlocks,
                "score": total,
                "score_components": components,
                "unknown_hard_filter_facts": unknown_facts,
                "eligibility_complete": not unknown_facts,
                "promotion_authority": False,
            }
        )
    candidates.sort(
        key=lambda row: (
            -row["score"],
            row["priority"],
            -row["critical_path_descendants"],
            -row["direct_unlocks"],
            row["id"],
        )
    )
    return candidates, dict(sorted(excluded.items()))


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Rank live Beads frontiers deterministically and fail closed."
    )
    parser.add_argument(
        "--issues",
        type=Path,
        default=Path(".beads/issues.jsonl"),
    )
    parser.add_argument("--overlay", type=Path)
    parser.add_argument(
        "--owner",
        help=(
            "Caller identity for matching recorded assignments; never claims work "
            "or resolves an unassigned in-progress issue."
        ),
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Require every non-Beads hard-filter fact in the overlay.",
    )
    parser.add_argument("--limit", type=int, default=10)
    return parser


def main(argv: Iterable[str] | None = None) -> int:
    args = build_parser().parse_args(list(argv) if argv is not None else None)
    if args.limit <= 0:
        die("--limit must be positive")
    try:
        issues, digest = load_issues(args.issues)
        overlays, overlay_digest = load_overlay_snapshot(args.overlay, set(issues))
        candidates, excluded = rank(
            issues,
            overlays,
            owner=args.owner,
            strict=args.strict,
        )
    except FrontierError as exc:
        die(str(exc))
    selected = candidates[0] if candidates else None
    document = {
        "schema": SCHEMA,
        "outcome": "ranked" if selected else "no_candidate",
        "authority": False,
        "eligibility_complete": bool(selected and selected["eligibility_complete"]),
        "read_only": True,
        "live_state_verified": False,
        "owner": args.owner,
        "strict": args.strict,
        "overlay_path": args.overlay.as_posix() if args.overlay is not None else None,
        "overlay_sha256": overlay_digest,
        "issues_path": args.issues.as_posix(),
        "issues_sha256": digest,
        "issue_count": len(issues),
        "candidate_count": len(candidates),
        "excluded": excluded,
        "selected": selected,
        "candidates": candidates[: args.limit],
    }
    print(
        json.dumps(
            document,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )
    )
    return 0 if selected else 3


if __name__ == "__main__":
    raise SystemExit(main())
