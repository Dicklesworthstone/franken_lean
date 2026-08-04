#!/usr/bin/env -S python3 -I -S
"""Read-only convergence admission report for plan risk R15 (bead 149).

This is deliberately a *policy judge*, not a scheduler.  It never changes a bead and it never
derives authority from a title, label, PageRank, or a ``bv`` recommendation.  The reviewed,
versioned registry is the sole classifier.  ``bv`` is sampled only as advisory telemetry and its
absence is recorded rather than promoted into an admission failure.

The live mode obtains the issue and dependency snapshots from ``br``'s JSON surfaces twice.  A
change between the snapshots is an inconclusive result: a recommendation over moving inputs is
not permission to claim more work.  Fixture mode accepts those same normalized inputs from files;
it exists for the deterministic model tests and never mutates a production tracker.
"""

import argparse
import copy
import datetime as dt
import hashlib
import hmac
import json
import os
import pathlib
import subprocess
import sys


SCHEMA = "fln.convergence-governance-report/1"
POLICY_SCHEMA = "fln.convergence-governance-policy/1"
MAX_ISSUES = 10_000
MAX_EDGES = 100_000
MAX_REPORT_ITEMS = 512


class InputFault(Exception):
    """A missing, stale, malformed, or inconsistent input; never an admission."""


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)


def digest(value):
    return "sha256:" + hashlib.sha256(canonical(value).encode("ascii")).hexdigest()


def read_json(path, label):
    try:
        with open(path, encoding="utf-8") as source:
            return json.load(source)
    except (OSError, json.JSONDecodeError) as error:
        raise InputFault(f"{label}-unreadable: {error}") from error


def read_jsonl(path, label):
    rows = []
    try:
        with open(path, encoding="utf-8") as source:
            for number, raw in enumerate(source, 1):
                line = raw.strip()
                if not line:
                    continue
                try:
                    rows.append(json.loads(line))
                except json.JSONDecodeError as error:
                    raise InputFault(f"{label}-malformed-line-{number}: {error}") from error
    except OSError as error:
        raise InputFault(f"{label}-unreadable: {error}") from error
    return rows


def command(argv, cwd):
    try:
        outcome = subprocess.run(
            argv, cwd=cwd, text=True, capture_output=True, check=False, timeout=30
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise InputFault(f"command-unavailable: {' '.join(argv)}: {error}") from error
    if outcome.returncode:
        stderr = outcome.stderr.strip().replace("\n", " ")[:512]
        raise InputFault(
            f"command-failed-{outcome.returncode}: {' '.join(argv)}: {stderr}"
        )
    try:
        return json.loads(outcome.stdout)
    except json.JSONDecodeError as error:
        raise InputFault(f"command-non-json: {' '.join(argv)}: {error}") from error


def issues_from_br(root):
    envelope = command(
        ["br", "list", "--all", "--format", "json", "--no-auto-flush", "--no-auto-import"], root
    )
    if not isinstance(envelope, dict) or not isinstance(envelope.get("issues"), list):
        raise InputFault("br-list-schema: expected object with issues array")
    issues = envelope["issues"]
    if len(issues) > MAX_ISSUES:
        raise InputFault(f"br-list-too-many-issues: {len(issues)} > {MAX_ISSUES}")
    return issues


def edges_from_br(root, issues):
    # ``br list`` intentionally omits dependency edges.  ``br graph --all --json`` is the
    # tracker-owned, non-TUI graph projection for the mutable (open/in-progress/blocked)
    # surface; unlike bv it is authoritative here.  Its pair is [dependent, prerequisite].
    graph = command(
        ["br", "graph", "--all", "--json", "--no-auto-flush", "--no-auto-import"], root
    )
    components = graph.get("components") if isinstance(graph, dict) else None
    if not isinstance(components, list):
        raise InputFault("br-graph-schema: expected components array")
    known = {row.get("id") for row in issues if isinstance(row, dict)}
    edges = []
    for component in components:
        rows = component.get("edges") if isinstance(component, dict) else None
        if not isinstance(rows, list):
            raise InputFault("br-graph-schema: component has no edges array")
        for pair in rows:
            if not isinstance(pair, list) or len(pair) != 2 or not all(isinstance(item, str) and item for item in pair):
                raise InputFault("br-graph-schema: malformed dependency pair")
            child, parent = pair
            if child not in known or parent not in known:
                raise InputFault(f"br-graph-unknown-issue: {child}->{parent}")
            edges.append({"issue_id": child, "depends_on_id": parent, "type": "blocks"})
            if len(edges) > MAX_EDGES:
                raise InputFault(f"br-graph-too-many-edges: {len(edges)} > {MAX_EDGES}")
    return edges


def advisory_bv(root):
    # Advisory absence must not manufacture an Inconclusive governance decision.  Keep only a
    # digest and typed availability status; PageRank/keywords never reach classify() or decide().
    try:
        value = command(["bv", "--robot-graph", "--format", "json", "--no-cache"], root)
    except InputFault as error:
        return {"state": "absent", "reason": str(error)}
    return {"state": "present", "hash": digest(value)}


def load_live(root, evidence_path):
    issues = issues_from_br(root)
    edges = edges_from_br(root, issues)
    evidence = read_jsonl(evidence_path, "evidence")
    return {"issues": issues, "edges": edges, "evidence": evidence, "bv": advisory_bv(root)}


def stable_snapshot(load_snapshot):
    """Return a double-read snapshot or refuse a moving authority surface.

    ``bv`` is deliberately excluded from this equality root: it is advisory telemetry, so a
    timeout or ranking refresh cannot turn a stable tracker/evidence authority into a different
    admission decision.  The normalized tracker graph and evidence rows are the authority.
    """

    first = normalize_snapshot(load_snapshot())
    second = normalize_snapshot(load_snapshot())
    first_root = digest({"issues": first["issues"], "edges": first["edges"], "evidence": first["evidence"]})
    second_root = digest({"issues": second["issues"], "edges": second["edges"], "evidence": second["evidence"]})
    if not hmac.compare_digest(first_root, second_root):
        raise InputFault("snapshot-drift: pre/post br-or-evidence roots differ")
    return second


def normalize_snapshot(raw):
    issues = raw.get("issues") if isinstance(raw, dict) else None
    edges = raw.get("edges") if isinstance(raw, dict) else None
    evidence = raw.get("evidence") if isinstance(raw, dict) else None
    if not isinstance(issues, list) or not isinstance(edges, list) or not isinstance(evidence, list):
        raise InputFault("snapshot-schema: issues, edges, and evidence must be arrays")
    by_id = {}
    for issue in issues:
        if not isinstance(issue, dict):
            raise InputFault("issue-schema: non-object issue")
        issue_id, status = issue.get("id"), issue.get("status")
        if not isinstance(issue_id, str) or not issue_id:
            raise InputFault("issue-schema: empty id")
        if issue_id in by_id:
            raise InputFault(f"issue-duplicate-id: {issue_id}")
        if not isinstance(status, str) or not status:
            raise InputFault(f"issue-missing-status: {issue_id}")
        by_id[issue_id] = {key: issue[key] for key in sorted(issue)}
    normalized_edges = []
    for edge in edges:
        if not isinstance(edge, dict):
            raise InputFault("edge-schema: non-object edge")
        child = edge.get("issue_id")
        parent = edge.get("depends_on_id")
        relation = edge.get("type")
        if not all(isinstance(value, str) and value for value in (child, parent, relation)):
            raise InputFault("edge-schema: requires issue_id, depends_on_id, type")
        if child not in by_id or parent not in by_id:
            raise InputFault(f"edge-unknown-issue: {child}->{parent}")
        if relation == "blocks":
            normalized_edges.append({"issue_id": child, "depends_on_id": parent, "type": relation})
    normalized_edges.sort(key=lambda item: (item["issue_id"], item["depends_on_id"], item["type"]))
    if len(normalized_edges) != len({canonical(row) for row in normalized_edges}):
        raise InputFault("edge-duplicate")
    normalized_evidence = []
    for row in evidence:
        if not isinstance(row, dict):
            raise InputFault("evidence-schema: non-object row")
        normalized_evidence.append({key: row[key] for key in sorted(row)})
    normalized_evidence.sort(key=canonical)
    return {
        "issues": [by_id[key] for key in sorted(by_id)],
        "edges": normalized_edges,
        "evidence": normalized_evidence,
        "bv": raw.get("bv", {"state": "absent", "reason": "not-collected"}),
    }


def parse_policy(path):
    policy = read_json(path, "policy")
    if not isinstance(policy, dict) or policy.get("schema") != POLICY_SCHEMA:
        raise InputFault(f"policy-schema: expected {POLICY_SCHEMA}")
    for field in ("policy_version", "workstreams", "wip", "review", "gates", "registry", "exceptions"):
        if field not in policy:
            raise InputFault(f"policy-missing-{field}")
    if not isinstance(policy["policy_version"], str) or not policy["policy_version"]:
        raise InputFault("policy-empty-version")
    if not isinstance(policy["wip"], dict):
        raise InputFault("policy-wip-schema")
    for field in ("max_active_workstreams", "verification_reservation", "incident_reservation"):
        if not isinstance(policy["wip"].get(field), int) or policy["wip"][field] < 0:
            raise InputFault(f"policy-wip-{field}")
    if policy["wip"]["max_active_workstreams"] < 1:
        raise InputFault("policy-wip-max-active-workstreams-must-be-positive")
    workstreams = policy["workstreams"]
    if (
        not isinstance(workstreams, list)
        or not workstreams
        or not all(isinstance(item, str) and item for item in workstreams)
        or len(workstreams) != len(set(workstreams))
    ):
        raise InputFault("policy-workstreams-schema-or-duplicate")
    review = policy["review"]
    if not isinstance(review, dict):
        raise InputFault("policy-review-schema")
    if not isinstance(review.get("authority"), str) or not review["authority"]:
        raise InputFault("policy-review-missing-authority")
    cadence = review.get("cadence_days")
    if not isinstance(cadence, int) or isinstance(cadence, bool) or cadence < 1:
        raise InputFault("policy-review-invalid-cadence")
    utc(review.get("next_review"))
    if not isinstance(policy["gates"], list) or not policy["gates"]:
        raise InputFault("policy-gates-empty")
    if not isinstance(policy["registry"], list) or not isinstance(policy["exceptions"], list):
        raise InputFault("policy-registry-or-exceptions-schema")
    return policy


CLASSES = {"implementation", "prerequisite", "verification", "incident", "additive", "adoption"}
GATE_STATES = {"passed", "failed", "dependency_blocked", "not_yet_runnable"}


def utc(value):
    if not isinstance(value, str):
        raise InputFault("timestamp-not-string")
    try:
        parsed = dt.datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError as error:
        raise InputFault(f"timestamp-malformed: {value}") from error
    if parsed.tzinfo is None:
        raise InputFault(f"timestamp-missing-offset: {value}")
    return parsed.astimezone(dt.timezone.utc)


def validate(policy, snapshot, now):
    issues = {row["id"]: row for row in snapshot["issues"]}
    if utc(policy["review"]["next_review"]) <= now:
        raise InputFault(f"policy-review-expired: {policy['review']['next_review']}")
    registry = {}
    for row in policy["registry"]:
        if not isinstance(row, dict):
            raise InputFault("registry-non-object")
        issue_id, kind, workstream = row.get("id"), row.get("class"), row.get("workstream")
        if not isinstance(issue_id, str) or not issue_id or issue_id in registry:
            raise InputFault(f"registry-duplicate-or-empty-id: {issue_id}")
        if kind not in CLASSES:
            raise InputFault(f"registry-unknown-class-{issue_id}: {kind}")
        if not isinstance(workstream, str) or not workstream:
            raise InputFault(f"registry-missing-workstream: {issue_id}")
        if kind != "adoption" and workstream not in policy["workstreams"]:
            raise InputFault(f"registry-unreviewed-workstream: {issue_id}:{workstream}")
        if kind == "adoption" and workstream != "adoption":
            raise InputFault(f"registry-adoption-workstream: {issue_id}:{workstream}")
        if kind == "implementation":
            issue = issues.get(issue_id)
            labels = issue.get("labels") if isinstance(issue, dict) else None
            tracker_workstreams = sorted(
                label
                for label in labels
                if isinstance(label, str) and label.startswith("W") and label[1:].isdigit()
            ) if isinstance(labels, list) else []
            if tracker_workstreams != [workstream]:
                raise InputFault(
                    f"registry-tracker-workstream-mismatch: {issue_id}:"
                    f"registry={workstream}:tracker={','.join(tracker_workstreams) or '-'}"
                )
        registry[issue_id] = row
    missing_registry = sorted(set(registry) - set(issues))
    if missing_registry:
        raise InputFault("registry-missing-from-tracker: " + ",".join(missing_registry[:16]))
    gates = []
    seen_gates = set()
    for ordinal, gate in enumerate(policy["gates"]):
        if not isinstance(gate, dict):
            raise InputFault("gate-non-object")
        gate_id, state = gate.get("id"), gate.get("state")
        if not isinstance(gate_id, str) or not gate_id or gate_id in seen_gates:
            raise InputFault(f"gate-duplicate-or-empty-id: {gate_id}")
        if state not in GATE_STATES:
            raise InputFault(f"gate-state-{gate_id}: {state}")
        roots = gate.get("root_beads")
        if not isinstance(roots, list) or not roots or not all(isinstance(item, str) and item for item in roots):
            raise InputFault(f"gate-roots-{gate_id}")
        for root in roots:
            if root not in issues:
                raise InputFault(f"gate-root-missing-from-tracker: {gate_id}:{root}")
        seen_gates.add(gate_id)
        gates.append({"id": gate_id, "state": state, "root_beads": sorted(roots), "ordinal": ordinal})
    active = []
    for issue_id, issue in issues.items():
        if issue["status"] != "in_progress":
            continue
        if issue_id not in registry:
            raise InputFault(f"active-unclassified: {issue_id}")
        active.append({"id": issue_id, **registry[issue_id]})
    # Explicit adoption entries are a bounded drain, never a silent forever-exception.
    for row in active:
        if row["class"] == "adoption":
            expiry = row.get("expiry")
            if not expiry:
                raise InputFault(f"adoption-missing-expiry: {row['id']}")
            if utc(expiry) <= now:
                raise InputFault(f"adoption-expired: {row['id']}:{expiry}")
    exceptions = []
    for row in policy["exceptions"]:
        if not isinstance(row, dict):
            raise InputFault("exception-non-object")
        for field in ("id", "owner", "scope", "expiry", "review"):
            if not isinstance(row.get(field), str) or not row[field]:
                raise InputFault(f"exception-missing-{field}")
        if utc(row["expiry"]) <= now:
            raise InputFault(f"exception-expired: {row['id']}:{row['expiry']}")
        exceptions.append({key: row[key] for key in sorted(row)})
    # Detect a cycle in every semantic (blocks) edge, not just the roots selected by this policy.
    outgoing = {issue_id: [] for issue_id in issues}
    indegree = {issue_id: 0 for issue_id in issues}
    for edge in snapshot["edges"]:
        outgoing[edge["depends_on_id"]].append(edge["issue_id"])
        indegree[edge["issue_id"]] += 1
    queue = sorted(issue_id for issue_id, count in indegree.items() if count == 0)
    visited = 0
    while queue:
        node = queue.pop(0)
        visited += 1
        for child in sorted(outgoing[node]):
            indegree[child] -= 1
            if indegree[child] == 0:
                queue.append(child)
                queue.sort()
    if visited != len(issues):
        cyclic = sorted(issue_id for issue_id, count in indegree.items() if count)
        raise InputFault("graph-cycle: " + ",".join(cyclic[:16]))
    return registry, gates, sorted(active, key=lambda row: row["id"]), exceptions


def blocked_by(issue_id, edges, issues):
    return sorted(
        edge["depends_on_id"]
        for edge in edges
        if edge["issue_id"] == issue_id and issues[edge["depends_on_id"]]["status"] != "closed"
    )


def starved_days(issue, now):
    stamp = issue.get("updated_at") or issue.get("created_at")
    if not isinstance(stamp, str):
        return None
    try:
        return max(0, (now - utc(stamp)).days)
    except InputFault:
        return None


def decide(policy, snapshot, now):
    registry, gates, active, exceptions = validate(policy, snapshot, now)
    issues = {row["id"]: row for row in snapshot["issues"]}
    earliest = next((gate for gate in gates if gate["state"] != "passed"), None)
    active_workstreams = sorted({row["workstream"] for row in active if row["class"] == "implementation"})
    over_cap = len(active_workstreams) > policy["wip"]["max_active_workstreams"]
    admitted_workstreams = set(active_workstreams)
    verification_slots = policy["wip"]["verification_reservation"]
    incident_slots = min(policy["wip"]["incident_reservation"], len(exceptions))
    selected, held = [], []
    for issue_id in sorted(registry):
        row = registry[issue_id]
        issue = issues.get(issue_id)
        if issue is None or issue["status"] in ("closed", "tombstone"):
            continue
        blockers = blocked_by(issue_id, snapshot["edges"], issues)
        common = {
            "id": issue_id,
            "class": row["class"],
            "workstream": row["workstream"],
            "status": issue["status"],
            "blockers": blockers,
            "starvation_days": starved_days(issue, now),
        }
        if issue["status"] == "in_progress":
            common["reason"] = "already-active"
            selected.append(common)
            continue
        if blockers:
            common["reason"] = "dependency-blocked"
            held.append(common)
            continue
        if row["class"] == "incident" and incident_slots:
            incident_slots -= 1
            common["reason"] = "bounded-incident-exception"
            selected.append(common)
        elif row["class"] == "incident" and exceptions:
            common["reason"] = "incident-reservation-exhausted"
            held.append(common)
        elif row["class"] == "verification":
            if verification_slots:
                verification_slots -= 1
                common["reason"] = "reserved-independent-verification"
                selected.append(common)
            else:
                common["reason"] = "verification-reservation-exhausted"
                held.append(common)
        elif earliest and row.get("gate") == earliest["id"] and row["class"] in {"prerequisite", "verification", "implementation"}:
            if row["class"] == "implementation" and row["workstream"] not in admitted_workstreams:
                if over_cap:
                    common["reason"] = "held-over-cap"
                    held.append(common)
                elif len(admitted_workstreams) >= policy["wip"]["max_active_workstreams"]:
                    common["reason"] = "held-capacity"
                    held.append(common)
                else:
                    admitted_workstreams.add(row["workstream"])
                    common["reason"] = "earliest-gate-ready-blocker"
                    selected.append(common)
            else:
                common["reason"] = "earliest-gate-ready-blocker"
                selected.append(common)
        elif earliest and row["class"] == "additive":
            common["reason"] = "frozen-earliest-gate"
            held.append(common)
        else:
            common["reason"] = "held-priority-order"
            held.append(common)
    state = "over_cap" if over_cap else "complete"
    return {
        "state": state,
        "earliest_failing_gate": earliest["id"] if earliest else None,
        "critical_path": [gate["id"] for gate in gates if earliest is None or gate["ordinal"] <= earliest["ordinal"]],
        "active_workstreams": active_workstreams,
        "wip": policy["wip"],
        "selected": selected,
        "held": held,
        "exceptions": exceptions,
    }


def report(policy, snapshot, decision, now):
    evidence_gates = sorted(
        {gate for row in snapshot["evidence"] if isinstance(row.get("gate_ids"), list) for gate in row["gate_ids"] if isinstance(gate, str)}
    )
    value = {
        "schema": SCHEMA,
        "policy_schema": POLICY_SCHEMA,
        "policy_version": policy["policy_version"],
        "at": now.isoformat().replace("+00:00", "Z"),
        "verdict": decision["state"],
        "graph_hash": digest({"issues": snapshot["issues"], "edges": snapshot["edges"]}),
        "evidence_hash": digest(snapshot["evidence"]),
        "config_hash": digest(policy),
        "advisory_bv": snapshot["bv"],
        "evidence_gates": evidence_gates,
        **decision,
    }
    if len(value["selected"]) > MAX_REPORT_ITEMS or len(value["held"]) > MAX_REPORT_ITEMS:
        raise InputFault(
            f"report-item-limit: selected={len(value['selected'])} held={len(value['held'])} "
            f"limit={MAX_REPORT_ITEMS}"
        )
    return value


def concise(value):
    gate = value["earliest_failing_gate"] or "none"
    def bounded(rows):
        ids = [row["id"] for row in rows]
        head = ",".join(ids[:8]) or "none"
        return f"{head}+{len(ids) - 8}" if len(ids) > 8 else head
    return (
        f"convergence-governance: {value['verdict']}; earliest_gate={gate}; "
        f"active_workstreams={','.join(value['active_workstreams']) or 'none'}; "
        f"selected={bounded(value['selected'])}; held={bounded(value['held'])}"
    )


def snapshot_from_files(args):
    if not (args.issues and args.edges and args.evidence):
        raise InputFault("fixture-mode-requires-issues-edges-evidence")
    return {
        "issues": read_json(args.issues, "issues"),
        "edges": read_json(args.edges, "edges"),
        "evidence": read_jsonl(args.evidence, "evidence"),
        "bv": {"state": "absent", "reason": "fixture-mode"},
    }


def self_test():
    """Deterministic model/mutation cells with no tracker, filesystem, or clock mutation."""
    now = utc("2026-08-04T10:10:00Z")
    policy = {
        "schema": POLICY_SCHEMA,
        "policy_version": "self-test",
        "workstreams": ["W1", "W2", "W3"],
        "wip": {"max_active_workstreams": 2, "verification_reservation": 1, "incident_reservation": 1},
        "review": {"authority": "self-test", "cadence_days": 1, "next_review": "2026-08-05T10:10:00Z"},
        "gates": [
            {"id": "G0", "state": "failed", "root_beads": ["root"]},
            {"id": "G1", "state": "not_yet_runnable", "root_beads": ["later"]},
        ],
        "exceptions": [],
        "registry": [
            {"id": "root", "class": "prerequisite", "workstream": "W1", "gate": "G0"},
            {"id": "ready", "class": "prerequisite", "workstream": "W1", "gate": "G0"},
            {"id": "blocked", "class": "prerequisite", "workstream": "W1", "gate": "G0"},
            {"id": "additive", "class": "additive", "workstream": "W3", "gate": "G1"},
            {"id": "active-w1", "class": "implementation", "workstream": "W1", "gate": "G0"},
            {"id": "active-w2", "class": "implementation", "workstream": "W2", "gate": "G0"},
        ],
    }
    issues = [
        {"id": "root", "status": "open", "created_at": "2026-08-01T00:00:00Z"},
        {"id": "later", "status": "open", "created_at": "2026-08-01T00:00:00Z"},
        {"id": "ready", "status": "open", "created_at": "2026-08-01T00:00:00Z"},
        {"id": "blocked", "status": "open", "created_at": "2026-08-01T00:00:00Z"},
        {"id": "additive", "status": "open", "created_at": "2026-07-01T00:00:00Z"},
        {"id": "active-w1", "status": "in_progress", "labels": ["W1"], "created_at": "2026-08-01T00:00:00Z"},
        {"id": "active-w2", "status": "in_progress", "labels": ["W2"], "created_at": "2026-08-01T00:00:00Z"},
    ]
    edges = [{"issue_id": "blocked", "depends_on_id": "root", "type": "blocks"}]
    raw = {"issues": issues, "edges": edges, "evidence": [{"bead": "root", "gate_ids": ["G0"]}]}
    first = normalize_snapshot(raw)
    reordered = normalize_snapshot({"issues": list(reversed(issues)), "edges": list(reversed(edges)), "evidence": raw["evidence"]})
    first_decision = decide(policy, first, now)
    second_decision = decide(policy, reordered, now)
    if first_decision != second_decision:
        raise AssertionError("reordered JSON changed a semantic decision")
    selected = {row["id"]: row["reason"] for row in first_decision["selected"]}
    held = {row["id"]: row["reason"] for row in first_decision["held"]}
    if selected.get("ready") != "earliest-gate-ready-blocker":
        raise AssertionError("nearest ready earliest-gate blocker was not selected")
    if held.get("blocked") != "dependency-blocked":
        raise AssertionError("status-only blocking mutant survived")
    if held.get("additive") != "frozen-earliest-gate":
        raise AssertionError("failed earliest gate did not freeze additive work")
    for mutant, transform, token in [
        ("unknown-active", lambda rows: rows + [{"id": "unknown", "status": "in_progress"}], "active-unclassified"),
        ("cycle", lambda rows: rows, "graph-cycle"),
    ]:
        candidate = {"issues": transform(issues), "edges": list(edges), "evidence": raw["evidence"]}
        if mutant == "cycle":
            candidate["edges"] = edges + [{"issue_id": "root", "depends_on_id": "blocked", "type": "blocks"}]
        try:
            decide(policy, normalize_snapshot(candidate), now)
        except InputFault as error:
            if token not in str(error):
                raise AssertionError(f"{mutant} wrong refusal: {error}") from error
        else:
            raise AssertionError(f"{mutant} survived")
    over_policy = copy.deepcopy(policy)
    over_policy["registry"].append({"id": "active-w3", "class": "implementation", "workstream": "W3", "gate": "G0"})
    over_issues = issues + [{"id": "active-w3", "status": "in_progress", "labels": ["W3"], "created_at": "2026-08-01T00:00:00Z"}]
    if decide(over_policy, normalize_snapshot({"issues": over_issues, "edges": edges, "evidence": raw["evidence"]}), now)["state"] != "over_cap":
        raise AssertionError("over-cap mutant survived")
    expired = copy.deepcopy(policy)
    expired["registry"].append({"id": "adopted", "class": "adoption", "workstream": "adoption", "expiry": "2026-08-04T10:10:00Z"})
    try:
        decide(expired, normalize_snapshot({"issues": issues + [{"id": "adopted", "status": "in_progress"}], "edges": edges, "evidence": raw["evidence"]}), now)
    except InputFault as error:
        if "adoption-expired" not in str(error):
            raise AssertionError(f"expired-adoption wrong refusal: {error}") from error
    else:
        raise AssertionError("evergreen-adoption mutant survived")
    missing_expiry = copy.deepcopy(policy)
    missing_expiry["registry"].append(
        {"id": "adoption-missing", "class": "adoption", "workstream": "adoption"}
    )
    try:
        decide(
            missing_expiry,
            normalize_snapshot(
                {
                    "issues": issues + [{"id": "adoption-missing", "status": "in_progress"}],
                    "edges": edges,
                    "evidence": raw["evidence"],
                }
            ),
            now,
        )
    except InputFault as error:
        if "adoption-missing-expiry" not in str(error):
            raise AssertionError(f"missing adoption expiry wrong refusal: {error}") from error
    else:
        raise AssertionError("missing adoption expiry mutant survived")
    draining_adoption = copy.deepcopy(policy)
    draining_adoption["registry"].append(
        {
            "id": "adoption-drain",
            "class": "adoption",
            "workstream": "adoption",
            "expiry": "2026-08-04T10:11:00Z",
        }
    )
    drain_decision = decide(
        draining_adoption,
        normalize_snapshot(
            {
                "issues": issues + [{"id": "adoption-drain", "status": "in_progress"}],
                "edges": edges,
                "evidence": raw["evidence"],
            }
        ),
        now,
    )
    if not any(row["id"] == "adoption-drain" and row["reason"] == "already-active" for row in drain_decision["selected"]):
        raise AssertionError("bounded adoption drain was not retained as active")
    capacity_policy = copy.deepcopy(policy)
    capacity_policy["registry"].append(
        {"id": "candidate-w3", "class": "implementation", "workstream": "W3", "gate": "G0"}
    )
    capacity_decision = decide(
        capacity_policy,
        normalize_snapshot(
            {
                "issues": issues + [{"id": "candidate-w3", "status": "open", "labels": ["W3"]}],
                "edges": edges,
                "evidence": raw["evidence"],
            }
        ),
        now,
    )
    if not any(row["id"] == "candidate-w3" and row["reason"] == "held-capacity" for row in capacity_decision["held"]):
        raise AssertionError("concurrent admission capacity mutant survived")
    reservation_policy = copy.deepcopy(policy)
    reservation_policy["wip"] = {"max_active_workstreams": 2, "verification_reservation": 1, "incident_reservation": 1}
    reservation_policy["exceptions"] = [
        {"id": "INC-1", "owner": "self-test", "scope": "incident", "expiry": "2026-08-04T10:11:00Z", "review": "2026-08-04T10:11:00Z"}
    ]
    reservation_policy["registry"].extend(
        [
            {"id": "verification-a", "class": "verification", "workstream": "W1", "gate": "G0"},
            {"id": "verification-b", "class": "verification", "workstream": "W1", "gate": "G0"},
            {"id": "incident-a", "class": "incident", "workstream": "W1", "gate": "G0"},
            {"id": "incident-b", "class": "incident", "workstream": "W1", "gate": "G0"},
        ]
    )
    reservation_decision = decide(
        reservation_policy,
        normalize_snapshot(
            {
                "issues": issues
                + [
                    {"id": "verification-a", "status": "open"},
                    {"id": "verification-b", "status": "open"},
                    {"id": "incident-a", "status": "open"},
                    {"id": "incident-b", "status": "open"},
                ],
                "edges": edges,
                "evidence": raw["evidence"],
            }
        ),
        now,
    )
    selected_reservations = {row["id"]: row["reason"] for row in reservation_decision["selected"]}
    held_reservations = {row["id"]: row["reason"] for row in reservation_decision["held"]}
    if selected_reservations.get("incident-a") != "bounded-incident-exception" or held_reservations.get("incident-b") != "incident-reservation-exhausted":
        raise AssertionError("incident reservation was not bounded")
    if selected_reservations.get("verification-a") != "reserved-independent-verification" or held_reservations.get("verification-b") != "verification-reservation-exhausted":
        raise AssertionError("verification reservation was not bounded")
    expired_exception = copy.deepcopy(reservation_policy)
    expired_exception["exceptions"][0]["expiry"] = "2026-08-04T10:10:00Z"
    try:
        decide(
            expired_exception,
            normalize_snapshot(
                {
                    "issues": issues
                    + [
                        {"id": "verification-a", "status": "open"},
                        {"id": "verification-b", "status": "open"},
                        {"id": "incident-a", "status": "open"},
                        {"id": "incident-b", "status": "open"},
                    ],
                    "edges": edges,
                    "evidence": raw["evidence"],
                }
            ),
            now,
        )
    except InputFault as error:
        if "exception-expired" not in str(error):
            raise AssertionError(f"expired exception wrong refusal: {error}") from error
    else:
        raise AssertionError("evergreen exception mutant survived")
    expired_review = copy.deepcopy(policy)
    expired_review["review"]["next_review"] = "2026-08-04T10:10:00Z"
    try:
        decide(expired_review, first, now)
    except InputFault as error:
        if "policy-review-expired" not in str(error):
            raise AssertionError(f"expired review wrong refusal: {error}") from error
    else:
        raise AssertionError("expired review mutant survived")
    relabeled = copy.deepcopy(policy)
    relabeled["registry"][0]["workstream"] = "W999"
    try:
        decide(relabeled, first, now)
    except InputFault as error:
        if "registry-unreviewed-workstream" not in str(error):
            raise AssertionError(f"relabeling wrong refusal: {error}") from error
    else:
        raise AssertionError("workstream relabel mutant survived")
    orphaned = copy.deepcopy(policy)
    orphaned["registry"].append(
        {"id": "orphaned-registry", "class": "verification", "workstream": "W1", "gate": "G0"}
    )
    try:
        decide(orphaned, first, now)
    except InputFault as error:
        if "registry-missing-from-tracker" not in str(error):
            raise AssertionError(f"orphan registry wrong refusal: {error}") from error
    else:
        raise AssertionError("orphan registry mutant survived")
    tracker_relabel = copy.deepcopy(first)
    tracker_relabel["issues"] = [
        {**issue, "labels": ["W2"]} if issue["id"] == "active-w1" else issue
        for issue in tracker_relabel["issues"]
    ]
    try:
        decide(policy, tracker_relabel, now)
    except InputFault as error:
        if "registry-tracker-workstream-mismatch" not in str(error):
            raise AssertionError(f"tracker relabel wrong refusal: {error}") from error
    else:
        raise AssertionError("tracker workstream relabel mutant survived")
    drifting = copy.deepcopy(raw)
    drifting["issues"] = [
        {**issue, "status": "in_progress"} if issue["id"] == "ready" else issue
        for issue in drifting["issues"]
    ]
    snapshots = iter((raw, drifting))
    try:
        stable_snapshot(lambda: next(snapshots))
    except InputFault as error:
        if "snapshot-drift" not in str(error):
            raise AssertionError(f"snapshot drift wrong refusal: {error}") from error
    else:
        raise AssertionError("stale-snapshot admission mutant survived")
    advisory_absent = normalize_snapshot({**raw, "bv": {"state": "absent", "reason": "self-test"}})
    if decide(policy, advisory_absent, now) != first_decision:
        raise AssertionError("advisory bv absence changed an admission decision")
    return "convergence-governance self-test: 20 named model/mutation cells passed"


def main(argv):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default=".")
    parser.add_argument("--policy")
    parser.add_argument("--issues")
    parser.add_argument("--edges")
    parser.add_argument("--evidence")
    parser.add_argument("--at", default=dt.datetime.now(dt.timezone.utc).isoformat())
    parser.add_argument("--ndjson", help="write exactly one canonical newline-terminated report row")
    parser.add_argument("--check", action="store_true", help="return nonzero for policy refusal")
    parser.add_argument("--self-test", action="store_true", help="run in-memory deterministic model/mutation cells")
    args = parser.parse_args(argv)
    if args.self_test:
        try:
            print(self_test())
        except (AssertionError, InputFault) as error:
            print(f"convergence-governance self-test: FAILED: {error}", file=sys.stderr)
            return 2
        return 0
    root = pathlib.Path(args.root).resolve()
    policy_path = pathlib.Path(args.policy) if args.policy else root / "ci/CONVERGENCE_GOVERNANCE_POLICY.json"
    try:
        now = utc(args.at)
        policy = parse_policy(policy_path)
        if args.issues or args.edges or args.evidence:
            first = normalize_snapshot(snapshot_from_files(args))
            second = first
        else:
            evidence_path = root / "ci/VERIFICATION_MANIFEST.jsonl"
            second = stable_snapshot(lambda: load_live(root, evidence_path))
        value = report(policy, second, decide(policy, second, now), now)
        code = 0 if (not args.check or value["verdict"] == "complete") else 2
    except InputFault as error:
        value = {
            "schema": SCHEMA,
            "policy_schema": POLICY_SCHEMA,
            "verdict": "inconclusive",
            "reason": str(error),
        }
        code = 2 if args.check else 0
    print(concise(value) if "active_workstreams" in value else f"convergence-governance: inconclusive; reason={value['reason']}")
    row = canonical(value) + "\n"
    if args.ndjson:
        try:
            pathlib.Path(args.ndjson).write_text(row, encoding="utf-8")
        except OSError as error:
            print(f"convergence-governance: inconclusive; ndjson-write: {error}", file=sys.stderr)
            return 2
    else:
        sys.stdout.write(row)
    return code


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
