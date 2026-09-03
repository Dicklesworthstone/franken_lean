#!/usr/bin/env python3
from __future__ import annotations

import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).with_name("agent_handoff.py")
PACKAGE = Path(__file__).with_name("agent_handoff_lib")
SELECTOR = r'''
import hashlib, json
from dataclasses import dataclass
class FrontierError(Exception): pass
@dataclass(frozen=True)
class Issue:
 id:str; title:str; status:str; priority:int; issue_type:str; assignee:str|None; acceptance_criteria:str; description:str; labels:tuple; blockers:tuple
@dataclass(frozen=True)
class Overlay:
 context_reuse:int=0

def load_issues(path):
 raw=path.read_bytes(); out={}
 for n,line in enumerate(raw.splitlines(),1):
  if not line.strip(): continue
  try: row=json.loads(line)
  except Exception as e: raise FrontierError(f"invalid row {n}: {e}")
  i=row.get("id")
  if not isinstance(i,str) or not i: raise FrontierError(f"invalid id at row {n}")
  if i in out: raise FrontierError(f"duplicate issue id {i!r}")
  blockers=tuple(sorted(d.get("depends_on_id") for d in row.get("dependencies",[]) if d.get("type")=="blocks"))
  out[i]=Issue(i,row.get("title",i),row.get("status","open"),row.get("priority",2),row.get("issue_type","task"),row.get("assignee") or None,row.get("acceptance_criteria","accept"),row.get("description",""),tuple(sorted(row.get("labels",[]))),blockers)
 for issue in out.values():
  for blocker in issue.blockers:
   if blocker not in out: raise FrontierError(f"{issue.id} has dangling blocker {blocker!r}")
 return out,hashlib.sha256(raw).hexdigest()
def load_overlays(path,ids):
 if path is None: return {}
 root=json.loads(path.read_text())
 unknown=sorted(set(root)-ids)
 if unknown: raise FrontierError(f"unknown overlay ids: {unknown}")
 return {k:Overlay(int(v.get("context_reuse",0))) for k,v in root.items()}
def rank(issues,overlays,*,owner,strict):
 rows=[]; excluded={}
 for x in issues.values():
  if x.status=="closed": excluded["closed"]=excluded.get("closed",0)+1; continue
  if any(issues[b].status!="closed" for b in x.blockers): excluded["blocked_dependencies"]=excluded.get("blocked_dependencies",0)+1; continue
  if x.assignee and x.assignee!=owner: excluded["owned_by_other"]=excluded.get("owned_by_other",0)+1; continue
  score=(4-x.priority)*1000+overlays.get(x.id,Overlay()).context_reuse
  rows.append({"id":x.id,"title":x.title,"status":x.status,"priority":x.priority,"issue_type":x.issue_type,"assignee":x.assignee,"labels":list(x.labels),"critical_path_descendants":0,"direct_unlocks":0,"score":score,"score_components":{"priority":(4-x.priority)*1000,"context_reuse":overlays.get(x.id,Overlay()).context_reuse},"unknown_hard_filter_facts":[] if strict else ["toolchain_available"],"promotion_authority":strict})
 rows.sort(key=lambda r:(-r["score"],r["id"]))
 return rows,dict(sorted(excluded.items()))
'''


def run(cmd, cwd, input_bytes=None):
    return subprocess.run(
        cmd,
        cwd=cwd,
        input=input_bytes,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


class HandoffTests(unittest.TestCase):
    def repo(self, rows=None):
        root = Path(tempfile.mkdtemp(prefix="fln-handoff-"))
        (root / "scripts").mkdir()
        shutil.copyfile(SCRIPT, root / "scripts/agent_handoff.py")
        shutil.copytree(PACKAGE, root / "scripts/agent_handoff_lib")
        shutil.copyfile(Path(__file__), root / "scripts/test_agent_handoff.py")
        os.chmod(root / "scripts/agent_handoff.py", 0o755)
        (root / "scripts/frontier_select.py").write_text(SELECTOR)
        (root / "scripts/check_agent_handoff.sh").write_text("#!/bin/sh\nexit 0\n")
        (root / ".beads").mkdir()
        self.rows(root, rows or [self.row("low", 2), self.row("high", 0)])
        for path in (
            "AGENTS.md",
            "README.md",
            "COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md",
            "SUITE.lock",
            "AGENT_FRONTIER_PROTOCOL.md",
            "IMPLEMENTATION_STATUS.md",
            "CHANGELOG.md",
        ):
            (root / path).write_text(path + "\n")
        (root / "docs").mkdir()
        (root / "docs/AGENT_HANDOFF.md").write_text("handoff\n")
        (root / "evidence/frontiers").mkdir(parents=True)
        (root / "evidence/frontiers/one.json").write_text("{}\n")
        for cmd in (
            ["git", "init", "-b", "main"],
            ["git", "config", "user.name", "test"],
            ["git", "config", "user.email", "test@example.invalid"],
            ["git", "add", "."],
            ["git", "commit", "-m", "initial\n\nBead: high"],
        ):
            result = run(cmd, root)
            self.assertEqual(result.returncode, 0, result.stderr.decode())
        return root

    @staticmethod
    def row(i, p, status="open", **extra):
        return {
            "id": i,
            "title": i,
            "status": status,
            "priority": p,
            "issue_type": "task",
            "acceptance_criteria": "done",
            **extra,
        }

    @staticmethod
    def rows(root, rows):
        (root / ".beads/issues.jsonl").write_text(
            "".join(
                json.dumps(x, sort_keys=True, separators=(",", ":")) + "\n"
                for x in rows
            )
        )

    @staticmethod
    def snap(root, *args):
        return run(
            [sys.executable, "scripts/agent_handoff.py", "snapshot", *args], root
        )

    @staticmethod
    def verify(root, payload, *args):
        return run(
            [sys.executable, "scripts/agent_handoff.py", "verify", "-", *args],
            root,
            payload,
        )

    @staticmethod
    def git(root, *args):
        result = run(["git", *args], root)
        if result.returncode:
            raise AssertionError(result.stderr.decode())
        return result.stdout.decode().strip()

    def capsule(self, root, bead, owner, tracked="tracked.txt", seams=None):
        commit = self.git(root, "rev-parse", "HEAD")
        tree = self.git(root, "rev-parse", "HEAD^{tree}")
        blob = self.git(root, "rev-parse", f"HEAD:{tracked}")
        return {
            "schema": "fln.agent-frontier/1",
            "bead": bead,
            "state": "in_progress",
            "owner": owner,
            "lease_observed_at": "2026-09-03T00:00:00Z",
            "anchor": {
                "branch": "main",
                "commit": commit,
                "tree": tree,
                "tracked_blobs": {tracked: blob},
            },
            "semantic_seams": seams or [],
            "frontier": {
                "artifact": "fixture",
                "pipeline": "parse -> verify",
                "last_proven": "zero",
                "first_failure": "one",
                "failure_class": "fixture",
            },
            "hypothesis": {
                "statement": "fixture hypothesis",
                "smallest_experiment": "run the fixture",
                "protected_surfaces": ["other seams"],
            },
            "last_green": {
                "commit": commit,
                "commands": ["python test"],
                "receipts": [],
                "scope": "fixture",
            },
            "negative_evidence": [],
            "next": {
                "command": "python test",
                "success": "fixture passes",
                "failure_capture": "stderr",
            },
            "closure": {"criteria": ["fixture passes"], "still_missing": ["run"]},
        }

    def test_deterministic_snapshot_and_full_current_verification(self):
        root = self.repo()
        a = self.snap(root, "--strict", "--selection-strict", "--recent", "1")
        b = self.snap(root, "--strict", "--selection-strict", "--recent", "1")
        self.assertEqual(a.returncode, 0, a.stderr.decode())
        self.assertEqual(a.stdout, b.stdout)
        document = json.loads(a.stdout)
        self.assertEqual(document["schema"], "fln.agent-handoff/2")
        self.assertEqual(document["tracker"]["selected"]["id"], "high")
        self.assertTrue(document["authority"]["promotion_authority"])
        self.assertEqual(document["recent_commits"][0]["beads"], ["high"])
        verified = self.verify(root, a.stdout, "--current")
        self.assertEqual(verified.returncode, 0, verified.stderr.decode())
        receipt = json.loads(verified.stdout)
        self.assertEqual(receipt["schema"], "fln.agent-handoff-verification/2")
        self.assertEqual(receipt["verification_scope"], "anchored-reconstruction")
        self.assertIn("tracker", receipt["verified_sections"])

    def test_every_authoritative_section_is_reconstructed(self):
        root = self.repo()
        snapshot = self.snap(root, "--strict", "--selection-strict", "--recent", "1")
        self.assertEqual(snapshot.returncode, 0, snapshot.stderr.decode())
        original = json.loads(snapshot.stdout)
        mutations = {
            "authority": lambda d: d["authority"].__setitem__("promotion_authority", False),
            "tracker": lambda d: d["tracker"]["selected"].__setitem__("id", "forged"),
            "capsules": lambda d: d["capsules"].__setitem__("path_conflicts", [{"path": "x", "claimants": []}]),
            "frontier_evidence": lambda d: d["frontier_evidence"].clear(),
            "recent_commits": lambda d: d["recent_commits"][0].__setitem__("subject", "forged"),
            "warnings": lambda d: d["warnings"].append("forged"),
            "control_files": lambda d: d["control_files"].pop(),
            "request": lambda d: d["request"].__setitem__("recent", 2),
            "integrity": lambda d: d["integrity"].__setitem__("sha256", "0" * 64),
        }
        for label, mutate in mutations.items():
            document = json.loads(json.dumps(original))
            mutate(document)
            refused = self.verify(
                root,
                (json.dumps(document, sort_keys=True, separators=(",", ":")) + "\n").encode(),
            )
            self.assertEqual(refused.returncode, 2, label)
            self.assertIn(
                "does not match anchored reconstruction",
                json.loads(refused.stderr)["reason"],
                label,
            )

    def test_strict_requires_complete_regular_control_plane(self):
        root = self.repo()
        (root / "docs/AGENT_HANDOFF.md").unlink()
        self.git(root, "add", "-u")
        self.git(root, "commit", "-m", "remove control")
        strict = self.snap(root, "--strict", "--selection-strict")
        self.assertEqual(strict.returncode, 2)
        self.assertIn(
            "requires every control path", json.loads(strict.stderr)["reason"]
        )
        observed = self.snap(root, "--selection-strict")
        self.assertEqual(observed.returncode, 0, observed.stderr.decode())
        document = json.loads(observed.stdout)
        self.assertFalse(document["authority"]["promotion_authority"])
        self.assertIn("1 control paths are missing", document["warnings"])

    def test_dirty_tracker_is_never_misrepresented_as_anchored(self):
        root = self.repo()
        self.rows(root, [self.row("new", 1)])
        refused = self.snap(root)
        self.assertEqual(refused.returncode, 2)
        self.assertIn(
            "differs from the anchored HEAD blob", json.loads(refused.stderr)["reason"]
        )

    def test_current_and_archived_verification(self):
        root = self.repo()
        snapshot = self.snap(root, "--strict", "--selection-strict")
        self.assertEqual(snapshot.returncode, 0, snapshot.stderr.decode())
        self.rows(root, [self.row("new", 1)])
        self.git(root, "add", ".beads/issues.jsonl")
        self.git(root, "commit", "-m", "advance")
        stale = self.verify(root, snapshot.stdout, "--current")
        self.assertEqual(stale.returncode, 2)
        archived = self.verify(root, snapshot.stdout)
        self.assertEqual(archived.returncode, 0, archived.stderr.decode())
        receipt = json.loads(archived.stdout)
        self.assertFalse(receipt["current_head_matches"])
        self.assertFalse(receipt["current_tracker_matches"])
        self.assertTrue(receipt["anchor_on_current_main"])

    def test_complete_capsule_reuse_staleness_and_comment_order(self):
        root = self.repo()
        tracked = root / "tracked.txt"
        tracked.write_text("one\n")
        self.git(root, "add", "tracked.txt")
        self.git(root, "commit", "-m", "seam")
        old = self.capsule(root, "active", "old-owner")
        new = self.capsule(root, "active", "new-owner")
        row = self.row(
            "active",
            1,
            "in_progress",
            comments=[
                {
                    "created_at": "9999-12-31T00:00:00Z",
                    "text": json.dumps(old),
                },
                {
                    "created_at": "0001-01-01T00:00:00Z",
                    "text": json.dumps(new),
                },
            ],
        )
        self.rows(root, [row])
        self.git(root, "add", ".beads/issues.jsonl")
        self.git(root, "commit", "-m", "capsule")
        snapshot = self.snap(root, "--owner", "new-owner")
        self.assertEqual(snapshot.returncode, 0, snapshot.stderr.decode())
        record = json.loads(snapshot.stdout)["capsules"]["records"][0]
        self.assertEqual(record["owner"], "new-owner")
        self.assertEqual(record["freshness"], "reusable")
        tracked.write_text("two\n")
        self.git(root, "add", "tracked.txt")
        self.git(root, "commit", "-m", "move")
        stale = json.loads(self.snap(root, "--owner", "new-owner").stdout)[
            "capsules"
        ]["records"][0]
        self.assertEqual(stale["freshness"], "stale")
        self.assertEqual(stale["stale_paths"], ["tracked.txt"])

    def test_partial_capsule_is_invalid_and_required_mode_refuses(self):
        root = self.repo()
        tracked = root / "tracked.txt"
        tracked.write_text("one\n")
        self.git(root, "add", "tracked.txt")
        self.git(root, "commit", "-m", "seam")
        commit = self.git(root, "rev-parse", "HEAD")
        tree = self.git(root, "rev-parse", "HEAD^{tree}")
        blob = self.git(root, "rev-parse", "HEAD:tracked.txt")
        partial = {
            "schema": "fln.agent-frontier/1",
            "bead": "active",
            "state": "in_progress",
            "owner": "tester",
            "anchor": {
                "branch": "main",
                "commit": commit,
                "tree": tree,
                "tracked_blobs": {"tracked.txt": blob},
            },
        }
        self.rows(
            root,
            [
                self.row(
                    "active",
                    1,
                    "in_progress",
                    comments=[{"created_at": "x", "text": json.dumps(partial)}],
                )
            ],
        )
        self.git(root, "add", ".beads/issues.jsonl")
        self.git(root, "commit", "-m", "partial")
        ordinary = self.snap(root, "--owner", "tester")
        self.assertEqual(ordinary.returncode, 0, ordinary.stderr.decode())
        record = json.loads(ordinary.stdout)["capsules"]["records"][0]
        self.assertEqual(record["freshness"], "invalid")
        self.assertIn("lease_observed_at", record["reason"])
        required = self.snap(root, "--owner", "tester", "--require-capsules")
        self.assertEqual(required.returncode, 2)
        self.assertIn("invalid=1", json.loads(required.stderr)["reason"])

    def test_malformed_latest_capsule_does_not_silently_reuse_an_older_one(self):
        root = self.repo()
        tracked = root / "tracked.txt"
        tracked.write_text("one\n")
        self.git(root, "add", "tracked.txt")
        self.git(root, "commit", "-m", "seam")
        valid = self.capsule(root, "active", "owner")
        row = self.row(
            "active",
            1,
            "in_progress",
            comments=[
                {"created_at": "2026-09-03T00:00:00Z", "text": json.dumps(valid)},
                {
                    "created_at": "2026-09-03T00:01:00Z",
                    "text": '{"schema":"fln.agent-frontier/1","bead":',
                },
            ],
        )
        self.rows(root, [row])
        self.git(root, "add", ".beads/issues.jsonl")
        self.git(root, "commit", "-m", "malformed latest")
        snapshot = self.snap(root, "--owner", "owner")
        self.assertEqual(snapshot.returncode, 0, snapshot.stderr.decode())
        record = json.loads(snapshot.stdout)["capsules"]["records"][0]
        self.assertEqual(record["freshness"], "invalid")
        self.assertIn("unreadable frontier capsule", record["reason"])

    def test_input_paths_must_not_traverse_symlinks(self):
        root = self.repo()
        (root / "issues-link.jsonl").symlink_to(root / ".beads/issues.jsonl")
        refused = self.snap(root, "--issues", "issues-link.jsonl")
        self.assertEqual(refused.returncode, 2)
        self.assertIn("must not traverse a symbolic link", json.loads(refused.stderr)["reason"])

    def test_path_and_semantic_conflicts_block_authority(self):
        root = self.repo()
        tracked = root / "tracked.txt"
        tracked.write_text("one\n")
        self.git(root, "add", "tracked.txt")
        self.git(root, "commit", "-m", "seam")

        def row(bead, owner):
            capsule = self.capsule(
                root,
                bead,
                owner,
                seams=["fln-server / diagnostic publication authority"],
            )
            return self.row(
                bead,
                1,
                "in_progress",
                comments=[{"created_at": "2026-09-03T00:00:00Z", "text": json.dumps(capsule)}],
            )

        self.rows(root, [row("alpha", "owner-a"), row("beta", "owner-b")])
        self.git(root, "add", ".beads/issues.jsonl")
        self.git(root, "commit", "-m", "conflict")
        snapshot = self.snap(root, "--owner", "owner-a", "--selection-strict")
        self.assertEqual(snapshot.returncode, 0, snapshot.stderr.decode())
        document = json.loads(snapshot.stdout)
        self.assertFalse(document["authority"]["promotion_authority"])
        self.assertEqual(len(document["capsules"]["path_conflicts"]), 1)
        self.assertEqual(len(document["capsules"]["semantic_conflicts"]), 1)
        refused = self.snap(
            root,
            "--owner",
            "owner-a",
            "--selection-strict",
            "--require-capsules",
        )
        self.assertEqual(refused.returncode, 2)
        reason = json.loads(refused.stderr)["reason"]
        self.assertIn("path_conflicts=1", reason)
        self.assertIn("seam_conflicts=1", reason)

    def test_environment_is_explicitly_unverified_telemetry(self):
        root = self.repo()
        snapshot = self.snap(
            root, "--strict", "--selection-strict", "--include-environment"
        )
        self.assertEqual(snapshot.returncode, 0, snapshot.stderr.decode())
        document = json.loads(snapshot.stdout)
        document["environment"] = {"forged": "telemetry"}
        payload = (json.dumps(document, sort_keys=True, separators=(",", ":")) + "\n").encode()
        verified = self.verify(root, payload)
        self.assertEqual(verified.returncode, 0, verified.stderr.decode())
        self.assertFalse(json.loads(verified.stdout)["environment_telemetry_verified"])
        del document["environment"]
        refused = self.verify(
            root,
            (json.dumps(document, sort_keys=True, separators=(",", ":")) + "\n").encode(),
        )
        self.assertEqual(refused.returncode, 2)

    def test_no_clobber_publication_leaves_no_staging_files(self):
        root = self.repo()
        output = root / "out.json"
        output.write_text("sentinel\n")
        refused = self.snap(root, "--output", str(output))
        self.assertEqual(refused.returncode, 2)
        self.assertEqual(output.read_text(), "sentinel\n")
        self.assertEqual(list(root.glob(".out.json.handoff-*")), [])
        published = root / "published.json"
        success = self.snap(root, "--output", str(published))
        self.assertEqual(success.returncode, 0, success.stderr.decode())
        self.assertEqual(stat.S_IMODE(published.stat().st_mode), 0o644)
        self.assertEqual(json.loads(published.read_text())["schema"], "fln.agent-handoff/2")
        self.assertEqual(list(root.glob(".published.json.handoff-*")), [])

    def test_duplicate_ids_and_keys_fail_closed(self):
        root = self.repo()
        with (root / ".beads/issues.jsonl").open("a") as handle:
            handle.write(json.dumps(self.row("high", 0)) + "\n")
        duplicate = self.snap(root)
        self.assertEqual(duplicate.returncode, 2)
        self.assertIn("differs from the anchored HEAD blob", json.loads(duplicate.stderr)["reason"])
        self.git(root, "add", ".beads/issues.jsonl")
        self.git(root, "commit", "-m", "duplicate")
        duplicate = self.snap(root)
        self.assertEqual(duplicate.returncode, 2)
        self.assertIn("duplicate issue id", json.loads(duplicate.stderr)["reason"])

        root = self.repo()
        (root / ".beads/issues.jsonl").write_text(
            '{"id":"a","id":"b","title":"x","status":"open","priority":1,"issue_type":"task","acceptance_criteria":"done"}\n'
        )
        self.git(root, "add", ".beads/issues.jsonl")
        self.git(root, "commit", "-m", "duplicate key")
        duplicate_key = self.snap(root)
        self.assertEqual(duplicate_key.returncode, 2)
        self.assertIn("duplicate JSON key", json.loads(duplicate_key.stderr)["reason"])

    def test_commit_record_separator_does_not_split_log(self):
        root = self.repo()
        message = b"separator-safe\n\nbody has \x1e byte\n\nBead: high\n"
        committed = run(["git", "commit", "--allow-empty", "-F", "-"], root, message)
        self.assertEqual(committed.returncode, 0, committed.stderr.decode())
        recent = json.loads(self.snap(root, "--recent", "2").stdout)["recent_commits"]
        self.assertEqual(recent[0]["subject"], "separator-safe")
        self.assertEqual(recent[0]["beads"], ["high"])

    def test_anchored_overlay_is_part_of_reconstruction(self):
        root = self.repo()
        overlay = root / "overlay.json"
        overlay.write_text(json.dumps({"low": {"context_reuse": 5000}}))
        self.git(root, "add", "overlay.json")
        self.git(root, "commit", "-m", "overlay")
        snapshot = self.snap(
            root,
            "--strict",
            "--selection-strict",
            "--overlay",
            "overlay.json",
        )
        self.assertEqual(snapshot.returncode, 0, snapshot.stderr.decode())
        document = json.loads(snapshot.stdout)
        self.assertEqual(document["tracker"]["selected"]["id"], "low")
        self.assertFalse(document["authority"]["promotion_authority"])
        self.assertIn(
            "custom tracker or overlay input is observational and cannot carry promotion authority",
            document["warnings"],
        )
        self.assertEqual(self.verify(root, snapshot.stdout).returncode, 0)
        document["request"]["overlay"] = None
        refused = self.verify(
            root,
            (json.dumps(document, sort_keys=True, separators=(",", ":")) + "\n").encode(),
        )
        self.assertEqual(refused.returncode, 2)


if __name__ == "__main__":
    unittest.main()
