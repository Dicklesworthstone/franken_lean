#!/usr/bin/env python3
from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent

SELECTOR = r'''
import hashlib,json
from dataclasses import dataclass
class FrontierError(Exception): pass
@dataclass(frozen=True)
class Issue:
 id:str; title:str; status:str; priority:int; issue_type:str; assignee:str|None; acceptance_criteria:str; description:str; labels:tuple; blockers:tuple
class Overlay: pass
def load_issues(path):
 raw=path.read_bytes(); out={}
 for line in raw.splitlines():
  if not line.strip(): continue
  row=json.loads(line); i=row["id"]
  if i in out: raise FrontierError(f"duplicate issue id {i!r}")
  out[i]=Issue(i,row.get("title",i),row.get("status","open"),row.get("priority",2),row.get("issue_type","task"),row.get("assignee"),row.get("acceptance_criteria","done"),row.get("description",""),tuple(row.get("labels",[])),())
 return out,hashlib.sha256(raw).hexdigest()
def load_overlays(path,ids): return {}
def rank(issues,overlays,*,owner,strict):
 rows=[]
 for x in issues.values():
  if x.status=="closed": continue
  rows.append({"id":x.id,"title":x.title,"status":x.status,"priority":x.priority,"issue_type":x.issue_type,"assignee":x.assignee,"labels":list(x.labels),"critical_path_descendants":0,"direct_unlocks":0,"score":1,"score_components":{},"unknown_hard_filter_facts":[],"promotion_authority":True})
 rows.sort(key=lambda row:row["id"]); return rows,{}
'''


def run(command: list[str], root: Path, input_bytes: bytes | None = None) -> subprocess.CompletedProcess[bytes]:
    return subprocess.run(
        command,
        cwd=root,
        input=input_bytes,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


class HierarchicalSeamTests(unittest.TestCase):
    def git(self, root: Path, *arguments: str) -> str:
        result = run(["git", *arguments], root)
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        return result.stdout.decode().strip()

    def capsule(
        self,
        root: Path,
        bead: str,
        owner: str,
        tracked: str,
        seam: str,
    ) -> dict[str, object]:
        commit = self.git(root, "rev-parse", "HEAD")
        return {
            "schema": "fln.agent-frontier/1",
            "bead": bead,
            "state": "in_progress",
            "owner": owner,
            "lease_observed_at": "2026-09-03T00:00:00Z",
            "anchor": {
                "branch": "main",
                "commit": commit,
                "tree": self.git(root, "rev-parse", "HEAD^{tree}"),
                "tracked_blobs": {
                    tracked: self.git(root, "rev-parse", f"HEAD:{tracked}")
                },
            },
            "semantic_seams": [seam],
            "frontier": {
                "artifact": "fixture",
                "pipeline": "parse -> verify",
                "last_proven": "zero",
                "first_failure": "one",
                "failure_class": "fixture",
            },
            "hypothesis": {
                "statement": "fixture hypothesis",
                "smallest_experiment": "run fixture",
                "protected_surfaces": ["other seams"],
            },
            "last_green": {
                "commit": commit,
                "commands": ["python fixture"],
                "receipts": [],
                "scope": "fixture",
            },
            "negative_evidence": [],
            "next": {
                "command": "python fixture",
                "success": "fixture passes",
                "failure_capture": "stderr",
            },
            "closure": {"criteria": ["fixture passes"], "still_missing": ["run"]},
        }

    def test_parent_and_descendant_semantic_claims_conflict(self) -> None:
        root = Path(tempfile.mkdtemp(prefix="fln-handoff-hierarchy-"))
        (root / "scripts").mkdir()
        shutil.copyfile(HERE / "agent_handoff.py", root / "scripts/agent_handoff.py")
        shutil.copytree(HERE / "agent_handoff_lib", root / "scripts/agent_handoff_lib")
        (root / "scripts/frontier_select.py").write_text(SELECTOR)
        shutil.copyfile(Path(__file__), root / "scripts/test_agent_handoff_hierarchy.py")
        (root / "scripts/test_agent_handoff.py").write_text("# fixture\n")
        (root / "scripts/check_agent_handoff.sh").write_text("#!/bin/sh\nexit 0\n")
        os.chmod(root / "scripts/agent_handoff.py", 0o755)
        (root / ".beads").mkdir()
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
        (root / "parent.txt").write_text("parent\n")
        (root / "child.txt").write_text("child\n")
        for command in (
            ["git", "init", "-b", "main"],
            ["git", "config", "user.name", "test"],
            ["git", "config", "user.email", "test@example.invalid"],
            ["git", "add", "."],
            ["git", "commit", "-m", "foundation"],
        ):
            result = run(command, root)
            self.assertEqual(result.returncode, 0, result.stderr.decode())

        rows = []
        for bead, owner, tracked, seam in (
            ("parent", "owner-a", "parent.txt", "fln-server/diagnostic authority"),
            (
                "child",
                "owner-b",
                "child.txt",
                "fln-server / diagnostic authority / wait completion",
            ),
        ):
            rows.append(
                {
                    "id": bead,
                    "title": bead,
                    "status": "in_progress",
                    "priority": 1,
                    "issue_type": "task",
                    "acceptance_criteria": "done",
                    "comments": [{"text": json.dumps(self.capsule(root, bead, owner, tracked, seam))}],
                }
            )
        (root / ".beads/issues.jsonl").write_text(
            "".join(json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n" for row in rows)
        )
        self.git(root, "add", ".beads/issues.jsonl")
        self.git(root, "commit", "-m", "claims")

        snapshot = run(
            [
                sys.executable,
                "scripts/agent_handoff.py",
                "snapshot",
                "--owner",
                "owner-a",
            ],
            root,
        )
        self.assertEqual(snapshot.returncode, 0, snapshot.stderr.decode())
        document = json.loads(snapshot.stdout)
        self.assertEqual(
            document["capsules"]["semantic_conflicts"],
            [
                {
                    "seam": "fln-server / diagnostic authority",
                    "claimants": [
                        {"bead": "child", "owner": "owner-b"},
                        {"bead": "parent", "owner": "owner-a"},
                    ],
                }
            ],
        )
        required = run(
            [
                sys.executable,
                "scripts/agent_handoff.py",
                "snapshot",
                "--owner",
                "owner-a",
                "--require-capsules",
            ],
            root,
        )
        self.assertEqual(required.returncode, 2)
        self.assertIn("seam_conflicts=1", json.loads(required.stderr)["reason"])


if __name__ == "__main__":
    unittest.main()
