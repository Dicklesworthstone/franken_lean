import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import frontier_select as fs


def issue(
    issue_id,
    *,
    status="open",
    priority=2,
    blockers=(),
    assignee=None,
    acceptance="done",
    labels=(),
):
    return {
        "id": issue_id,
        "title": issue_id,
        "description": "desc",
        "acceptance_criteria": acceptance,
        "status": status,
        "priority": priority,
        "issue_type": "task",
        "assignee": assignee,
        "labels": list(labels),
        "dependencies": [
            {
                "issue_id": issue_id,
                "depends_on_id": blocker,
                "type": "blocks",
            }
            for blocker in blockers
        ],
    }


class FrontierSelectTests(unittest.TestCase):
    def write_issues(self, rows):
        temp = tempfile.TemporaryDirectory()
        path = Path(temp.name) / "issues.jsonl"
        path.write_text(
            "".join(json.dumps(row) + "\n" for row in rows),
            encoding="utf-8",
        )
        self.addCleanup(temp.cleanup)
        return path

    def test_dependency_closure_and_unlocks_drive_ranking(self):
        path = self.write_issues(
            [
                issue("root", priority=2),
                issue("child", priority=1, blockers=("root",)),
                issue("leaf", priority=1, blockers=("child",)),
                issue("other", priority=2),
            ]
        )
        issues, _ = fs.load_issues(path)
        ranked, excluded = fs.rank(issues, {}, owner="agent", strict=False)
        self.assertEqual([row["id"] for row in ranked], ["root", "other"])
        self.assertEqual(ranked[0]["critical_path_descendants"], 2)
        self.assertEqual(ranked[0]["direct_unlocks"], 1)
        self.assertEqual(excluded["blocked_dependencies"], 2)

    def test_priority_precedes_small_unlock_difference(self):
        path = self.write_issues(
            [
                issue("p0", priority=0),
                issue("p1", priority=1),
                issue("child", priority=1, blockers=("p1",)),
            ]
        )
        issues, _ = fs.load_issues(path)
        ranked, _ = fs.rank(issues, {}, owner="agent", strict=False)
        self.assertEqual(ranked[0]["id"], "p0")

    def test_overlay_costs_and_context_are_explicit(self):
        path = self.write_issues([issue("a"), issue("b")])
        issues, _ = fs.load_issues(path)
        overlays = {
            "a": fs.Overlay(context_reuse=5, seam_isolation=5),
            "b": fs.Overlay(evidence_cost=5, collision_risk=5),
        }
        ranked, _ = fs.rank(issues, overlays, owner="agent", strict=False)
        self.assertEqual([row["id"] for row in ranked], ["a", "b"])
        self.assertFalse(ranked[0]["promotion_authority"])

    def test_strict_mode_requires_declared_hard_facts(self):
        path = self.write_issues([issue("a"), issue("b")])
        issues, _ = fs.load_issues(path)
        overlays = {
            "a": fs.Overlay(
                first_failure_named=True,
                artifacts_available=True,
                toolchain_available=True,
                oracle_only_compliant=True,
            )
        }
        ranked, excluded = fs.rank(issues, overlays, owner="agent", strict=True)
        self.assertEqual([row["id"] for row in ranked], ["a"])
        self.assertEqual(excluded["unknown_hard_filter_facts"], 1)
        self.assertTrue(ranked[0]["promotion_authority"])

    def test_false_hard_fact_refuses_candidate(self):
        path = self.write_issues([issue("a")])
        issues, _ = fs.load_issues(path)
        ranked, excluded = fs.rank(
            issues,
            {"a": fs.Overlay(toolchain_available=False)},
            owner="agent",
            strict=False,
        )
        self.assertEqual(ranked, [])
        self.assertEqual(excluded["declared_hard_filter_failure"], 1)

    def test_owner_collision_and_unowned_in_progress_are_filtered(self):
        path = self.write_issues(
            [
                issue("mine", status="in_progress", assignee="me"),
                issue("theirs", status="in_progress", assignee="other"),
                issue("unknown", status="in_progress"),
            ]
        )
        issues, _ = fs.load_issues(path)
        ranked, excluded = fs.rank(issues, {}, owner="me", strict=False)
        self.assertEqual([row["id"] for row in ranked], ["mine", "unknown"])
        self.assertEqual(excluded["owned_by_other"], 1)
        ranked, excluded = fs.rank(issues, {}, owner=None, strict=False)
        self.assertEqual(ranked, [])
        self.assertEqual(excluded["owned_by_other"], 2)
        self.assertEqual(excluded["unowned_in_progress"], 1)

    def test_input_order_does_not_change_ranking(self):
        rows = [issue("z"), issue("a"), issue("m")]
        first, _ = fs.load_issues(self.write_issues(rows))
        second, _ = fs.load_issues(self.write_issues(reversed(rows)))
        first_rank, _ = fs.rank(first, {}, owner="agent", strict=False)
        second_rank, _ = fs.rank(second, {}, owner="agent", strict=False)
        self.assertEqual([row["id"] for row in first_rank], ["a", "m", "z"])
        self.assertEqual(first_rank, second_rank)

    def test_duplicate_and_dangling_ids_fail_closed(self):
        duplicate = self.write_issues([issue("a"), issue("a")])
        with self.assertRaisesRegex(fs.FrontierError, "duplicate issue id"):
            fs.load_issues(duplicate)
        dangling = self.write_issues([issue("a", blockers=("missing",))])
        with self.assertRaisesRegex(fs.FrontierError, "dangling blocker"):
            fs.load_issues(dangling)

    def test_missing_acceptance_is_not_a_candidate(self):
        path = self.write_issues([issue("a", acceptance="")])
        issues, _ = fs.load_issues(path)
        ranked, excluded = fs.rank(issues, {}, owner="agent", strict=False)
        self.assertEqual(ranked, [])
        self.assertEqual(excluded["missing_acceptance_criteria"], 1)


if __name__ == "__main__":
    unittest.main()
