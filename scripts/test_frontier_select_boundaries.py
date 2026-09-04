import json
import subprocess
import sys
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import frontier_select as fs
from test_frontier_select import issue


class FrontierBoundaryTests(unittest.TestCase):
    def write_issues(self, rows):
        temp = tempfile.TemporaryDirectory()
        path = Path(temp.name) / "issues.jsonl"
        path.write_text(
            "".join(json.dumps(row) + "\n" for row in rows),
            encoding="utf-8",
        )
        self.addCleanup(temp.cleanup)
        return path

    def test_closed_dependency_is_a_cut_in_the_unresolved_cone(self):
        issues, _ = fs.load_issues(self.write_issues([
            issue("root"),
            issue("bridge", status="closed", blockers=("root",)),
            issue("leaf", blockers=("bridge",)),
        ]))
        ranked, _ = fs.rank(issues, {}, owner="agent", strict=False)
        by_id = {row["id"]: row for row in ranked}
        self.assertEqual(set(by_id), {"root", "leaf"})
        self.assertEqual(by_id["root"]["critical_path_descendants"], 0)
        self.assertEqual(by_id["root"]["direct_unlocks"], 0)
        self.assertEqual(by_id["root"]["score"], by_id["leaf"]["score"])

    def test_real_unlock_beats_descendants_behind_a_closed_bridge(self):
        rows = [
            issue("phantom-root"),
            issue("bridge", status="closed", blockers=("phantom-root",)),
            issue("live-root"),
            issue("live-child", blockers=("live-root",)),
        ]
        rows.extend(
            issue(f"already-ready-{index}", priority=4, blockers=("bridge",))
            for index in range(12)
        )
        issues, _ = fs.load_issues(self.write_issues(rows))
        ranked, _ = fs.rank(issues, {}, owner="agent", strict=False)
        self.assertEqual(ranked[0]["id"], "live-root")
        self.assertEqual(ranked[0]["critical_path_descendants"], 1)
        self.assertEqual(ranked[0]["direct_unlocks"], 1)

    def test_diamond_preserves_live_paths_and_reopened_work(self):
        issues, _ = fs.load_issues(self.write_issues([
            issue("root"),
            issue("left", blockers=("root",)),
            issue("right", blockers=("root",)),
            issue("leaf", blockers=("left", "right")),
        ]))
        reverse = fs.reverse_block_graph(issues)
        for left, right, expected in (
            ("open", "open", 3),
            ("closed", "open", 2),
            ("closed", "closed", 0),
            ("open", "closed", 2),
            ("open", "open", 3),
        ):
            with self.subTest(left=left, right=right):
                issues["left"] = replace(issues["left"], status=left)
                issues["right"] = replace(issues["right"], status=right)
                self.assertEqual(fs.descendant_count("root", reverse, issues), expected)

    def test_unresolved_cone_matches_independent_small_dag_closure(self):
        names = tuple(str(index) for index in range(4))
        possible_edges = tuple(
            (parent, child) for parent in range(4) for child in range(parent + 1, 4)
        )
        for edge_mask in range(1 << len(possible_edges)):
            edges = [
                edge for index, edge in enumerate(possible_edges)
                if edge_mask & (1 << index)
            ]
            base, _ = fs.load_issues(self.write_issues([
                issue(name, blockers=tuple(
                    names[parent] for parent, child in edges if names[child] == name
                ))
                for name in names
            ]))
            reverse = fs.reverse_block_graph(base)
            for closed_mask in range(1 << len(names)):
                active = [not (closed_mask & (1 << index)) for index in range(4)]
                issues = {
                    name: replace(base[name], status="open" if active[index] else "closed")
                    for index, name in enumerate(names)
                }
                reachable = [[False] * 4 for _ in range(4)]
                for parent, child in edges:
                    reachable[parent][child] = active[parent] and active[child]
                for via in range(4):
                    for parent in range(4):
                        for child in range(4):
                            reachable[parent][child] |= (
                                reachable[parent][via] and reachable[via][child]
                            )
                with self.subTest(edges=edge_mask, closed=closed_mask):
                    for index, name in enumerate(names):
                        if active[index]:
                            self.assertEqual(
                                fs.descendant_count(name, reverse, issues),
                                sum(reachable[index]),
                            )

    def test_duplicate_issue_fields_are_rejected_before_selection(self):
        row = issue("task")
        body = json.dumps(row)
        for key, conflicting in (
            ("id", "different"),
            ("status", "in_progress"),
            ("assignee", "other-agent"),
            ("dependencies", [{
                "issue_id": "task", "depends_on_id": "missing", "type": "blocks",
            }]),
        ):
            with self.subTest(key=key):
                path = self.write_issues([row])
                raw = "{" + json.dumps(key) + ":" + json.dumps(conflicting) + "," + body[1:]
                path.write_text(raw + "\n", encoding="utf-8")
                with self.assertRaisesRegex(fs.FrontierError, "duplicate JSON key"):
                    fs.load_issues(path)

    def test_duplicate_nested_dependency_target_is_not_last_write_wins(self):
        task = json.dumps(issue("task", blockers=("parent",)))
        task = task.replace(
            '"depends_on_id": "parent"',
            '"depends_on_id": "missing", "depends_on_id": "parent"',
        )
        path = self.write_issues([])
        path.write_text(
            json.dumps(issue("parent", status="closed")) + "\n" + task + "\n",
            encoding="utf-8",
        )
        with self.assertRaisesRegex(fs.FrontierError, "duplicate JSON key 'depends_on_id'"):
            fs.load_issues(path)

    def test_duplicate_overlay_facts_refuse_in_both_orders_and_when_equal(self):
        path = self.write_issues([]).with_name("overlay.json")
        for first, last in (("false", "true"), ("true", "false"), ("true", "true")):
            with self.subTest(first=first, last=last):
                path.write_text(
                    '{"task":{"first_failure_named":true,"artifacts_available":true,'
                    '"oracle_only_compliant":true,"toolchain_available":' + first
                    + ',"toolchain_available":' + last + '}}',
                    encoding="utf-8",
                )
                with self.assertRaisesRegex(fs.FrontierError, "duplicate JSON key"):
                    fs.load_overlays(path, {"task"})

    def test_duplicate_overlay_rows_and_decoded_keys_are_rejected(self):
        path = self.write_issues([]).with_name("overlay.json")
        cases = (
            '{"task":{"toolchain_available":false},"task":{"toolchain_available":true}}',
            r'{"task":{"toolchain_\u0061vailable":false,"toolchain_available":true}}',
        )
        for raw in cases:
            with self.subTest(raw=raw):
                path.write_text(raw, encoding="utf-8")
                with self.assertRaisesRegex(fs.FrontierError, "duplicate JSON key"):
                    fs.load_overlays(path, {"task"})

    def test_repeated_keys_in_distinct_objects_and_string_content_remain_valid(self):
        rows = [issue("a"), issue("b")]
        rows[0]["description"] = 'literal {"status":"closed","status":"open"}'
        path = self.write_issues(rows)
        original = path.read_bytes()
        issues, digest = fs.load_issues(path)
        facts = {
            "first_failure_named": True,
            "artifacts_available": True,
            "toolchain_available": True,
            "oracle_only_compliant": True,
        }
        overlay_path = path.with_name("overlay.json")
        overlay_path.write_text(json.dumps({"a": facts, "b": facts}), encoding="utf-8")
        overlays = fs.load_overlays(overlay_path, set(issues))
        ranked, excluded = fs.rank(issues, overlays, owner="agent", strict=True)
        self.assertEqual([row["id"] for row in ranked], ["a", "b"])
        self.assertTrue(all(row["eligibility_complete"] for row in ranked))
        self.assertTrue(all(not row["promotion_authority"] for row in ranked))
        self.assertEqual(excluded, {})
        self.assertEqual(issues["a"].description, rows[0]["description"])
        self.assertEqual(path.read_bytes(), original)
        self.assertEqual(digest, fs.hashlib.sha256(original).hexdigest())

    def test_cli_duplicate_overlay_refuses_without_an_authoritative_stdout(self):
        path = self.write_issues([issue("task")])
        overlay = path.with_name("overlay.json")
        raw = (
            '{"task":{"first_failure_named":true,"artifacts_available":true,'
            '"oracle_only_compliant":true,"toolchain_available":false,'
            '"toolchain_available":true}}'
        )
        overlay.write_text(raw, encoding="utf-8")
        process = subprocess.run(
            [
                sys.executable, str(Path(fs.__file__).resolve()),
                "--issues", str(path), "--overlay", str(overlay),
                "--owner", "agent", "--strict",
            ],
            capture_output=True, text=True, check=False, timeout=10,
        )
        self.assertEqual(process.returncode, 2, process.stdout)
        self.assertEqual(process.stdout, "")
        refusal = json.loads(process.stderr)
        self.assertEqual(refusal["schema"], fs.SCHEMA)
        self.assertEqual(refusal["outcome"], "refused")
        self.assertIn("duplicate JSON key", refusal["reason"])
        self.assertEqual(overlay.read_text(encoding="utf-8"), raw)


if __name__ == "__main__":
    unittest.main()
