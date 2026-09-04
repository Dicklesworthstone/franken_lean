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


if __name__ == "__main__":
    unittest.main()
