#!/usr/bin/env python3
"""Derive the canonical G3 from-source file ladder from the pinned grammar censuses.

Bead: fln-vokf (acceptance criterion: "The ladder order for z8j.1.12 is derived
from it (a file becomes eligible when all its kinds exist).")

Inputs (checked in, extracted from the SUITE.lock-pinned Reference by
scripts/extract/gen_grammar_census.sh):
  - SUITE.lock
  - contracts/REFERENCE_GRAMMAR_CENSUS.txt
  - contracts/REFERENCE_SYNTAX_KIND_USE.txt

Output:
  - contracts/REFERENCE_G3_LADDER.txt

Usage:
  scripts/extract/gen_g3_file_ladder.py generate
  scripts/extract/gen_g3_file_ladder.py --check
"""

from __future__ import annotations

import difflib
import hashlib
import os
import sys
from pathlib import Path

SCHEMA = "fln-reference-g3-ladder/1"
ROOT = Path(__file__).resolve().parents[2]
SUITE_LOCK = ROOT / "SUITE.lock"
GRAMMAR_CENSUS = ROOT / "contracts" / "REFERENCE_GRAMMAR_CENSUS.txt"
KIND_USE_CENSUS = ROOT / "contracts" / "REFERENCE_SYNTAX_KIND_USE.txt"
LADDER_OUT = ROOT / "contracts" / "REFERENCE_G3_LADDER.txt"
SELF_PATH = Path(__file__).resolve()


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_provenance(path: Path, expected_schema: str) -> dict[str, str]:
    prov: dict[str, str] = {}
    for raw in path.read_text(encoding="utf-8").splitlines():
        if not raw or raw.startswith("#"):
            continue
        fields = raw.split("\t")
        tag = fields[0]
        if tag == "schema":
            if len(fields) != 2 or fields[1] != expected_schema:
                raise ValueError(f"{path.name}: expected schema {expected_schema}, got {fields!r}")
            prov["schema"] = fields[1]
        elif tag == "reference":
            if len(fields) != 4:
                raise ValueError(f"{path.name}: malformed reference row: {fields!r}")
            prov["reference"] = "\t".join(fields[1:])
        elif tag == "suite-lock-sha256":
            if len(fields) != 2:
                raise ValueError(f"{path.name}: malformed suite-lock-sha256 row: {fields!r}")
            prov["suite-lock-sha256"] = fields[1]
        elif len(prov) == 3:
            break
    for req in ("schema", "reference", "suite-lock-sha256"):
        if req not in prov:
            raise ValueError(f"{path.name}: missing provenance row {req}")
    return prov


def load_grammar_imports(path: Path) -> dict[str, list[str]]:
    imports: dict[str, list[str]] = {}
    declared_modules: int | None = None
    for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not raw or raw.startswith("#"):
            continue
        fields = raw.split("\t")
        if fields[0] == "count" and len(fields) == 3 and fields[1] == "init-std-modules":
            declared_modules = int(fields[2])
        elif fields[0] == "module":
            if len(fields) < 3 or not fields[2].startswith("imports="):
                raise ValueError(f"{path.name}:{lineno}: malformed module row")
            mod = fields[1]
            if mod in imports:
                raise ValueError(f"{path.name}:{lineno}: duplicate module {mod}")
            raw_imps = fields[2][len("imports=") :]
            imports[mod] = [x for x in raw_imps.split(" ") if x]
    if declared_modules is None or declared_modules != len(imports):
        raise ValueError(
            f"{path.name}: module count mismatch (declared={declared_modules}, found={len(imports)})"
        )
    for mod, deps in imports.items():
        for dep in deps:
            if dep not in imports:
                raise ValueError(f"{path.name}: module {mod} imports unknown module {dep}")
    return imports


def load_kind_use(path: Path) -> tuple[dict[str, str], dict[str, set[str]]]:
    paths: dict[str, str] = {}
    uses: dict[str, set[str]] = {}
    declared_files: int | None = None
    declared_kinds: int | None = None
    for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if not raw or raw.startswith("#"):
            continue
        fields = raw.split("\t")
        if fields[0] == "count" and len(fields) == 3:
            if fields[1] == "files":
                declared_files = int(fields[2])
            elif fields[1] == "distinct-kinds":
                declared_kinds = int(fields[2])
            elif fields[1] in ("errors", "faults") and int(fields[2]) != 0:
                raise ValueError(f"{path.name}:{lineno}: non-zero {fields[1]}={fields[2]}")
        elif fields[0] == "file":
            if len(fields) != 6 or fields[4] != "errors=0":
                raise ValueError(f"{path.name}:{lineno}: malformed or errored file row")
            mod = fields[1]
            if mod in paths:
                raise ValueError(f"{path.name}:{lineno}: duplicate file {mod}")
            paths[mod] = fields[2]
        elif fields[0] == "uses":
            if len(fields) != 3:
                raise ValueError(f"{path.name}:{lineno}: malformed uses row")
            mod = fields[1]
            if mod in uses:
                raise ValueError(f"{path.name}:{lineno}: duplicate uses row for {mod}")
            uses[mod] = {k for k in fields[2].split(" ") if k}
    if declared_files is None or declared_files != len(paths):
        raise ValueError(
            f"{path.name}: file count mismatch (declared={declared_files}, found={len(paths)})"
        )
    if set(paths) != set(uses):
        raise ValueError(f"{path.name}: file set and uses set differ")
    all_kinds = set().union(*uses.values()) if uses else set()
    if declared_kinds is None or declared_kinds != len(all_kinds):
        raise ValueError(
            f"{path.name}: distinct-kinds mismatch (declared={declared_kinds}, found={len(all_kinds)})"
        )
    return paths, uses


def compute_depths(imports: dict[str, list[str]]) -> dict[str, int]:
    depths: dict[str, int] = {}
    visiting: set[str] = set()

    def dfs(mod: str) -> int:
        if mod in depths:
            return depths[mod]
        if mod in visiting:
            raise ValueError(f"import cycle detected involving {mod}")
        visiting.add(mod)
        deps = imports[mod]
        depth = 0 if not deps else 1 + max(dfs(d) for d in deps)
        visiting.remove(mod)
        depths[mod] = depth
        return depth

    for mod in sorted(imports):
        dfs(mod)
    return depths


def compute_transitive_importers(imports: dict[str, list[str]]) -> dict[str, set[str]]:
    reverse: dict[str, list[str]] = {m: [] for m in imports}
    for mod, deps in imports.items():
        for dep in deps:
            reverse[dep].append(mod)

    trans: dict[str, set[str]] = {}
    for mod in sorted(imports):
        seen = {mod}
        stack = [mod]
        while stack:
            cur = stack.pop()
            for nxt in reverse[cur]:
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)
        trans[mod] = seen
    return trans


def parse_suite_lock_reference(path: Path) -> str:
    refs = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        if raw.startswith("reference "):
            parts = raw.split()
            tag = next((p.split("=", 1)[1] for p in parts if p.startswith("tag=")), None)
            commit = next((p.split("=", 1)[1] for p in parts if p.startswith("commit=")), None)
            tree = next((p for p in parts if p.startswith("tree=")), None)
            if not tag or not commit or not tree:
                raise ValueError(f"SUITE.lock: malformed reference row: {raw!r}")
            refs.append(f"{tag}\t{commit}\t{tree}")
    if len(refs) != 1:
        raise ValueError(f"SUITE.lock: expected 1 reference row, found {len(refs)}")
    return refs[0]


def build_ladder_text() -> str:
    suite_ref = parse_suite_lock_reference(SUITE_LOCK)
    grammar_sha = sha256_file(GRAMMAR_CENSUS)
    kind_use_sha = sha256_file(KIND_USE_CENSUS)
    generator_sha = sha256_file(SELF_PATH)

    g_prov = parse_provenance(GRAMMAR_CENSUS, "fln-reference-grammar-census/1")
    k_prov = parse_provenance(KIND_USE_CENSUS, "fln-reference-syntax-kind-use/1")
    if g_prov["reference"] != k_prov["reference"]:
        raise ValueError("grammar and kind-use censuses disagree on Reference pin")
    if g_prov["reference"] != suite_ref:
        raise ValueError(
            f"census Reference pin ({g_prov['reference']!r}) disagrees with SUITE.lock ({suite_ref!r})"
        )
    if g_prov["suite-lock-sha256"] != k_prov["suite-lock-sha256"]:
        raise ValueError("grammar and kind-use censuses came from different SUITE.lock snapshots")

    imports = load_grammar_imports(GRAMMAR_CENSUS)
    paths, uses = load_kind_use(KIND_USE_CENSUS)
    if set(imports) != set(paths):
        raise ValueError("module set mismatch between grammar census and kind-use census")

    depths = compute_depths(imports)
    reverse: dict[str, list[str]] = {m: [] for m in imports}
    remaining_deps: dict[str, int] = {}
    for mod, deps in imports.items():
        unique_deps = sorted(set(deps))
        imports[mod] = unique_deps
        remaining_deps[mod] = len(unique_deps)
        for dep in unique_deps:
            reverse[dep].append(mod)

    ready: set[str] = {m for m, deg in remaining_deps.items() if deg == 0}
    cumulative: set[str] = set()
    ordered: list[tuple[int, str, list[str], int]] = []
    first_seen_kind: dict[str, tuple[int, str]] = {}

    rank = 0
    while ready:
        rank += 1
        # Canonical deterministic key: fewest newly required syntax kinds, then
        # fewest total syntax kinds, then smallest import depth, then module name.
        chosen = min(
            ready,
            key=lambda m: (len(uses[m] - cumulative), len(uses[m]), depths[m], m),
        )
        ready.remove(chosen)
        added = sorted(uses[chosen] - cumulative)
        cumulative.update(added)
        for kind in added:
            first_seen_kind[kind] = (rank, chosen)
        ordered.append((rank, chosen, added, len(cumulative)))
        for dependent in reverse[chosen]:
            remaining_deps[dependent] -= 1
            if remaining_deps[dependent] == 0:
                ready.add(dependent)

    if len(ordered) != len(imports):
        raise ValueError(
            f"topological ladder ordered {len(ordered)} of {len(imports)} modules (import cycle?)"
        )

    trans_importers = compute_transitive_importers(imports)
    direct_users: dict[str, set[str]] = {k: set() for k in cumulative}
    for mod, ks in uses.items():
        for k in ks:
            direct_users[k].add(mod)

    ref_parts = g_prov["reference"].split("\t")
    pin_tag, pin_commit, pin_tree = ref_parts[0], ref_parts[1], ref_parts[2]

    lines = [
        "# REFERENCE_G3_LADDER.txt — GENERATED by scripts/extract/gen_g3_file_ladder.py (bead fln-vokf).",
        f"# Derived mechanically from REFERENCE_GRAMMAR_CENSUS.txt and REFERENCE_SYNTAX_KIND_USE.txt ({pin_tag} {pin_commit}).",
        "# Regenerate with the script; never edit by hand (Rule D5). Tab-separated rows;",
        "# multi-valued fields are space-separated ('-' when empty).",
        f"schema\t{SCHEMA}",
        f"reference\t{pin_tag}\t{pin_commit}\t{pin_tree}",
        f"grammar-census-sha256\t{grammar_sha}",
        f"kind-use-census-sha256\t{kind_use_sha}",
        f"generator-sha256\t{generator_sha}",
        f"count\tmodules\t{len(ordered)}",
        f"count\tdistinct-kinds\t{len(cumulative)}",
        f"count\tmax-depth\t{max(depths.values()) if depths else 0}",
    ]

    for rank_num, mod, added, cum_count in ordered:
        imp_str = " ".join(imports[mod]) if imports[mod] else "-"
        added_str = " ".join(added) if added else "-"
        lines.append(
            "\t".join(
                [
                    "ladder",
                    str(rank_num),
                    mod,
                    paths[mod],
                    f"depth={depths[mod]}",
                    f"new-kinds={len(added)}",
                    f"total-kinds={len(uses[mod])}",
                    f"cumulative-kinds={cum_count}",
                    f"imports={imp_str}",
                    f"added-kinds={added_str}",
                ]
            )
        )

    for kind in sorted(cumulative):
        d_users = direct_users[kind]
        t_users: set[str] = set()
        for u in d_users:
            t_users.update(trans_importers[u])
        first_rank, first_mod = first_seen_kind[kind]
        lines.append(
            "\t".join(
                [
                    "kind-reach",
                    kind,
                    f"direct={len(d_users)}",
                    f"transitive={len(t_users)}",
                    f"first-rank={first_rank}",
                    f"first-module={first_mod}",
                ]
            )
        )

    return "\n".join(lines) + "\n"


def main(argv: list[str]) -> int:
    mode = argv[1] if len(argv) > 1 else "generate"
    if mode not in ("generate", "--check"):
        print(f"usage: {argv[0]} [generate|--check]", file=sys.stderr)
        return 2
    try:
        rendered = build_ladder_text()
    except Exception as exc:
        print(f"[gen_g3_file_ladder] error: {exc}", file=sys.stderr)
        return 2

    if mode == "generate":
        tmp = LADDER_OUT.with_suffix(".txt.candidate")
        tmp.write_text(rendered, encoding="utf-8")
        os.replace(tmp, LADDER_OUT)
        print(
            f"[gen_g3_file_ladder] wrote {LADDER_OUT.relative_to(ROOT)} ({len(rendered.splitlines())} lines)",
            file=sys.stderr,
        )
        return 0

    if not LADDER_OUT.exists():
        print(f"[gen_g3_file_ladder] DRIFT: {LADDER_OUT.relative_to(ROOT)} is missing", file=sys.stderr)
        return 1
    current = LADDER_OUT.read_text(encoding="utf-8")
    if current != rendered:
        diff = difflib.unified_diff(
            current.splitlines(keepends=True),
            rendered.splitlines(keepends=True),
            fromfile=str(LADDER_OUT.relative_to(ROOT)),
            tofile="derived",
            n=2,
        )
        sys.stderr.writelines(list(diff)[:80])
        print("[gen_g3_file_ladder] DRIFT: published ladder does not match censuses", file=sys.stderr)
        return 1
    print("[gen_g3_file_ladder] no drift: REFERENCE_G3_LADDER.txt matches the censuses", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
