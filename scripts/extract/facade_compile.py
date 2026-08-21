#!/usr/bin/env -S python3 -I -S
"""Compile the curated mathlib metaprogram slice's toolchain demand AGAINST THE
FACADE ALONE (bead `fln-l8f`, G0-8 acceptance b; plan §4.3, risk R1, OQ-3).

THE QUESTION THIS ANSWERS, and the one it does not. Acceptance (b) says "generated
facade stubs compile against real mathlib tactic code". Two readings live inside
that sentence and only one of them is affordable at G0:

  READING 1 (what this measures): every toolchain constant that a REAL curated
  mathlib metaprogram file actually uses — the elaborated demand measured in
  contracts/facade_demand_exact.ndjson, not a lexical guess — resolves, at its
  Reference type, against the standalone facade with NO Reference `Lean.*` in
  scope. That is a real compile against real demand, and it is falsifiable: the
  negative control below shows the same probe failing when the facade is emptied.

  READING 2 (NOT measured here, and named so nobody reads this artifact as it):
  elaborating the curated FILES themselves against the facade. Those files import
  Mathlib, Batteries, Aesop and Qq — the library-code partition — so that reading
  needs the whole library closure source-elaborated against the facade first. It
  is the Mirror rig's job and it is priced as such, not silently claimed here.

THE HIDDEN-ORACLE GUARDS, because a probe that quietly resolves its names through
the toolchain would report a perfect facade:

  * LEAN_PATH is the facade root and nothing else; no probe may contain `import
    Lean`; the facade root is refused if it holds any Reference artifact.
  * A NEGATIVE CONTROL runs the same probe against an EMPTY facade. If it does not
    fail, the whole run refuses: whatever the probe was proving, it was not the
    facade.

Output: NDJSON, schema fln-facade-compile/1 — one row per (module, symbol), one
per module, and a summary that carries the reading above with it.
"""

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from collections import Counter, defaultdict

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PARTITION = os.path.join(REPO, "contracts", "builtin_partition.tsv")
SCHEMA = "fln-facade-compile/1"


def pinned_lean():
    with open(os.path.join(REPO, "SUITE.lock"), encoding="utf-8") as fh:
        lock = fh.read()
    tag = corpus = None
    for line in lock.splitlines():
        if line.startswith("reference "):
            for field in line.split():
                if field.startswith("tag="):
                    tag = field[4:]
        if line.startswith("corpus "):
            for field in line.split():
                if field.startswith("commit="):
                    corpus = field[7:]
    if not tag:
        raise SystemExit("REFUSE: SUITE.lock has no Reference tag")
    path = os.path.join(os.path.expanduser("~"), ".elan", "toolchains",
                        f"leanprover--lean4---{tag}", "bin", "lean")
    if not os.path.isfile(path):
        raise SystemExit(f"SKIP: pinned Reference not installed at {path}")
    return path, tag, corpus


def load_partition():
    """census key -> partition class. The denominator of this measurement must not
    come from the facade's own manifest: asking the facade which symbols it should
    serve and then checking exactly those is a tautology, and it reads as full
    coverage no matter how small the facade is."""
    part = {}
    with open(PARTITION, encoding="utf-8", errors="replace") as fh:
        for lineno, line in enumerate(fh, 1):
            if not line.startswith("partition\t"):
                continue
            cols = line.rstrip("\n").split("\t")
            if len(cols) < 3:
                raise SystemExit(f"REFUSE: {PARTITION}:{lineno} is truncated")
            part[cols[1]] = cols[2]
    if not part:
        raise SystemExit("REFUSE: partition census loaded zero rows")
    return part


def load_demand(path, part):
    """Curated module -> the toolchain-api constants it actually uses, from the
    elaborated exact-demand artifact (never a lexical scan: `open Lean Meta Elab`
    makes ~95% of real usage unqualified, measured on this same slice)."""
    by_module = defaultdict(set)
    modules, seen = [], {}
    with open(path, encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise SystemExit(f"REFUSE: {path}:{lineno} is not JSON ({exc})") from exc
            if row.get("kind") == "summary":
                modules = row.get("curated_modules", [])
                continue
            if row.get("kind") != "symbol":
                continue
            key = row.get("census_key")
            if key is None:
                raise SystemExit(f"REFUSE: {path}:{lineno} carries no census_key")
            cls = part.get('"' + key.replace('"', '\\"') + '"')
            seen[row["name"]] = cls
            if cls != "toolchain-api":
                continue
            for module in row.get("used_by", ()):
                by_module[module].add(row["name"])
    if not modules:
        raise SystemExit(f"REFUSE: {path} has no curated_modules summary — the slice "
                         "under test would be undefined")
    if not by_module:
        raise SystemExit("REFUSE: no toolchain-api demand joined — an empty demand "
                         "compiles vacuously and reads as full facade coverage")
    return modules, by_module, seen


def build_facade(lean, env, root, source, label):
    os.makedirs(root, exist_ok=True)
    dst = os.path.join(root, "FlnFacade.lean")
    shutil.copyfile(source, dst)
    proc = subprocess.run([lean, "-o", os.path.join(root, "FlnFacade.olean"), dst],
                          capture_output=True, text=True, env=env, timeout=1800)
    if proc.returncode != 0:
        raise SystemExit(f"REFUSE: the {label} facade does not build:\n"
                         f"{(proc.stdout + proc.stderr)[:1200]}")
    for entry in os.listdir(root):
        if entry.startswith("Lean") and entry != "FlnFacade.lean" and not entry.startswith("FlnFacade"):
            raise SystemExit(f"REFUSE: {root} holds {entry} — a facade root that "
                             "carries a Reference artifact is not a facade")
    return root


def probe_text(names):
    lines = ["import FlnFacade", "set_option autoImplicit false", ""]
    line_map = {}
    for name in names:
        lines.append(f"#check @{name}")
        line_map[len(lines)] = name
    return "\n".join(lines) + "\n", line_map


def run_probe(lean, root, work, tag_name, names):
    text, line_map = probe_text(names)
    if "import Lean" in text:
        raise SystemExit("REFUSE: a probe imports the Reference")
    src = os.path.join(work, f"probe_{tag_name}.lean")
    with open(src, "w", encoding="utf-8") as fh:
        fh.write(text)
    env = {k: v for k, v in os.environ.items() if k not in ("LEAN_PATH", "LEAN_SYSROOT")}
    env["LC_ALL"] = "C"
    env["LEAN_PATH"] = root
    proc = subprocess.run([lean, "-DmaxErrors=100000", src],
                          capture_output=True, text=True, env=env, timeout=1800)
    out = proc.stdout + proc.stderr
    verdict = {n: "available" for n in names}
    detail = {}
    base = os.path.basename(src)
    for m in re.finditer(rf"{re.escape(base)}:(\d+):\d+: error(?:\(([^)]*)\))?: (.*)",
                         out):
        name = line_map.get(int(m.group(1)))
        if name is None:
            continue
        kind, msg = (m.group(2) or ""), m.group(3)
        if "nknown" in kind or "nknown identifier" in msg or "nknown constant" in msg:
            verdict[name] = "unresolved"
        else:
            verdict[name] = "resolved-but-rejected"
        detail[name] = (kind or "-") + ": " + msg[:200]
    return verdict, detail, out
