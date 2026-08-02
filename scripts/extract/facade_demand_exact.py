#!/usr/bin/env -S python3 -I -S
"""Exact elaborated facade demand for a curated mathlib metaprogram set (bead
`fln-l8f`, G0-8 acceptance b; plan §4.3, risk R1, OQ-3).

WHY THIS EXISTS: the resistance census's demand scan is LEXICAL and declares so —
"it bounds the demand's SHAPE; the exact set needs elaboration against a BUILT
corpus". This extractor is that elaboration, bounded to a curated set. It builds
nothing itself: it requires the curated modules already built at the pinned corpus
commit, elaborates a probe against their .oleans with the pinned Reference
(oracle-only, D5/D9), and records the EXACT constants each compiled declaration
references — types and available bodies — joined against the partition census and
the stub surface.

THE CURATED SET is a reviewed constant, chosen from a measured import-closure sweep
over every Mathlib.Tactic/Mathlib.Lean/Mathlib.Util module at the pinned corpus
commit: the closure distribution has a cliff (families at 1-12 modules, then 1582+),
and these nine sit below it — real tactic/linter/metaprogram code, union closure 23
modules, measured 7.3 s to build. Changing the set is a reviewed edit, not a knob.

MEASUREMENT BOUNDS, declared up front:
  1. Bodies the module system does not export have invisible demand: a declaration
     whose `value?` is absent contributes only its type. The count is disclosed per
     kind in the summary (ctor/rec/inductive carry no bodies anywhere; a hidden def
     body is a real under-count).
  2. The demand is the CURATED set's, not mathlib's: class bounded_model, a floor
     on the corpus-wide exact demand, never a census of it.

Output: NDJSON, schema fln-facade-demand-exact/1, sorted by (coverage, name).
"""

import argparse
import json
import os
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
RESISTANCE = os.path.join(REPO, "contracts", "facade_resistance.ndjson")
PARTITION = os.path.join(REPO, "contracts", "builtin_partition.tsv")
SCHEMA = "fln-facade-demand-exact/1"

CURATED = [
    "Mathlib.Lean.Elab.InfoTree",
    "Mathlib.Lean.Elab.Tactic.Meta",
    "Mathlib.Lean.Environment",
    "Mathlib.Lean.Expr.Basic",
    "Mathlib.Tactic.DeclarationNames",
    "Mathlib.Tactic.Lift",
    "Mathlib.Tactic.Linter.FlexibleLinter",
    "Mathlib.Tactic.Linter.Lint",
    "Mathlib.Tactic.TacticAnalysis",
]

# Toolchain module roots: a constant DEFINED in one of these modules ships with the
# pinned Reference itself. Package roots (Mathlib, Batteries, Qq, Aesop, ...) are
# corpus-internal and never facade demand.
TOOLCHAIN_ROOTS = {"Lean", "Init", "Std", "Lake"}


def pinned_toolchain():
    with open(os.path.join(REPO, "SUITE.lock"), encoding="utf-8") as fh:
        lock = fh.read()
    tag = corpus_commit = None
    for line in lock.splitlines():
        if line.startswith("reference "):
            for field in line.split():
                if field.startswith("tag="):
                    tag = field[4:]
        if line.startswith("corpus "):
            for field in line.split():
                if field.startswith("commit="):
                    corpus_commit = field[7:]
    if not tag or not corpus_commit:
        raise SystemExit("REFUSE: SUITE.lock lacks a Reference tag or Corpus commit")
    root = os.path.join(os.path.expanduser("~"), ".elan", "toolchains",
                        f"leanprover--lean4---{tag}", "bin")
    if not os.path.isfile(os.path.join(root, "lake")):
        raise SystemExit(f"SKIP: pinned Reference not installed at {root}")
    return root, tag, corpus_commit


def corpus_head(corpus):
    """Resolve the checkout's HEAD by reading .git directly — no subprocess, and a
    worker checkout without .git is refused rather than answered for."""
    git = os.path.join(corpus, ".git")
    if not os.path.isdir(git):
        raise SystemExit(f"REFUSE: {corpus} has no .git directory to attest its commit")
    with open(os.path.join(git, "HEAD"), encoding="utf-8") as fh:
        head = fh.read().strip()
    if not head.startswith("ref: "):
        return head
    ref = head[5:]
    loose = os.path.join(git, *ref.split("/"))
    if os.path.isfile(loose):
        with open(loose, encoding="utf-8") as fh:
            return fh.read().strip()
    packed = os.path.join(git, "packed-refs")
    if os.path.isfile(packed):
        with open(packed, encoding="utf-8") as fh:
            for line in fh:
                if line.strip().endswith(ref):
                    return line.split()[0]
    raise SystemExit(f"REFUSE: cannot resolve {ref} in {git}")


PROBE = r"""module
@IMPORTS@
public import Lean

open Lean

meta def censusKey : Name -> String
  | .anonymous => "a"
  | .str p s => censusKey p ++ "/s\"" ++ s ++ "\""
  | .num p k => censusKey p ++ "/n" ++ toString k

#eval show CoreM Unit from do
  let env <- getEnv
  let hdr := env.header
  let targets : Array Name := #[@TARGETS@]
  let mut seenTargets : Array Name := #[]
  for i in [0:hdr.moduleNames.size] do
    if targets.contains hdr.moduleNames[i]! then
      let mname := hdr.moduleNames[i]!
      seenTargets := seenTargets.push mname
      let md := hdr.moduleData[i]!
      for n in md.constNames do
        match env.find? n with
        | none => IO.println s!"GONE\t{mname}\t{n}"
        | some ci =>
          let kind := match ci with
            | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm"
            | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot"
            | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
          IO.println s!"DECL\t{mname}\t{n}\t{kind}\t{ci.value?.isSome}"
          let mut used := ci.type.getUsedConstants
          if let some v := ci.value? then used := used ++ v.getUsedConstants
          let mut emitted : NameSet := NameSet.empty
          for u in used do
            unless emitted.contains u do
              emitted := emitted.insert u
              let dm := match env.getModuleIdxFor? u with
                | some ui => s!"{hdr.moduleNames[ui.toNat]!}"
                | none => "<local>"
              IO.println s!"USE\t{mname}\t{u}\t{dm}\t{censusKey u}"
  for t in targets do
    unless seenTargets.contains t do IO.println s!"ABSENT\t{t}"
"""


def run_probe(corpus, toolchain_bin):
    imports = "\n".join(f"import all {m}" for m in CURATED)
    targets = ", ".join(f"`{m}" for m in CURATED)
    work = os.path.join(os.environ.get("TMPDIR", "/tmp"), f"fln-l8f-demand-{os.getpid()}")
    os.makedirs(work, exist_ok=True)
    src = os.path.join(work, "probe.lean")
    with open(src, "w", encoding="utf-8") as fh:
        fh.write(PROBE.replace("@IMPORTS@", imports).replace("@TARGETS@", targets))
    env = {k: v for k, v in os.environ.items() if k not in ("LEAN_PATH", "LEAN_SYSROOT")}
    env["PATH"] = toolchain_bin + os.pathsep + env.get("PATH", "")
    env["LC_ALL"] = "C"
    proc = subprocess.run(
        [os.path.join(toolchain_bin, "lake"), "env", "lean", src],
        capture_output=True, text=True, env=env, cwd=corpus, timeout=900,
    )
    if proc.returncode != 0:
        raise SystemExit(f"REFUSE: the pinned binary refused the probe:\n{proc.stderr[:1200]}")
    return proc.stdout


def load_partition():
    part = {}
    with open(PARTITION, encoding="utf-8") as fh:
        for line in fh:
            if line.startswith("#"):
                continue
            fields = line.rstrip("\n").split("\t")
            if len(fields) >= 3 and fields[0] == "partition":
                part[fields[1]] = fields[2]
    if not part:
        raise SystemExit("REFUSE: partition census loaded zero rows — a broken load "
                         "would classify every demand as census-missing")
    return part


def load_stub_surface():
    names = set()
    with open(RESISTANCE, encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise SystemExit(
                    f"REFUSE: {RESISTANCE}:{lineno} is not JSON ({exc}) — a damaged "
                    f"resistance census cannot define the stub surface") from exc
            if row.get("kind") == "symbol":
                names.add(row["name"])
    if not names:
        raise SystemExit("REFUSE: no symbol rows in the resistance census")
    return names


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", required=True,
                    help="mathlib4 checkout at the SUITE.lock corpus commit, with the "
                         "curated modules already built (lake build <CURATED>)")
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    toolchain_bin, tag, want_commit = pinned_toolchain()
    have_commit = corpus_head(args.corpus)
    if have_commit != want_commit:
        raise SystemExit(f"REFUSE: corpus at {have_commit}, SUITE.lock pins {want_commit}")

    stdout = run_probe(args.corpus, toolchain_bin)

    decls, uses, gone, absent = [], {}, [], []
    for line in stdout.splitlines():
        f = line.split("\t")
        if f[0] == "DECL" and len(f) == 5:
            decls.append({"module": f[1], "name": f[2], "kind": f[3],
                          "has_value": f[4] == "true"})
        elif f[0] == "USE" and len(f) == 5:
            key = (f[2], f[3], f[4])
            uses.setdefault(key, set()).add(f[1])
        elif f[0] == "GONE":
            gone.append(f[2])
        elif f[0] == "ABSENT":
            absent.append(f[1])
    if absent:
        raise SystemExit(f"REFUSE: curated modules absent from the probe environment: "
                         f"{absent} — build them first (lake build ...)")
    if not decls or not uses:
        raise SystemExit("REFUSE: the probe emitted no declarations or no uses — an "
                         "empty scan would read as an empty demand")

    part = load_partition()
    stubs = load_stub_surface()

    hidden = {}
    for d in decls:
        if not d["has_value"] and d["kind"] in ("def", "thm", "opaque"):
            hidden[d["kind"]] = hidden.get(d["kind"], 0) + 1

    demand, census_missing = {}, []
    counts = {"local": 0, "corpus-internal": 0, "toolchain-library-code": 0,
              "toolchain-user-facing-data": 0}
    for (name, defmod, key), used_by in sorted(uses.items()):
        if defmod == "<local>":
            counts["local"] += 1
            continue
        if defmod.split(".")[0] not in TOOLCHAIN_ROOTS:
            counts["corpus-internal"] += 1
            continue
        # probe emits the bare key body; census cells wrap it in quotes and escape
        cls = part.get('"' + key.replace('"', '\\"') + '"')
        if cls is None:
            census_missing.append(name)
        elif cls == "toolchain-api":
            # census_key is the probe's structural encoding (component kinds, /s
            # vs /n) — carried so no consumer ever re-derives it from the dotted
            # display name, which collapses numeric components into strings.
            demand[name] = {"def_module": defmod, "census_key": key,
                            "used_by": sorted(used_by)}
        else:
            counts[f"toolchain-{cls}"] = counts.get(f"toolchain-{cls}", 0) + 1
    if not demand:
        raise SystemExit("REFUSE: zero toolchain-api demand from a metaprogram corpus "
                         "— that is a broken join, not a self-sufficient corpus")

    covered = {n for n in demand if n in stubs}
    uncovered = {n for n in demand if n not in stubs}
    unused_stubs = sorted(stubs - set(demand))

    rows = [{
        "schema": SCHEMA, "kind": "summary", "pin": tag, "corpus_commit": have_commit,
        "curated_modules": CURATED, "decls": len(decls),
        "decl_bodies_unavailable": hidden, "distinct_used_constants": len(uses),
        "counts": counts, "census_missing": sorted(census_missing),
        "toolchain_api_demanded": len(demand), "covered_by_stubs": len(covered),
        "uncovered": len(uncovered), "stubs_not_demanded_here": len(unused_stubs),
        "gone": sorted(set(gone)),
        "claim_class": "bounded_model",
        "bound": "exact demand of the curated set only — a floor on corpus-wide "
                 "demand, never a census of it; hidden bodies contribute types only",
    }]
    for name in sorted(demand):
        rows.append({"kind": "symbol", "name": name,
                     "coverage": "covered" if name in covered else "uncovered",
                     **demand[name]})
    rows.sort(key=lambda r: (r.get("kind") != "summary",
                             r.get("coverage", ""), r.get("name", "")))

    tmp = args.out + ".tmp"
    with open(tmp, "w", encoding="utf-8") as fh:
        for row in rows:
            fh.write(json.dumps(row, sort_keys=True) + "\n")
    os.replace(tmp, args.out)
    print(f"facade-demand-exact: decls={len(decls)} used={len(uses)} "
          f"toolchain-api={len(demand)} covered={len(covered)} "
          f"uncovered={len(uncovered)} census-missing={len(census_missing)} pin={tag}",
          file=sys.stderr)


if __name__ == "__main__":
    main()
