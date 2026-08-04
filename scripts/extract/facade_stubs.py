#!/usr/bin/env -S python3 -I -S
"""Generate Mirror facade stubs for the demanded toolchain surface (bead `fln-l8f`,
G0-8 acceptance b; plan §4.3).

WHY THIS EXISTS AS A SECOND EXTRACTOR: the builtin census answers "did this type
change" and stores type DIGESTS (68,181 mix256 roots) — a perfect integrity witness
and a useless generator input, because `axiom X : mix256:5372…` is not Lean. Stub
generation needs the type ITSELF, so this extractor asks the pinned Reference for it
through the oracle-only census route (D5/D9): the binary pretty-prints each demanded
symbol's type from its own environment, and the stubs are emitted from that.

Bounded by construction: the input is the DEMANDED surface (the resistance census's
symbol rows), not the whole 204,543-constant environment — which is very likely why
the original census chose digests.

Output: a Lean source file of `axiom` declarations, one per demanded symbol, with the
bucket and effect recorded as comments so the facade's L-level ratchet is readable in
the artifact it generates.
"""

import argparse
import json
import os
import re
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
RESISTANCE = os.path.join(REPO, "contracts", "facade_resistance.ndjson")


def pinned_lean():
    with open(os.path.join(REPO, "SUITE.lock"), encoding="utf-8") as fh:
        lock = fh.read()
    tag = None
    for line in lock.splitlines():
        if line.startswith("reference "):
            for field in line.split():
                if field.startswith("tag="):
                    tag = field[4:]
    if not tag:
        raise SystemExit("REFUSE: SUITE.lock has no Reference tag")
    path = os.path.join(
        os.path.expanduser("~"), ".elan", "toolchains",
        f"leanprover--lean4---{tag}", "bin", "lean",
    )
    if not os.path.isfile(path):
        raise SystemExit(f"SKIP: pinned Reference not installed at {path}")
    return path, tag


def demanded_symbols():
    rows = []
    with open(RESISTANCE, encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise SystemExit(
                    f"REFUSE: {RESISTANCE}:{lineno} is not JSON ({exc}) — a damaged "
                    f"resistance census cannot define the stub surface") from exc
            if row.get("kind") == "symbol":
                rows.append(row)
    if not rows:
        raise SystemExit("REFUSE: no symbol rows in the resistance census — an empty "
                         "stub set would read as a facade with nothing to serve")
    return sorted(rows, key=lambda r: r["name"])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--plan",
                    help="also emit the dependency-ordered facade closure plan "
                         "(fln-facade-closure-plan/1) — acceptance (d)'s letter, "
                         "handed to the production census bead franken_lean-epx")
    args = ap.parse_args()

    lean, tag = pinned_lean()
    rows = demanded_symbols()
    names = "\n".join(f"    `{r['name']},"  for r in rows)
    program = (
        "import Lean\n"
        "open Lean in\n"
        "#eval show CoreM Unit from do\n"
        "  let env <- getEnv\n"
        "  let names : Array Name := #[\n" + names + "\n  ]\n"
        "  for n in names do\n"
        "    match env.find? n with\n"
        "    | some info =>\n"
        "      let fmt <- Meta.MetaM.run' (withOptions\n"
        "        (fun o => o.setBool `pp.fullNames true)\n"
        "        (Meta.ppExpr info.type))\n"
        "      let fmtx <- Meta.MetaM.run' (withOptions\n"
        "        (fun o => (o.setBool `pp.fullNames true).setBool `pp.explicit true)\n"
        "        (Meta.ppExpr info.type))\n"
        "      let lvls := \",\".intercalate (info.levelParams.map toString)\n"
        "      let deps := \",\".intercalate\n"
        "        ((info.type.getUsedConstants.map toString).toList)\n"
        "      IO.println s!\"TYPE\\t{n}\\t{lvls}\\t{fmt}\"\n"
        "      IO.println s!\"TYPEX\\t{n}\\t{lvls}\\t{fmtx}\"\n"
        "      IO.println s!\"DEPS\\t{n}\\t{deps}\"\n"
        "    | none => IO.println s!\"MISSING\\t{n}\"\n"
    )
    work = os.path.join(os.environ.get("TMPDIR", "/tmp"), f"fln-l8f-stubs-{os.getpid()}")
    os.makedirs(work, exist_ok=True)
    src = os.path.join(work, "probe.lean")
    with open(src, "w", encoding="utf-8") as fh:
        fh.write(program)
    env = {k: v for k, v in os.environ.items() if k not in ("LEAN_PATH", "LEAN_SYSROOT")}
    env["LC_ALL"] = "C"
    proc = subprocess.run([lean, src], capture_output=True, text=True, env=env, timeout=900)
    if proc.returncode != 0:
        raise SystemExit(f"REFUSE: the pinned binary refused the probe:\n{proc.stderr[:800]}")

    # The pretty-printer WRAPS at its default width, so a long type arrives as a
    # TYPE line plus continuation lines (measured: 6 stubs that did not parse
    # when emitted verbatim). Continuations are exactly the lines that open
    # neither marker, and joining them here is robust to any pp width — more so
    # than setting a format option the probe would have to keep matching.
    types, typesx, levels, deps, missing = {}, {}, {}, {}, []
    current = None
    for line in proc.stdout.splitlines():
        if line.startswith("TYPE\t"):
            _, name, lvls, ty = line.split("\t", 3)
            types[name] = ty
            levels[name] = lvls
            current = (types, name)
        elif line.startswith("TYPEX\t"):
            _, name, lvls, ty = line.split("\t", 3)
            typesx[name] = ty
            current = (typesx, name)
        elif line.startswith("DEPS\t"):
            _, name, dep_csv = line.split("\t", 2)
            deps[name] = [d for d in dep_csv.split(",") if d]
            current = None
        elif line.startswith("MISSING\t"):
            missing.append(line.split("\t", 1)[1])
            current = None
        elif current is not None and line.strip():
            d, name = current
            d[name] = d[name] + " " + line.strip()

    out = [
        "-- GENERATED by scripts/extract/facade_stubs.py from the pinned Reference",
        f"-- ({tag}) — Mirror facade stubs for the demanded toolchain surface",
        "-- (bead fln-l8f, G0-8 acceptance b). DO NOT EDIT.",
        "--",
        "-- Each stub is an `axiom`: a facade DECLARES the symbol's type and leaves",
        "-- the implementation to the native mirror. The bucket comment carries the",
        "-- resistance class from contracts/facade_resistance.ndjson, so the L-level",
        "-- ratchet is readable in the generated artifact rather than only beside it.",
        "--",
        "-- `autoImplicit false` is load-bearing: with it on, an unresolved name in a",
        "-- stub type silently becomes a bound type variable and elaboration proves",
        "-- only syntax — measured on the first generation of this file, which went",
        "-- green while >=100 of its type references resolved to nothing.",
        "import Lean",
        "set_option autoImplicit false",
        "namespace FlnFacade",
        "",
    ]
    header = out

    def render(explicit_for):
        body = list(header)
        stub_lines = {}
        count = 0
        for row in rows:
            name = row["name"]
            ty = typesx[name] if name in explicit_for else types.get(name)
            if ty is None:
                continue
            body.append(f"-- {row['bucket']} effect={row.get('effect')} "
                        f"extern={row.get('extern')}"
                        + (" pp=explicit" if name in explicit_for else ""))
            # A universe-polymorphic constant (casesOn, projections of
            # polymorphic structures) needs its level params declared, or the
            # printed `Sort u_1` is a free universe and the stub does not
            # elaborate.
            binder = "" if not levels[name] else ".{" + levels[name].replace(",", ", ") + "}"
            body.append(f"axiom {name.replace('.', '_')}{binder} : {ty}")
            stub_lines[len(body)] = name
            count += 1
        body.append("")
        body.append("end FlnFacade")
        for name in missing:
            body.append(f"-- MISSING FROM THE PINNED ENVIRONMENT: {name}")
        return "\n".join(body) + "\n", count, stub_lines

    # The generator verifies its own output before it may land: the pinned
    # binary must re-accept every printed type with autoImplicit off. The
    # default rendering is the readable one; a stub whose printed type does not
    # round-trip (pp elides an implicit that cannot be re-synthesized — Expr.
    # brecOn's `Expr.below t` was the measured case) is re-rendered with
    # pp.explicit, and only the stubs that needed it carry the marker. A
    # candidate that still fails stays on disk under its own name and never
    # replaces the artifact.
    candidate = args.out + ".candidate.lean"
    explicit_for = set()
    for attempt in (1, 2):
        text, emitted, stub_lines = render(explicit_for)
        with open(candidate, "w", encoding="utf-8") as fh:
            fh.write(text)
        proc = subprocess.run([lean, "-DmaxErrors=1000", candidate],
                              capture_output=True, text=True, env=env, timeout=900)
        if proc.returncode == 0:
            break
        if attempt == 2:
            raise SystemExit(
                f"REFUSE: the pinned binary rejects the generated stubs even "
                f"with pp.explicit fallback (candidate kept at {candidate}):\n"
                f"{(proc.stdout + proc.stderr)[:1500]}")
        failing = set()
        for m in re.finditer(r"\.candidate\.lean:(\d+):", proc.stdout + proc.stderr):
            name = stub_lines.get(int(m.group(1)))
            if name is not None:
                failing.add(name)
        if not failing:
            raise SystemExit(
                f"REFUSE: elaboration failed but no error line maps to a stub "
                f"(candidate kept at {candidate}):\n"
                f"{(proc.stdout + proc.stderr)[:1500]}")
        explicit_for = failing
    os.replace(candidate, args.out)

    plan_note = ""
    if args.plan:
        # Acceptance (d)'s letter: a VERSIONED, DEPENDENCY-ORDERED closure plan.
        # The ratchet buckets give the coarse order; this orders each stub after
        # every demanded symbol its TYPE references. Wave-based Kahn with a
        # declared tie-break (bucket rank, then name) so the order is
        # deterministic; a dependency cycle is emitted as disclosed residue,
        # never silently linearized.
        emitted_names = [row["name"] for row in rows if row["name"] in types]
        demand_set = set(emitted_names)
        bucket_of_name = {row["name"]: row["bucket"] for row in rows}
        undeps = [n for n in emitted_names if n not in deps]
        if undeps:
            raise SystemExit(f"REFUSE: no DEPS record for {undeps[:5]} — the plan "
                             "would silently omit edges")
        edges = {n: sorted({d for d in deps[n] if d in demand_set and d != n})
                 for n in emitted_names}
        bucket_rank = {"R-NONE": 0, "R-EFFECT": 1, "R-UNSAFE": 2, "R-EXTERN": 3}
        tie = lambda n: (bucket_rank.get(bucket_of_name[n], 99), n)
        remaining = dict(edges)
        order = []
        while remaining:
            ready = sorted((n for n, e in remaining.items()
                            if not any(d in remaining for d in e)), key=tie)
            if not ready:
                break
            for n in ready:
                order.append(n)
                del remaining[n]
        plan_schema = "fln-facade-closure-plan/1"
        plan_rows = [{"schema": plan_schema, "kind": "summary",
                      "steps": len(order), "cyclic_residue": len(remaining),
                      "stub_surface": len(emitted_names),
                      "handed_to": "franken_lean-epx", "pin": tag,
                      "tie_break": "bucket-rank-then-name"}]
        for i, n in enumerate(order, 1):
            plan_rows.append({"schema": plan_schema, "kind": "step", "order": i,
                              "name": n, "bucket": bucket_of_name[n],
                              "depends_on": edges[n]})
        for n in sorted(remaining, key=tie):
            plan_rows.append({"schema": plan_schema, "kind": "cyclic-residue",
                              "name": n, "bucket": bucket_of_name[n],
                              "in_cycle_deps": [d for d in edges[n] if d in remaining]})
        tmp = args.plan + ".tmp"
        with open(tmp, "w", encoding="utf-8") as fh:
            for r in plan_rows:
                fh.write(json.dumps(r, sort_keys=True) + "\n")
        os.replace(tmp, args.plan)
        plan_note = f" plan_steps={len(order)} cyclic_residue={len(remaining)}"

    print(
        f"facade-stubs: demanded={len(rows)} typed={emitted} missing={len(missing)} "
        f"elaborated=yes explicit_fallback={len(explicit_for)} pin={tag}{plan_note}",
        file=sys.stderr,
    )


if __name__ == "__main__":
    main()
