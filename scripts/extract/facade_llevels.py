#!/usr/bin/env -S python3 -I -S
"""Per-symbol HONEST L-levels for the Mirror facade slice (bead `fln-l8f`, G0-8
acceptance c; plan §4.2 evidence axis, §4.3 facade-row columns, §18.1 Parity
Ledger, risk R1, OQ-3).

WHY THIS EXISTS. The resistance census buckets the demanded surface by the
MECHANISM through which semantics could leak, and it carries one L-level per
BUCKET — four strings for 560 symbols. The acceptance letter asks for the row's
own level: "every implementation-detail leak or hard semantic row, its
bit/observational/performance equivalence, current honest L-level, fixture,
Behavior Note candidate, load-bearing unknown, owner, and promotion prerequisite".
A bucket-level L-level cannot say that `Lean.MonadEnv.getEnv` is L0 while
`Lean.Expr.app` is L1 — and after the standalone facade was measured, that is
exactly the difference between them.

THE LADDER IS THE PLAN'S, NOT THIS SCRIPT'S (§4.2): L0 recognized (inventoried;
precise `unsupported`, never a guess) -> L1 shape-compatible (names/shapes exist;
development only) -> L2 behavioral (gated corpus passes) -> L3 differentially
closed -> L4 drop-in attested.

THE DERIVATION, so no row is judged:

  * L0 when the standalone facade cannot even DECLARE the row (quarantined), or
    when the row does not resolve in a real curated file's demand check. The shape
    does not exist, so L1 is false by the ladder's own words.
  * L1 when the row's name and Reference type stand up in the standalone facade
    (no Reference `Lean.*` in scope) — and no higher, for any row, ever, from this
    spike: NOTHING WAS EXECUTED here. L2 needs the metaprogram-corpus rig (§18.2),
    which is the promotion prerequisite this artifact hands forward.
  * The equivalence class (bit/obs/perf) is a TARGET, never an observation: no
    differential ran. Every row therefore carries claim_state TARGETED on that
    column and OBSERVED only on the L-level it measured.

Output: NDJSON, schema fln-facade-llevel/1. TOTAL over the demanded toolchain-api
surface by construction — a symbol with no row is a refusal, because §4.3's first
law is that an unclassifiable symbol blocks the L-level rather than being guessed.
"""

import argparse
import hashlib
import json
import os
import sys
from collections import Counter, defaultdict

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SCHEMA = "fln-facade-llevel/1"
OWNER = "W6-fln-elab"

# Prose that is identical across hundreds of rows belongs in ONE place. A ledger
# that repeats its own boilerplate per row is four times its own size and no
# easier to read; the codes below are expanded once, in the summary's legend.
LEGEND = {
    "owner": {
        "W6-fln-elab": "W6 · the generated facade registry in fln-elab, which plan "
                       "§22 Appendix C derives from the toolchain-api subset",
        "init-lane": "the Init/library-code lane (G1→G3), not the facade registry",
    },
    "evidence": {
        "curated-demand-check": "name and Reference type stand up against the "
            "standalone facade, checked as part of a real curated mathlib file's "
            "measured demand, with no Reference Lean.* in scope",
        "facade-standalone-elaboration": "declared and elaborated in the standalone "
            "facade; no curated file in this slice uses it, so no demand check "
            "exercised it",
        "facade-declaration-refused": "the standalone facade cannot declare the row "
            "at all; the pin's own diagnostic is in the mechanism column",
        "curated-demand-check-failed": "declared in the facade, but unresolved when "
            "a real curated file's demand was checked against the facade alone",
        "init-substrate": "defined under Init: the implicitly imported prelude "
            "serves the shape; the facade neither declares nor owns it",
    },
    "promotion_prerequisite": {
        "class-expression": "the facade must express what an axiom cannot — a class "
            "declared as a class, a transparent definition where defeq is demanded "
            "— before this row can reach L1",
        "diagnostic-repair": "repair the pin diagnostic this row carries, or record "
            "a precise typed Unsupported for it",
        "corpus-rig": "the §18.2 metaprogram-corpus rig must EXECUTE this row "
            "against the oracle before L2",
        "curated-use-then-rig": "a curated file that actually uses it, then the "
            "§18.2 rig; a row no real file demands cannot be promoted on this "
            "evidence",
        "init-source-elab": "Init source-elaborated by the native toolchain (G3), "
            "then the metaprogram-corpus rig for behavior",
    },
}

# The equivalence class each bucket TARGETS, with the reason it is a target and
# not a measurement. §4.3: bit = identical results always; obs = identical
# observable behavior, internal traces may differ; perf = identical results,
# different cost.
BUCKET_EQUIV = {
    "R-NONE": ("bit", "pure, safe and non-extern: nothing in the census marks a "
                      "leak path, so identical results are the target"),
    "R-EFFECT": ("obs", "toolchain-monad state can expose object identity, "
                        "allocation order and metavariable naming"),
    "R-UNSAFE": ("obs", "the unsafe safety class makes evaluation order and "
                        "nontermination observable"),
    "R-EXTERN": ("obs", "extern-backed: the observable behavior is the C "
                        "runtime's, not the source definition's"),
    "-": ("unclassified", "no resistance bucket"),
}
BEHAVIOR_NOTE = {"R-EFFECT", "R-UNSAFE", "R-EXTERN"}


def input_digest(path):
    """Bind a derived artifact to the exact bytes it was derived FROM. Every input
    here is itself generated and is being regenerated by other hands; a summary
    that names its inputs by PATH alone goes stale silently, and the reader cannot
    tell a fresh row from one derived before the input moved."""
    with open(path, "rb") as fh:
        return {"path": os.path.relpath(path, REPO),
                "sha256": hashlib.sha256(fh.read()).hexdigest()}


def load_ndjson(path):
    rows = []
    with open(path, encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            if not line.strip():
                continue
            try:
                rows.append(json.loads(line))
            except json.JSONDecodeError as exc:
                raise SystemExit(f"REFUSE: {path}:{lineno} is not JSON ({exc})") from exc
    if not rows:
        raise SystemExit(f"REFUSE: {path} is empty")
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--resistance", required=True)
    ap.add_argument("--module", required=True, help="fln-facade-module/1 NDJSON")
    ap.add_argument("--compile", required=True, help="fln-facade-compile/1 NDJSON")
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    demand = {}
    for row in load_ndjson(args.resistance):
        if row.get("kind") == "symbol" and row.get("partition", "toolchain-api") == "toolchain-api":
            demand[row["name"]] = row
    if not demand:
        raise SystemExit("REFUSE: no demanded toolchain-api rows to level")

    facade, init_rows = {}, set()
    for row in load_ndjson(args.module):
        if row.get("kind") != "decl":
            continue
        facade[row["name"]] = row
        if row.get("role") == "init-substrate":
            init_rows.add(row["name"])

    checks = defaultdict(dict)
    substrate_only = set()
    for row in load_ndjson(args.compile):
        if row.get("kind") != "check":
            continue
        checks[row["name"]][row["module"]] = row["verdict"]
        if row.get("substrate_only"):
            substrate_only.add(row["name"])
    if not checks:
        raise SystemExit("REFUSE: the compile artifact carries no checks — every "
                         "row would be levelled from declaration alone and the "
                         "measurement this script exists to consume is missing")

    out, counts, unclassified = [], Counter(), []
    for name in sorted(demand):
        res = demand[name]
        bucket = res.get("bucket", "-")
        equiv, equiv_why = BUCKET_EQUIV.get(bucket, BUCKET_EQUIV["-"])
        decl = facade.get(name)
        used_in = sorted(checks.get(name, {}))
        verdicts = set(checks.get(name, {}).values())

        if decl is None:
            # Demanded, but the facade emitter never saw it: unclassifiable here,
            # and §4.3's first law says such a row blocks rather than guesses.
            unclassified.append(name)
            continue
        if name in init_rows:
            level, evidence, mechanism = "L1", "init-substrate", None
            prereq, owner = "init-source-elab", "init-lane"
        elif not decl.get("emitted"):
            level, evidence = "L0", "facade-declaration-refused"
            mechanism = decl.get("quarantine_reason") or "not emitted"
            prereq, owner = "class-expression", OWNER
        elif verdicts and verdicts != {"available"}:
            level, evidence = "L0", "curated-demand-check-failed"
            mechanism = None
            prereq, owner = "diagnostic-repair", OWNER
        elif verdicts == {"available"}:
            level, evidence, mechanism = "L1", "curated-demand-check", None
            prereq, owner = "corpus-rig", OWNER
        else:
            level, evidence, mechanism = "L1", "facade-standalone-elaboration", None
            prereq, owner = "curated-use-then-rig", OWNER

        counts[level] += 1
        out.append({
            "schema": SCHEMA, "kind": "row", "name": name, "bucket": bucket,
            "l_level": level,
            "l_level_claim_state": "OBSERVED",
            "l_level_evidence": evidence,
            "equivalence_class": equiv,
            "equivalence_claim_state": "TARGETED",
            "mechanism": mechanism,
            "behavior_note_candidate": bucket in BEHAVIOR_NOTE,
            "load_bearing": res.get("provenance") in ("exact", "both") or bool(used_in),
            "load_bearing_basis": res.get("provenance", "unknown"),
            "used_by_curated": used_in,
            "served_by_init_substrate": name in substrate_only,
            "promotion_prerequisite": prereq,
            "owner": owner,
            "fixture": ("contracts/facade_compile.ndjson#" + name) if used_in
                       else ("contracts/facade_module.ndjson#" + name),
            "safety": res.get("safety"), "effect": res.get("effect"),
            "extern": res.get("extern"),
        })

    if unclassified:
        raise SystemExit(
            "REFUSE: the facade artifacts do not classify "
            f"{len(unclassified)} demanded symbols ({unclassified[:6]}) — plan §4.3's "
            "first law is that an unclassifiable symbol blocks the L-level rather "
            "than being guessed, so no partial ledger is emitted")

    # The ratchet order (acceptance d) at ROW granularity: L0 rows first, because
    # each names a mechanism the facade cannot express, and every one of them is a
    # symbol a real curated mathlib file actually uses.
    blockers = Counter((r["mechanism"] or r["l_level_evidence"]).split(" -- ")[-1][:90]
                       for r in out if r["l_level"] == "L0")
    summary = {
        "schema": SCHEMA, "kind": "summary", "claim_class": "bounded_model",
        "inputs": [input_digest(args.resistance), input_digest(args.module),
                   input_digest(args.compile)],
        "demanded_toolchain_api": len(demand), "rows": len(out),
        "unclassified": 0,
        "by_level": dict(counts),
        "legend": LEGEND,
        "equivalence_legend": {b: why for b, (_, why) in BUCKET_EQUIV.items()},
        "ceiling_note": "no row from this spike may exceed L1: nothing was executed; "
                        "L2 requires the gated metaprogram-corpus rig (§18.2)",
        "l0_blocking_mechanisms": blockers.most_common(),
        "ceiling": "L1",
        "ceiling_reason": "this spike declared and resolved types; it executed nothing",
        "ratchet": [
            {"step": 1, "target": "L0 rows whose blocker is class-hood",
             "action": "emit `class`/`structure` declarations rather than opaque "
                       "axioms for the demanded class surface, then re-run the "
                       "compile rig",
             "members": sum(1 for r in out if r["l_level"] == "L0"
                            and "not a class" in (r["mechanism"] or ""))},
            {"step": 2, "target": "remaining L0 rows",
             "action": "each names its own pin diagnostic in the module artifact; "
                       "repair or record a typed Unsupported",
             "members": sum(1 for r in out if r["l_level"] == "L0"
                            and "not a class" not in (r["mechanism"] or ""))},
            {"step": 3, "target": "L1 rows in R-NONE",
             "action": "native implementation + differential fixtures; L2 on a "
                       "gated corpus pass",
             "members": sum(1 for r in out if r["l_level"] == "L1" and r["bucket"] == "R-NONE")},
            {"step": 4, "target": "L1 rows in R-EFFECT/R-UNSAFE/R-EXTERN",
             "action": "Behavior Note plus golden decision traces before any "
                       "promotion; these leak identity, order or runtime behavior",
             "members": sum(1 for r in out if r["l_level"] == "L1"
                            and r["bucket"] in BEHAVIOR_NOTE)},
        ],
        "owner": OWNER,
    }
    tmp = args.out + ".tmp"
    with open(tmp, "w", encoding="utf-8") as fh:
        fh.write(json.dumps(summary, sort_keys=True) + "\n")
        for row in out:
            fh.write(json.dumps(row, sort_keys=True) + "\n")
    os.replace(tmp, args.out)
    print(f"facade-llevels: rows={len(out)} " +
          " ".join(f"{k}={v}" for k, v in sorted(counts.items())) +
          f" behavior_notes={sum(1 for r in out if r['behavior_note_candidate'])}",
          file=sys.stderr)


if __name__ == "__main__":
    main()
