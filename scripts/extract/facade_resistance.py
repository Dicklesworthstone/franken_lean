#!/usr/bin/env -S python3 -I -S
"""The Mirror-facade resistance census and its ordered closure plan (bead
`fln-l8f`, G0-8 acceptance c+d; plan §4.3, risk R1, OQ-3).

WHAT THIS DERIVES, never judges: for every `Lean.*` symbol the REAL mathlib tactic
corpus demands, join the landed builtin census's own per-constant facts and bucket by
the MECHANISM through which observable semantics could leak — extern backing, unsafe
safety, or a nontrivial effect class. The ratchet order is then a function of the
buckets, not of anyone's opinion.

TWO MEASUREMENT BOUNDS, declared because both were paid for:

  1. The demand scan is LEXICAL. It over-approximates (a name in a comment counts)
     and under-approximates (`open Lean` appears in most files, hiding unqualified
     uses). It bounds the demand's SHAPE; the exact set needs elaboration against a
     BUILT corpus, which the host does not have.
  2. The census TSV QUOTES its values, so the absent-sentinel is the string `"-"`
     WITH quotes. Comparing against a bare `-` classified all 170 rows as
     extern-backed — a tidy-looking, entirely wrong answer. Values are unquoted at
     the join, and an empty join REFUSES rather than reporting "no resistance".

Output: NDJSON, schema fln-facade-resistance/1, sorted by (bucket, name).
"""

import argparse
import json
import os
import re
import sys
from collections import Counter

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
# The environment census is SHARDED (fln-census-out-of-git-2ya9): three
# observation shards, dot-numbered BEFORE the extension. Reading only the first
# silently manufactured 122 phantom orphans once — names present in shards 001
# and 002 scored "no constant row". The completeness check below makes a missing
# shard a refusal, never a quiet under-join.
ENV_SHARDS = [
    os.path.join(REPO, "contracts", "builtin_environment.tsv"),
    os.path.join(REPO, "contracts", "builtin_environment.001.tsv"),
    os.path.join(REPO, "contracts", "builtin_environment.002.tsv"),
]
PARTITION = os.path.join(REPO, "contracts", "builtin_partition.tsv")
SCHEMA = "fln-facade-resistance/1"

COLS = [
    "key", "display", "kind", "module", "levels", "arity", "telescope",
    "sig_root", "res_root", "res_head", "safety", "attrs", "extern",
    "impl_by", "effect",
]

# The ordered closure plan (acceptance d), expressed as the bucket order itself:
# cheapest and largest first, hardest and rarest last, each with the evidence a
# ratchet step demands before it may raise an L-level.
RATCHET = [
    ("R-NONE", "L2-on-landing, L3 with the metaprogram-corpus rig",
     "pure, safe, non-extern: nothing in the census marks a leak path"),
    ("R-EFFECT", "L1, ratchetable to L2 per symbol under the Mirror rig",
     "toolchain-monad state can expose identity, allocation order, mvar naming"),
    ("R-UNSAFE", "L0 until a fault-model decision; Behavior Note candidate",
     "unsafe safety class makes evaluation order and nontermination observable"),
    ("R-EXTERN", "L1 until a differential rig scores it against the runtime",
     "extern-backed: the observable behavior is the C runtime's, not the source's"),
]


def unquote(v):
    return v[1:-1] if len(v) >= 2 and v[0] == '"' and v[-1] == '"' else v


def key_of(name):
    return '"a/' + "/".join(f's\\"{p}\\"' for p in name.split(".")) + '"'


def scan_demand(corpus_dir):
    rx = re.compile(r"\bLean\.([A-Z]\w*(?:\.\w+)*)")
    demanded = set()
    files = 0
    for dirpath, dirnames, filenames in os.walk(corpus_dir):
        dirnames.sort()
        for f in sorted(filenames):
            if not f.endswith(".lean"):
                continue
            files += 1
            with open(os.path.join(dirpath, f), encoding="utf-8", errors="replace") as sfh:
                text = sfh.read()
            for m in rx.finditer(text):
                demanded.add(f"Lean.{m.group(1)}")
    if files == 0:
        raise SystemExit(f"REFUSE: no .lean files under {corpus_dir} — an empty scan "
                         "would report an empty demand, which reads as no dependence")
    return files, demanded


def load_exact_demand(path):
    """Symbol rows of fln-facade-demand-exact/1: dotted name -> carried structural
    census key (raw probe form). The key is carried, never re-derived from the
    dotted name, which collapses numeric components into strings."""
    exact = {}
    with open(path, encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            try:
                row = json.loads(line)
            except json.JSONDecodeError as exc:
                raise SystemExit(
                    f"REFUSE: {path}:{lineno} is not JSON ({exc})") from exc
            if row.get("kind") == "symbol":
                if "census_key" not in row:
                    raise SystemExit(
                        f"REFUSE: {path}:{lineno} symbol row carries no census_key "
                        "— regenerate the exact-demand artifact first")
                exact[row["name"]] = '"' + row["census_key"].replace('"', '\\"') + '"'
    if not exact:
        raise SystemExit(f"REFUSE: no symbol rows in {path} — an empty exact demand "
                         "would silently shrink the union to the lexical scan")
    return exact


def bucket_of(row):
    if row.get("extern") not in ("", "-") or row.get("impl_by") not in ("", "-"):
        return "R-EXTERN"
    if row.get("safety") not in ("safe", "", "-"):
        return "R-UNSAFE"
    if row.get("effect") not in ("pure", "", "-", "none"):
        return "R-EFFECT"
    return "R-NONE"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", required=True, help="a real tactic-source tree")
    ap.add_argument("--exact-demand",
                    help="fln-facade-demand-exact/1 NDJSON; when given, the demand "
                         "is the UNION of the lexical scan and the exact elaborated "
                         "set, each symbol row carrying its provenance")
    ap.add_argument("--out")
    args = ap.parse_args()

    files, demanded = scan_demand(args.corpus)
    exact = load_exact_demand(args.exact_demand) if args.exact_demand else {}
    provenance = {}
    keys = {}
    for n in demanded:
        keys[key_of(n)] = n
        provenance[n] = "lexical"
    for n, cell in exact.items():
        if n in provenance and key_of(n) != cell:
            # Two spellings of one key would join the same name twice and count
            # it in two rows; a dotted name that does not round-trip means the
            # "both" classification itself is unsound for this symbol.
            raise SystemExit(f"REFUSE: {n} is in both demand sources but its "
                             f"carried key {cell!r} differs from the derived "
                             f"{key_of(n)!r}")
        keys[cell] = n
        provenance[n] = "both" if n in provenance else "exact"

    toolchain = set()
    with open(PARTITION, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            if not line.startswith("partition\t"):
                continue
            cols = line.rstrip("\n").split("\t")
            if len(cols) >= 3 and cols[1] in keys and cols[2] == "toolchain-api":
                toolchain.add(cols[1])

    rows = {}
    declared = observed = 0
    for shard in ENV_SHARDS:
        with open(shard, encoding="utf-8", errors="replace") as fh:
            for line in fh:
                if line.startswith("constant_count\t"):
                    declared = max(declared, int(line.split("\t")[1]))
                if not line.startswith("observed\t"):
                    continue
                observed += 1
                cols = line.rstrip("\n").split("\t")[1:]
                if cols and cols[0] in toolchain:
                    rows[cols[0]] = {k: unquote(v) for k, v in zip(COLS, cols)}
    if observed != declared:
        raise SystemExit(f"REFUSE: {observed} observed rows across {len(ENV_SHARDS)} "
                         f"shards against a declared constant_count of {declared} — "
                         "a partial census turns shard boundaries into fake orphans")
    if not rows:
        raise SystemExit("REFUSE: empty census join — the row prefix or key form is "
                         "wrong, and an empty resistance list reads as no resistance")

    out = []
    counts = Counter()
    for key, row in rows.items():
        b = bucket_of(row)
        counts[b] += 1
        out.append((b, keys[key], row))
    # Names classified toolchain-api by partition but carrying no constant row:
    # disclosed, never dropped.
    orphans = sorted(keys[k] for k in toolchain - set(rows))

    order = {b: i for i, (b, _, _) in enumerate(RATCHET)}
    out.sort(key=lambda t: (order[t[0]], t[1]))
    lines = []
    for step, (bucket, level, reason) in enumerate(RATCHET, start=1):
        lines.append(
            f'{{"schema":"{SCHEMA}","kind":"ratchet-step","step":{step},'
            f'"bucket":"{bucket}","l_level":"{level}","reason":"{reason}",'
            f'"members":{counts[bucket]}}}'
        )
    for bucket, name, row in out:
        lines.append(
            f'{{"schema":"{SCHEMA}","kind":"symbol","bucket":"{bucket}",'
            f'"name":"{name}","provenance":"{provenance[name]}",'
            f'"safety":"{row.get("safety")}",'
            f'"effect":"{row.get("effect")}",'
            f'"extern":{"true" if row.get("extern") not in ("", "-") else "false"}}}'
        )
    for name in orphans:
        lines.append(
            f'{{"schema":"{SCHEMA}","kind":"orphan","name":"{name}",'
            f'"reason":"toolchain-api by partition with no constant row"}}'
        )
    lines.append(
        f'{{"schema":"{SCHEMA}","kind":"summary","tactic_files":{files},'
        f'"demanded_names":{len(demanded)},"exact_demanded":{len(exact)},'
        f'"union_demanded":{len(provenance)},"toolchain_api":{len(toolchain)},'
        f'"joined":{len(rows)},"orphans":{len(orphans)},'
        f'"resisting":{sum(counts[b] for b in ("R-EXTERN", "R-UNSAFE", "R-EFFECT"))},'
        f'"unresisting":{counts["R-NONE"]}}}'
    )
    text = "\n".join(lines) + "\n"
    if args.out:
        tmp = args.out + ".tmp"
        with open(tmp, "w", encoding="utf-8") as fh:
            fh.write(text)
        os.replace(tmp, args.out)
    else:
        sys.stdout.write(text)
    print(
        f"facade-resistance: files={files} demanded={len(demanded)} "
        f"exact={len(exact)} union={len(provenance)} "
        f"toolchain={len(toolchain)} joined={len(rows)} orphans={len(orphans)} "
        + " ".join(f"{b}={counts[b]}" for b, _, _ in RATCHET),
        file=sys.stderr,
    )


if __name__ == "__main__":
    main()
