#!/usr/bin/env python3
"""Derive the population of ENFORCEMENT CLAIMS in AGENTS.md (bead `franken_lean-pfei`, R1).

An ENFORCEMENT CLAIM is a sentence asserting that some mechanism enforces something. A PRODUCER
is what the sentence names as doing the enforcing: a test function, a source site, a lane
script, a CI workflow, a bead. The defect class pfei was filed for is a claim with no producer,
or with one that does not denote -- four of them were measured FALSE in two days, each found by
a person reading rather than by a check, and two of the four cost a lane.

WHY THIS FILE IS IN THE REPOSITORY AND NOT IN /data/tmp
=======================================================
It lived at `/data/tmp/cc2-pfei-derive.py` for a day, run by nobody. That is the `pnav` shape --
a producer that exists but is not registered anywhere, so it neither runs nor rots visibly -- and
it is exactly the defect pfei itself is about, one floor up. A census whose only home is a
scratch directory dies at the next pane rotation together with every number it produced.

THE META REGION, AND WHY GETTING IT WRONG INVERTED THE ANSWER
=============================================================
Item 7 of "Evidence & Census Pins" is a CATALOGUE OF PAST DEFECTS. Its rows quote the very
phrases this scan searches for, because that is what the rows are about. Counting them makes the
scan's own subject matter into its own findings -- `fln-8zsq`'s lesson one floor up.

The predecessor of this file DECLARED that exclusion in a `META_HEADINGS` constant and **never
applied it**: the constant appeared exactly once in the file, at its own definition. The
consequence was not cosmetic. Measured 2026-07-27 across three commits:

    commit      total reported   inside item 7   LIVE (bound/unbound)
    94902fb7          26               4            22  (10/12)
    4e197f02          27               5            22  (10/12)
    7d7fe137          28               6            22  (10/12)

Every movement anyone ever recorded for this number -- 26 -> 27 -> 28, re-anchored across three
handoffs as evidence that "a count of claims is itself a claim" -- happened entirely inside the
catalogue. **The live population never moved.** A count bound to the unfiltered number would
have reddened on precisely the commits that record good work, since item 7 is the section this
repository edits most often, and people would have learned to ignore it. So the exclusion is
applied here, and its absence is a FAILURE rather than a silently wider scan.

WHAT THIS CENSUS DOES NOT ESTABLISH
===================================
`bound` means a producer is NAMED IN THE SAME SENTENCE. It does not mean the producer exists,
runs, or enforces what the sentence says -- that is pfei R2, and it is not implemented here.
A sentence citing a deleted test counts as bound. Read `bound` as "has a candidate referent",
never as "is verified".
"""

import argparse
import json
import re
import sys
from pathlib import Path

# Verbs that assert enforcement. Deliberately generous: R1 wants the population DERIVED, and a
# narrow pattern hand-tuned to the known instances would be the hand-listed scope the bead
# forbids (`fln-guard-scope-must-be-derived`: twelve evidence roots once hid behind a
# five-script list).
ENFORCE = re.compile(
    r"\b("
    r"CI (?:walks|checks|enforces|rejects|refuses|counts|proves)"
    r"|fails the build"
    r"|fails? (?:workspace-wide|the gate|the \w+ suite)"
    r"|runs? under plain `?cargo test`?"
    r"|is (?:held to the code|enforced|checked|refused|walked)"
    r"|(?:is|are) enforced"
    r"|turns `?cargo test`? red"
    r"|refuses (?:any|a|the) \w+"
    r"|the validator (?:checks|enforces|refuses)"
    r"|guard (?:refuses|fails|fires)"
    r"|blocks? (?:the )?(?:gate|release)"
    r"|must (?:fail|redden)"
    r"|nothing (?:holds|watches|binds)"
    r")\b",
    re.IGNORECASE,
)

# A producer is something addressable. These are the forms actually used in AGENTS.md.
PRODUCER = {
    "test-fn": re.compile(r"`[a-z_][a-z0-9_]{6,}`"),
    "source-site": re.compile(r"`[\w./-]+\.rs:\d+"),
    "source-file": re.compile(r"`[\w./-]+\.(?:rs|py|sh|txt|jsonl|toml|md)`"),
    "lane": re.compile(r"scripts/(?:e2e|tribunal|extract)/[\w.]+\.sh"),
    "workflow": re.compile(r"\.github/workflows/[\w.-]+\.yml"),
    "commit": re.compile(r"`[0-9a-f]{8}`"),
    "bead": re.compile(r"`(?:fln|franken_lean)-[\w-]+`"),
}

# The heading whose section is a catalogue of past defects rather than a set of live claims.
META_HEADING = "The recurring defect: evidence must be produced where the claim is made"

# The disclosure line AGENTS.md must carry, so the census is stated where the claim is made.
DISCLOSURE = re.compile(
    r"enforcement-census:\s*live=(\d+)\s+bound=(\d+)\s+unbound=(\d+)\s+catalogued=(\d+)"
)


class CensusError(RuntimeError):
    """A scan that cannot establish its own scope. Never reported as a clean tree."""


def meta_span(text):
    """Line range [start, end) of the catalogue region, 1-based and end-exclusive.

    Raises rather than returning None. A scan that cannot find the region it is required to
    exclude has not found a clean file -- it has lost its scope, and the difference is six
    catalogue rows that look exactly like live claims.
    """
    lines = text.splitlines()
    start = None
    for index, line in enumerate(lines, 1):
        if META_HEADING in line:
            if start is not None:
                raise CensusError(
                    f"the catalogue heading appears twice (lines {start} and {index}); "
                    "the region to exclude is ambiguous"
                )
            start = index
    if start is None:
        raise CensusError(
            "cannot find the catalogue heading in AGENTS.md:\n"
            f"  {META_HEADING!r}\n"
            "Its section is a list of PAST defects whose rows quote every phrase this scan "
            "searches for. Without the region this census silently counts them as live claims, "
            "which is how the number drifted 26 -> 27 -> 28 while the live population never "
            "moved. If the heading was reworded, update META_HEADING -- do not delete this check."
        )
    for index in range(start, len(lines)):
        if lines[index].startswith("## ") or lines[index].rstrip() == "---":
            return start, index + 1
    return start, len(lines) + 1


def sentences(text):
    """Yield (line_number, sentence). Table rows split on `|` so one row's several claims are
    not merged into a single giant pseudo-sentence."""
    for lineno, line in enumerate(text.splitlines(), 1):
        stripped = line.strip()
        if not stripped or stripped.startswith(("```", "#", ">")):
            continue
        chunks = stripped.split("|") if stripped.startswith("|") else [stripped]
        for chunk in chunks:
            for part in re.split(r"(?<=[.!?])\s+(?=[A-Z*`])", chunk):
                part = part.strip()
                if len(part) > 25:
                    yield lineno, part


def producers_in(sentence):
    return sorted({name for name, pat in PRODUCER.items() if pat.search(sentence)})


def census(text):
    start, end = meta_span(text)
    live, catalogued = [], []
    for lineno, sentence in sentences(text):
        match = ENFORCE.search(sentence)
        if not match:
            continue
        claim = {
            "line": lineno,
            "verb": match.group(1).lower(),
            "producers": producers_in(sentence),
            "sentence": sentence[:180],
        }
        (catalogued if start <= lineno < end else live).append(claim)

    # Anti-vacuity. A scan returning nothing is a BROKEN SCAN, never a clean file, and a
    # catalogue region that excluded nothing means the span is wrong even though it was found.
    if not live:
        raise CensusError(
            "derived ZERO live enforcement claims from AGENTS.md. That file is the densest "
            "source of them in the repository, so an empty result is a broken scan and is "
            "refused rather than reported as a clean tree."
        )
    if not catalogued:
        raise CensusError(
            f"the catalogue region (lines {start}..{end}) excluded NOTHING. The heading was "
            "found but the span is wrong, which leaves the rows it exists to exclude counted "
            "as live claims."
        )
    return {
        "live": len(live),
        "bound": sum(1 for c in live if c["producers"]),
        "unbound": sum(1 for c in live if not c["producers"]),
        "catalogued": len(catalogued),
        "meta_span": [start, end],
        "claims": live,
        "catalogued_claims": catalogued,
    }


def disclosed(text):
    """The census AGENTS.md states about itself, or None."""
    found = DISCLOSURE.findall(text)
    if len(found) > 1:
        raise CensusError(
            f"AGENTS.md carries {len(found)} enforcement-census disclosures; exactly one is "
            "required, or a repair can fix one copy and leave the other making the old claim"
        )
    if not found:
        return None
    live, bound, unbound, catalogued = (int(v) for v in found[0])
    return {"live": live, "bound": bound, "unbound": unbound, "catalogued": catalogued}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--agents", default="AGENTS.md", type=Path)
    parser.add_argument("--json", action="store_true")
    parser.add_argument(
        "--check",
        action="store_true",
        help="compare the derived census against AGENTS.md's own disclosure and exit 1 on any "
        "disagreement, in either direction",
    )
    args = parser.parse_args()

    try:
        text = args.agents.read_text()
        result = census(text)
        stated = disclosed(text)
    except (CensusError, OSError) as err:
        print(f"enforcement-census: {err}", file=sys.stderr)
        return 2

    if args.json:
        print(json.dumps(result, indent=1))
        return 0

    if args.check:
        if stated is None:
            print(
                "enforcement-census: AGENTS.md states no enforcement-census disclosure. "
                "Add a line reading:\n"
                f"  enforcement-census: live={result['live']} bound={result['bound']} "
                f"unbound={result['unbound']} catalogued={result['catalogued']}\n"
                "The census belongs in the file it describes; a number that lives only in a "
                "bead comment or a handoff dies at the next rotation.",
                file=sys.stderr,
            )
            return 1
        keys = ("live", "bound", "unbound", "catalogued")
        differ = {k: (stated[k], result[k]) for k in keys if stated[k] != result[k]}
        if differ:
            detail = ", ".join(f"{k}: stated {s}, derived {d}" for k, (s, d) in differ.items())
            print(
                f"enforcement-census: AGENTS.md's disclosure disagrees with the derivation "
                f"({detail}).\n"
                "Equality is required in BOTH directions: a new unbound claim must raise the "
                "number and its author must say so, and a repaired one must lower it. Do NOT "
                "soften enforcement sentences to make this pass -- that is pfei R5, the cheapest "
                "way to go green and the one that destroys the file's usefulness.",
                file=sys.stderr,
            )
            return 1
        print(
            f"enforcement-census: OK  live={result['live']} bound={result['bound']} "
            f"unbound={result['unbound']} catalogued={result['catalogued']} "
            f"(catalogue lines {result['meta_span'][0]}..{result['meta_span'][1]})"
        )
        return 0

    print(f"AGENTS.md: {len(text.splitlines())} lines")
    print(f"LIVE ENFORCEMENT CLAIMS: {result['live']}")
    print(f"  with a named producer:  {result['bound']}")
    print(f"  with NO named producer: {result['unbound']}")
    print(f"CATALOGUED (item 7, excluded): {result['catalogued']}")
    print()
    print("=== UNBOUND (no producer named in the same sentence) ===")
    for claim in result["claims"]:
        if not claim["producers"]:
            print(f"  L{claim['line']:<5} [{claim['verb']}] {claim['sentence'][:140]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
