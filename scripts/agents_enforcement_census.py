#!/usr/bin/env -S python3 -I -S
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
runs, or enforces what the sentence says. This file remains the sole sentence extractor; the
Rust gate consumes its `--referents` stream to resolve operational lane, workflow, and bead
referents, alongside the line- and test-citation bindings already there. Read `bound` as "has a
candidate referent", never as "is verified".

The `reviewed-unwalked` registry is a bijection over the still-unbound claims. It makes every
remainder explicit without pretending that prose reasons are executable proofs. The live floor
is intentionally independent of that registry: lowering the disclosure and deleting a row after
softening an enforcement sentence is pfei R5's cheapest hollow green, so a population below the
measured floor is a typed refusal.
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
    "source-file": re.compile(
        r"`(?:[\w./-]+\.(?:rs|py|sh|txt|jsonl|toml|md)|scripts/git-hooks/pre-commit)`"
    ),
    "lane": re.compile(r"scripts/(?:e2e|tribunal|extract)/[\w.]+\.sh"),
    "workflow": re.compile(r"\.github/workflows/[\w.-]+\.yml"),
    "bead": re.compile(r"`(?:fln|franken_lean)-[\w-]+`"),
}

# The heading whose section is a catalogue of past defects rather than a set of live claims.
META_HEADING = "The recurring defect: evidence must be produced where the claim is made"

REVIEWED_PREFIX = "> reviewed-unwalked "
REVIEWED_ID = re.compile(r"PFEI-U\d{2}")
REVIEWED_UNWALKED_CEILING = 16

# Measured at the R3/R5 landing point. This is intentionally a floor, not an exact count: new
# claims still flow through the disclosure and registry, while a wording-only population shrink
# is refused until this constant is deliberately revisited in code.
LIVE_CLAIM_FLOOR = 35

# The disclosure line AGENTS.md must carry, so the census is stated where the claim is made.
DISCLOSURE = re.compile(
    r"enforcement-census:\s*live=(\d+)\s+bound=(\d+)\s+unbound=(\d+)\s+catalogued=(\d+)"
    r"\s+reviewed=(\d+)"
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


def reviewed_rows(text):
    """Parse AGENTS.md's reviewed-unwalked registry without forgiving malformed rows."""
    rows, findings = [], []
    for lineno, raw in enumerate(text.splitlines(), 1):
        stripped = raw.strip()
        if not stripped.startswith("> reviewed-unwalked"):
            continue
        if not stripped.startswith(REVIEWED_PREFIX):
            findings.append(
                f"reviewed-unwalked row at line {lineno} is malformed; expected "
                f"`{REVIEWED_PREFIX}PFEI-Udd :: unique sentence needle :: reason`"
            )
            continue
        fields = [field.strip() for field in stripped[len(REVIEWED_PREFIX) :].split(" :: ")]
        if len(fields) != 3:
            findings.append(
                f"reviewed-unwalked row at line {lineno} has {len(fields)} fields; expected "
                "exactly id, unique sentence needle, and reason"
            )
            continue
        row_id, needle, reason = fields
        if not REVIEWED_ID.fullmatch(row_id):
            findings.append(
                f"reviewed-unwalked row at line {lineno} has malformed id {row_id!r}; "
                "expected PFEI-Udd"
            )
        if not needle:
            findings.append(f"reviewed-unwalked row {row_id!r} has an empty sentence needle")
        if not reason:
            findings.append(f"reviewed-unwalked row {row_id!r} has an empty reason")
        rows.append({"id": row_id, "needle": needle, "reason": reason, "line": lineno})

    ids = [row["id"] for row in rows]
    if ids != sorted(ids):
        findings.append(
            "reviewed-unwalked ids are not sorted; stable order is part of the review surface: "
            f"{ids!r}"
        )
    duplicates = sorted({row_id for row_id in ids if ids.count(row_id) > 1})
    if duplicates:
        findings.append(f"duplicate reviewed-unwalked ids: {duplicates!r}")
    for field in ("needle", "reason"):
        values = [row[field] for row in rows if row[field]]
        repeated = sorted({value for value in values if values.count(value) > 1})
        if repeated:
            findings.append(f"duplicate reviewed-unwalked {field}s: {repeated!r}")
    if len(rows) > REVIEWED_UNWALKED_CEILING:
        findings.append(
            f"reviewed-unwalked registry has {len(rows)} rows against ceiling "
            f"{REVIEWED_UNWALKED_CEILING}; growth must raise the code constant deliberately"
        )
    return rows, findings


def review_findings(result, rows, findings):
    """Require a one-to-one declaration of every live claim that still names no producer."""
    findings = list(findings)
    unbound = [claim for claim in result["claims"] if not claim["producers"]]
    for claim in unbound:
        matches = [row for row in rows if row["needle"] in claim["sentence"]]
        if len(matches) != 1:
            findings.append(
                f"unbound claim at line {claim['line']} matches {len(matches)} reviewed-unwalked "
                f"rows {[row['id'] for row in matches]!r}: {claim['sentence']!r}"
            )
    for row in rows:
        matches = [claim for claim in unbound if row["needle"] in claim["sentence"]]
        if len(matches) != 1:
            findings.append(
                f"reviewed-unwalked {row['id']} at line {row['line']} matches {len(matches)} "
                f"still-unbound claims at lines {[claim['line'] for claim in matches]!r}; "
                f"needle={row['needle']!r}"
            )
    return findings


def operational_referents(result):
    """Yield the live lane/workflow/bead referents for the Rust operational judge."""
    found = set()
    for claim in result["claims"]:
        for kind in ("lane", "workflow", "bead"):
            for match in PRODUCER[kind].finditer(claim["sentence"]):
                found.add((claim["line"], kind, match.group(0).strip("`")))
    return sorted(found)


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
            "sentence": sentence,
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
    if len(live) < LIVE_CLAIM_FLOOR:
        raise CensusError(
            f"anti-softening floor: derived {len(live)} live enforcement claims, below the "
            f"measured floor {LIVE_CLAIM_FLOOR}. Lowering the disclosure and deleting a "
            "reviewed-unwalked row cannot make an enforcement sentence disappear cleanly. If "
            "the population genuinely shrank because executable coverage replaced prose, amend "
            "LIVE_CLAIM_FLOOR in the same reviewed change and preserve the before/after evidence."
        )
    result = {
        "live": len(live),
        "bound": sum(1 for c in live if c["producers"]),
        "unbound": sum(1 for c in live if not c["producers"]),
        "catalogued": len(catalogued),
        "meta_span": [start, end],
        "claims": live,
        "catalogued_claims": catalogued,
    }
    rows, parse_findings = reviewed_rows(text)
    result["reviewed"] = len(rows)
    result["reviewed_rows"] = rows
    result["review_findings"] = review_findings(result, rows, parse_findings)
    return result


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
    live, bound, unbound, catalogued, reviewed = (int(v) for v in found[0])
    return {
        "live": live,
        "bound": bound,
        "unbound": unbound,
        "catalogued": catalogued,
        "reviewed": reviewed,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--agents", default="AGENTS.md", type=Path)
    parser.add_argument("--json", action="store_true")
    parser.add_argument(
        "--referents",
        action="store_true",
        help="emit live operational referents as line<TAB>kind<TAB>value for the Rust judge",
    )
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

    if args.referents:
        for line, kind, value in operational_referents(result):
            print(f"{line}\t{kind}\t{value}")
        return 0

    if args.json:
        print(json.dumps(result, indent=1))
        return 0

    if args.check:
        if stated is None:
            print(
                "enforcement-census: AGENTS.md states no enforcement-census disclosure. "
                "Add a line reading:\n"
                f"  enforcement-census: live={result['live']} bound={result['bound']} "
                f"unbound={result['unbound']} catalogued={result['catalogued']} "
                f"reviewed={result['reviewed']}\n"
                "The census belongs in the file it describes; a number that lives only in a "
                "bead comment or a handoff dies at the next rotation.",
                file=sys.stderr,
            )
            return 1
        keys = ("live", "bound", "unbound", "catalogued", "reviewed")
        differ = {k: (stated[k], result[k]) for k in keys if stated[k] != result[k]}
        problems = []
        if differ:
            detail = ", ".join(f"{k}: stated {s}, derived {d}" for k, (s, d) in differ.items())
            problems.append(
                f"AGENTS.md's disclosure disagrees with the derivation ({detail}). Equality is "
                "required in BOTH directions: a new unbound claim must raise the number and its "
                "author must say so, and a repaired one must lower it."
            )
        problems.extend(result["review_findings"])
        if problems:
            print("enforcement-census: check failed:", file=sys.stderr)
            for problem in problems:
                print(f"  - {problem}", file=sys.stderr)
            print(
                "Do NOT soften enforcement sentences to make this pass -- that is pfei R5, the "
                "cheapest way to go green and the one that destroys the file's usefulness.",
                file=sys.stderr,
            )
            return 1
        print(
            f"enforcement-census: OK  live={result['live']} bound={result['bound']} "
            f"unbound={result['unbound']} catalogued={result['catalogued']} "
            f"reviewed={result['reviewed']} "
            f"(catalogue lines {result['meta_span'][0]}..{result['meta_span'][1]})"
        )
        return 0

    print(f"AGENTS.md: {len(text.splitlines())} lines")
    print(f"LIVE ENFORCEMENT CLAIMS: {result['live']}")
    print(f"  with a named producer:  {result['bound']}")
    print(f"  with NO named producer: {result['unbound']}")
    print(f"CATALOGUED (item 7, excluded): {result['catalogued']}")
    print(f"REVIEWED-UNWALKED: {result['reviewed']}")
    if result["review_findings"]:
        print("REVIEW FINDINGS:")
        for finding in result["review_findings"]:
            print(f"  - {finding}")
    print()
    print("=== UNBOUND (no producer named in the same sentence) ===")
    for claim in result["claims"]:
        if not claim["producers"]:
            print(f"  L{claim['line']:<5} [{claim['verb']}] {claim['sentence'][:140]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
