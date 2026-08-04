#!/usr/bin/env -S python3 -I -S
"""Announce the coverage-row obligation AT THE MOMENT br create/br close creates it.

Bead `franken_lean-xjjr`. The obligation is created by `br create` and `br close`
and reported by a git pre-commit hook an unbounded number of actions later, to
whoever commits next -- who may be a third pane that created no obligation at
all. The enforcement is sound and late, and lateness has three costs a
correctness argument does not see: the committer is not always the ower, the
diagnosis lands on someone with no context, and one pane's unmet obligation
blocks every other pane's unrelated commit through the shared JSONL.

WHY THIS IS A WRAPPER AND NOT A HOOK. Measured at br 0.2.19: `br --help` (67
lines) contains hook 0, plugin 0, callback 0, notify 0, post-command 0; `br
config list` declares NINE options, all identity, with no command-lifecycle key.
There is no point inside br where this can be emitted, and beads_rust is outside
this repository. A wrapper is the only available position, and it is precedented
here -- `scripts/br_comment.py` already wraps br for a different br defect.

WHY THIS IS NOT A SECOND COPY OF THE PREDICATE, which the bead forbids outright
and rightly: a duplicate is free to drift from the guard and would certify a
stale answer as fresh. This script decides NOTHING. It runs the same producer the
pre-commit hook runs --

    python3 -I -S scripts/evidence.py validate-verification-manifest
        --manifest ci/VERIFICATION_MANIFEST.jsonl --beads .beads/issues.jsonl

-- and repeats what that producer says. A second CALL SITE of one producer is not
a second copy of a predicate. The hook remains the enforcement point and is not
weakened; this only moves the ANNOUNCEMENT earlier.

USAGE
    scripts/br_obligation.py create --title "..." --type task --priority 1
    scripts/br_obligation.py close  <id> --reason "..."
    scripts/br_obligation.py --self-test

Every argument after the subcommand is forwarded to `br` through an argv list, so
no shell expansion is possible -- the same hazard `br_comment.py` exists for.

WHAT THIS DOES NOT DO. It does not block: br has already acted by the time the
validator runs, and refusing afterwards would leave the tracker and the message
disagreeing. It reports. It also cannot see an obligation created by a bare `br`
invocation that bypasses this wrapper, which is a real limit and the reason this
is an ergonomic repair rather than an enforcement one.
"""

import json
import subprocess
import sys
from pathlib import Path

VALIDATOR = "scripts/evidence.py"
MANIFEST = "ci/VERIFICATION_MANIFEST.jsonl"
TRACKER = ".beads/issues.jsonl"

# The producer's own words when an obligation is outstanding. Keyed on the
# validator's message rather than re-derived, so this script cannot disagree
# with it about WHAT the obligation is -- only about when it is said.
OBLIGATION_NEEDLES = (
    "crossed the adoption boundary without coverage rows",
    "must not be empty",
    "closure",
)


def repo_root(start: Path) -> Path:
    for candidate in [start, *start.parents]:
        if (candidate / TRACKER).exists() and (candidate / VALIDATOR).exists():
            return candidate
    raise SystemExit(
        "br_obligation: not inside a franken_lean checkout "
        f"(no {TRACKER} + {VALIDATOR} above {start})"
    )


def tracker_state(root: Path) -> dict[str, str]:
    """id -> status, or {} when the export is unreadable.

    Deliberately tolerant: this is used only to say WHICH bead the obligation is
    probably about. It is never used to decide whether one exists.
    """
    path = root / TRACKER
    try:
        text = path.read_text(encoding="utf-8")
    except OSError:
        return {}
    state: dict[str, str] = {}
    for line in text.splitlines():
        if not line.strip():
            continue
        try:
            record = json.loads(line)
        except json.JSONDecodeError:
            continue
        identifier = record.get("id")
        if isinstance(identifier, str):
            state[identifier] = str(record.get("status"))
    return state


def run_validator(root: Path) -> tuple[int, str]:
    """The SAME invocation scripts/git-hooks/pre-commit makes."""
    completed = subprocess.run(
        [
            sys.executable,
            "-I",
            "-S",
            str(root / VALIDATOR),
            "validate-verification-manifest",
            "--manifest",
            str(root / MANIFEST),
            "--beads",
            str(root / TRACKER),
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    return completed.returncode, (completed.stdout + completed.stderr).strip()


def obligation_report(
    status: int, output: str, changed: list[str]
) -> str | None:
    """Format the announcement, or None when the producer reported none.

    Pure so it can be self-tested without running br: the classification is the
    part worth testing, and it must not invent an obligation the validator did
    not report.
    """
    if status == 0:
        return None
    if not any(needle in output for needle in OBLIGATION_NEEDLES):
        # The validator refused for some other reason. Say so plainly rather
        # than mislabelling it a coverage obligation.
        return (
            "br_obligation: the verification validator refused for a reason that "
            "is NOT a coverage-row obligation. Reporting it verbatim rather than "
            f"classifying it:\n{output}"
        )
    lines = [
        "br_obligation: THIS ACT CREATED A COVERAGE-ROW OBLIGATION, and the "
        "pre-commit hook will refuse the next commit until it is met.",
        "",
        "The verification validator says:",
        output,
        "",
        "Filing owes a SPARSE row (every evidence array empty, notes carrying the "
        "measurement). Closing owes a COMPLETE row citing a bead comment created "
        "at or after the bead's closed_at.",
    ]
    if changed:
        lines += ["", "Beads this invocation moved: " + ", ".join(changed)]
    lines += [
        "",
        "Check it yourself with the same producer the hook uses:",
        f"  python3 -I -S {VALIDATOR} validate-verification-manifest \\",
        f"    --manifest {MANIFEST} --beads {TRACKER}",
    ]
    return "\n".join(lines)


def self_test() -> int:
    failures: list[str] = []

    # A clean validator run announces nothing.
    if obligation_report(0, "", []) is not None:
        failures.append("a passing validator must announce no obligation")

    # A real adoption-boundary refusal is announced AND names the bead.
    refusal = (
        "beads crossed the adoption boundary without coverage rows: "
        "['franken_lean-example']"
    )
    report = obligation_report(1, refusal, ["franken_lean-example"])
    if report is None:
        failures.append("an adoption-boundary refusal must be announced")
    else:
        if refusal not in report:
            failures.append("the validator's own words must be repeated verbatim")
        if "franken_lean-example" not in report:
            failures.append("the moved bead must be named")

    # ANTI-VACUITY: an unrelated refusal must NOT be dressed up as a coverage
    # obligation. Without this cell the classifier could return the same banner
    # for everything and both cells above would still pass.
    unrelated = "verification-manifest: rows must be coverage-then-scenario canonical order"
    other = obligation_report(1, unrelated, [])
    if other is None:
        failures.append("a non-obligation refusal must still be reported")
    elif "THIS ACT CREATED A COVERAGE-ROW OBLIGATION" in other:
        failures.append(
            "a non-obligation refusal was mislabelled as a coverage obligation"
        )
    elif unrelated not in other:
        failures.append("a non-obligation refusal must be reported verbatim")

    # The producer must be the hook's, not a reimplementation.
    source = Path(__file__).read_text(encoding="utf-8")
    if "validate-verification-manifest" not in source:
        failures.append("this script must invoke the real validator")
    # The needles are ASSEMBLED, so this scanner's own body does not contain
    # them. The first version wrote them as literals and failed against itself:
    # a source-reading guard whose needle appears in its own text is the
    # self-exclusion trap AGENTS.md records, and it is only visible because the
    # cell was run rather than assumed.
    for tail in ("adoption_boundary", "derive_lifecycle"):
        forbidden = "def " + "_" + tail
        if forbidden in source:
            failures.append(
                f"this script must not reimplement the predicate: {forbidden}"
            )

    if failures:
        for failure in failures:
            print(f"br_obligation self-test FAILED: {failure}", file=sys.stderr)
        return 1
    print("br_obligation self-test: PASS (4 cases)")
    return 0


def main(argv: list[str]) -> int:
    if not argv:
        print(__doc__, file=sys.stderr)
        return 2
    if argv[0] == "--self-test":
        return self_test()

    root = repo_root(Path.cwd().resolve())
    before = tracker_state(root)

    completed = subprocess.run(["br", *argv], check=False)

    after = tracker_state(root)
    changed = sorted(
        identifier
        for identifier in set(after) | set(before)
        if before.get(identifier) != after.get(identifier)
    )

    status, output = run_validator(root)
    report = obligation_report(status, output, changed)
    if report is not None:
        print("", file=sys.stderr)
        print(report, file=sys.stderr)

    # br's own exit status is what the caller asked for; the announcement is
    # advisory and must not change it.
    return completed.returncode


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
