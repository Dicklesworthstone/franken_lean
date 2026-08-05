#!/usr/bin/env -S python3 -I -S
"""Announce coverage obligations and refuse unsupported statuses at the creating act.

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
    scripts/br_obligation.py update <id> --status <status>
    scripts/br_obligation.py --self-test

Every argument after the subcommand is forwarded to `br` through an argv list, so
no shell expansion is possible -- the same hazard `br_comment.py` exists for.

WHAT THIS DOES AND DOES NOT BLOCK. Coverage-row obligations are still announced
after br acts: refusing then would leave the tracker and the message disagreeing.
An explicit --status is different because it can be checked before the act; an
unsupported or underivable value is refused before br runs. A bare `br` invocation
can bypass this wrapper, which is a real limit and why the committed-export guard
remains the backstop.
"""

import json
import subprocess
import sys
from collections.abc import Callable
from pathlib import Path

VALIDATOR = "scripts/evidence.py"
MANIFEST = "ci/VERIFICATION_MANIFEST.jsonl"
TRACKER = ".beads/issues.jsonl"
STATUS_VALIDATOR_TIMEOUT_SECONDS = 30

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
        (
            "br_obligation: THIS ACT CREATED A COVERAGE-ROW OBLIGATION, and the "
            "pre-commit hook will refuse the next commit until it is met."
        ),
        "",
        "The verification validator says:",
        output,
        "",
        (
            "Filing owes a SPARSE row (every evidence array empty, notes carrying the "
            "measurement). Closing owes a COMPLETE row citing a bead comment created "
            "at or after the bead's closed_at."
        ),
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


# --- franken_lean-shlw: an unmodelled status is an export-wide blocker --------
#
# Measured at br 0.2.19: `br update --status` accepts ARBITRARY text. `nonsense`
# and `zzzz-not-a-status` were both stored and exported verbatim. The verification
# validator accepts exactly four values, so ANY other string -- a deliberate
# `blocked`, or a typo -- refuses every pane's beads export until it is changed or
# pinned out, and the refusal lands on whoever commits next rather than on whoever
# set it.
#
# The lifecycle decision is criterion 2 of franken_lean-shlw: this wrapper refuses
# any value outside the validator's set BEFORE invoking br. That makes the pane
# setting the value see the refusal and leaves the shared tracker unchanged.
#
# The wrapper CALLS the validator's status-only entry point before br. It does not
# parse or transcribe the vocabulary. A validator fault is a refusal rather than a
# silent fallback: a stale local copy that still looked right is exactly how this
# check would stop checking.


def run_status_validator(
    root: Path,
    requested: str,
    *,
    invoke_validator: Callable[..., subprocess.CompletedProcess[str]] = subprocess.run,
) -> subprocess.CompletedProcess[str]:
    """Call the existing evidence validator for one prospective lifecycle value."""
    return invoke_validator(
        [
            sys.executable,
            "-I",
            "-S",
            str(root / VALIDATOR),
            "validate-bead-status",
            "--status",
            requested,
        ],
        capture_output=True,
        text=True,
        timeout=STATUS_VALIDATOR_TIMEOUT_SECONDS,
        check=False,
    )


def status_refusal(
    root: Path,
    requested: str | None,
    *,
    invoke_validator: Callable[..., subprocess.CompletedProcess[str]] = subprocess.run,
) -> str | None:
    """Explain a pre-action validator refusal, or None when br may run."""
    if requested is None:
        return None
    try:
        completed = run_status_validator(
            root,
            requested,
            invoke_validator=invoke_validator,
        )
    except subprocess.TimeoutExpired:
        return (
            "br_obligation: REFUSED BEFORE br: validate-bead-status timed out "
            f"after {STATUS_VALIDATOR_TIMEOUT_SECONDS}s while judging {requested!r}.\n"
            "The shared tracker is unchanged; a validator non-answer is never permission "
            "to invoke br. See franken_lean-shlw."
        )
    except OSError as error:
        return (
            "br_obligation: REFUSED BEFORE br: validate-bead-status could not run "
            f"while judging {requested!r} ({error}).\n"
            "The shared tracker is unchanged; a validator launch failure is never permission "
            "to invoke br. See franken_lean-shlw."
        )
    if completed.returncode == 0:
        return None
    detail = (completed.stdout + completed.stderr).strip()
    if not detail:
        detail = f"validator exited {completed.returncode} without a diagnostic"
    return (
        f"br_obligation: REFUSED BEFORE br: validate-bead-status rejected "
        f"{requested!r} (exit {completed.returncode}).\n"
        f"{detail}\n"
        "br accepts arbitrary text here (measured at 0.2.19), but this wrapper did "
        "not invoke br, so the shared tracker is unchanged and the refusal reaches "
        "the pane that requested the status. See franken_lean-shlw."
    )


def requested_statuses(argv: list[str]) -> list[str]:
    """Every explicit status value in a br argv, including attached spellings."""
    found: list[str] = []
    index = 0
    while index < len(argv):
        token = argv[index]
        if token == "--":
            break
        if token == "--status" or token == "-s":
            # Missing values are invalid too. Represent one as the empty string so
            # the validator refuses before br instead of silently skipping the check.
            found.append(argv[index + 1] if index + 1 < len(argv) else "")
            index += 2
            continue
        if token.startswith("--status="):
            found.append(token.split("=", 1)[1])
        elif token.startswith("-s") and len(token) > 2:
            found.append(token[2:].removeprefix("="))
        index += 1
    return found


def execute_br_command(
    root: Path,
    argv: list[str],
    *,
    invoke_br: Callable[..., subprocess.CompletedProcess[str]] = subprocess.run,
) -> int:
    """Run br only after an explicit status is admitted by the validator's set."""
    for requested in requested_statuses(argv):
        refusal = status_refusal(root, requested)
        if refusal is not None:
            print(refusal, file=sys.stderr)
            return 2

    before = tracker_state(root)
    completed = invoke_br(["br", *argv], check=False)

    after = tracker_state(root)
    changed = sorted(
        identifier
        for identifier in set(after) | set(before)
        if before.get(identifier) != after.get(identifier)
    )

    status, output = run_validator(root)
    report = obligation_report(status, output, changed)
    if report is not None:
        print(file=sys.stderr)
        print(report, file=sys.stderr)

    return completed.returncode


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
    if (
        "validate-verification-manifest" not in source
        or "validate-bead-status" not in source
    ):
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

    # --- franken_lean-shlw cells ---------------------------------------------
    root = repo_root(Path.cwd().resolve())
    if status_refusal(root, None) is not None:
        failures.append("no --status must be admitted")
    if status_refusal(root, "open") is not None:
        failures.append("a supported status must be admitted")

    refused = status_refusal(root, "blocked")
    if refused is None:
        failures.append("an unmodelled status must be refused")
    elif (
        "blocked" not in refused
        or "franken_lean-shlw" not in refused
        or "bead-status: unsupported status" not in refused
    ):
        failures.append("the refusal must carry the validator's status diagnosis")

    # A TYPO must refuse exactly as `blocked` does: the defect is not one word.
    if status_refusal(root, "in_progres") is None:
        failures.append("a typo must be refused too -- the defect is not one word")

    # ANTI-VACUITY: a validator fault must REFUSE, never silently pass.
    def broken_validator(
        command: list[str], **_kwargs: object
    ) -> subprocess.CompletedProcess[str]:
        return subprocess.CompletedProcess(command, 2, stdout="", stderr="validator fault")

    undecided = status_refusal(
        root,
        "blocked",
        invoke_validator=broken_validator,
    )
    if undecided is None or "validator fault" not in undecided:
        failures.append("a faulting validator must be reported, not assumed")

    def timed_out_validator(
        command: list[str], **_kwargs: object
    ) -> subprocess.CompletedProcess[str]:
        raise subprocess.TimeoutExpired(command, STATUS_VALIDATOR_TIMEOUT_SECONDS)

    timed_out = status_refusal(
        root,
        "blocked",
        invoke_validator=timed_out_validator,
    )
    if timed_out is None or "timed out" not in timed_out:
        failures.append("a timed-out validator must refuse before br with a diagnosis")

    for argv, expected in (
        (["update", "x", "--status", "blocked"], ["blocked"]),
        (["update", "x", "--status=blocked"], ["blocked"]),
        (["update", "x", "-s", "blocked"], ["blocked"]),
        (["update", "x", "-sblocked"], ["blocked"]),
        (
            ["update", "x", "--status", "open", "--status=blocked"],
            ["open", "blocked"],
        ),
        (["update", "--", "--status"], []),
        (["close", "x"], []),
    ):
        if requested_statuses(argv) != expected:
            failures.append(f"requested_statuses{argv} != {expected!r}")

    # The before-action property, not merely the wording: a refused status must
    # return nonzero without reaching the injected br runner.
    invocations: list[list[str]] = []

    def forbidden_br(
        command: list[str], *, check: bool
    ) -> subprocess.CompletedProcess[str]:
        invocations.append(command)
        return subprocess.CompletedProcess(command, 0)

    refusal_status = execute_br_command(
        root,
        ["update", "fixture", "--status", "blocked"],
        invoke_br=forbidden_br,
    )
    if refusal_status == 0:
        failures.append("a refused status must return nonzero")
    if invocations:
        failures.append(f"a refused status invoked br anyway: {invocations!r}")

    # GREEN CONTROL: the injected runner must remain reachable for a status the
    # real validator admits. Otherwise the negative cell could pass because this
    # wrapper had become a blanket refusal that never invokes br at all.
    admitted_invocations: list[list[str]] = []

    def admitted_br(
        command: list[str], *, check: bool
    ) -> subprocess.CompletedProcess[str]:
        admitted_invocations.append(command)
        return subprocess.CompletedProcess(command, 0)

    admitted_argv = ["update", "fixture", "--status", "open"]
    admitted_status = execute_br_command(root, admitted_argv, invoke_br=admitted_br)
    if admitted_status != 0:
        failures.append(f"an admitted status returned {admitted_status}, not zero")
    if admitted_invocations != [["br", *admitted_argv]]:
        failures.append(
            f"an admitted status did not invoke br exactly once: {admitted_invocations!r}"
        )

    if failures:
        for failure in failures:
            print(f"br_obligation self-test FAILED: {failure}", file=sys.stderr)
        return 1
    print("br_obligation self-test: PASS (obligation + status cells)")
    return 0


def main(argv: list[str]) -> int:
    if not argv:
        print(__doc__, file=sys.stderr)
        return 2
    if argv[0] == "--self-test":
        return self_test()

    root = repo_root(Path.cwd().resolve())
    return execute_br_command(root, argv)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
