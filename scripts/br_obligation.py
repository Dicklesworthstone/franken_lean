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
import re
import subprocess
import sys
from collections.abc import Callable
from pathlib import Path

VALIDATOR = "scripts/evidence.py"
MANIFEST = "ci/VERIFICATION_MANIFEST.jsonl"
TRACKER = ".beads/issues.jsonl"
CONVERGENCE = "scripts/convergence_governance.py"
STATUS_VALIDATOR_TIMEOUT_SECONDS = 30
CONVERGENCE_TIMEOUT_SECONDS = 60

# The producer's own words when an obligation is outstanding. Keyed on the
# validator's message rather than re-derived, so this script cannot disagree
# with it about WHAT the obligation is -- only about when it is said.
OBLIGATION_NEEDLES = (
    "crossed the adoption boundary without coverage rows",
    "must not be empty",
    "closure",
)

# The R15 producer's own word for the same shape one registry over. Keyed on its
# message for the same reason as above: this script must not be able to disagree
# with the producer about WHAT is owed.
#
# **The filing obligation has FOUR parts and this announcer named three.** A bead,
# its regenerated ownership projection, its coverage row -- and, since R15, a
# convergence-registry row for any bead that reaches `in_progress`. The fourth was
# reported only by `cargo test`, which is the exact lateness `franken_lean-xjjr`
# exists to remove, and it reddened the tree three times in one day (`a0324ca4` is
# the third) before any author could act on it.
CONVERGENCE_NEEDLES = ("active-unclassified",)


def repo_root(start: Path) -> Path:
    for candidate in [start, *start.parents]:
        if (candidate / TRACKER).exists() and (candidate / VALIDATOR).exists():
            return candidate
    raise SystemExit(
        "br_obligation: not inside a franken_lean checkout "
        f"(no {TRACKER} + {VALIDATOR} above {start})"
    )


SUBJECT_LINE = re.compile(
    r"^\s*(?:[^\w\s]\s*)?(?:Created|Closed|Updated|Reopened)\s+([A-Za-z0-9][\w.\-]*)\s*:",
)


def acted_on(br_output: str) -> list[str]:
    """The bead ids `br` itself says it acted on.

    THE DIFF ALONE IS NOT THE ANSWER, and this is the defect franken_lean-xjjr
    is about arriving inside its own repair. `tracker_state` diffs the WHOLE
    shared tracker across the br invocation, and in a live swarm a peer's
    ordinary `br` command auto-flushes into that same file inside the window. So
    the diff reports beads the caller never touched: measured on 2026-08-05, one
    `create` of `franken_lean-gii.25` announced three beads, two of them other
    panes' (`fln-ehb5`, `franken_lean-ephemeral-manifest-artifact-povo`).

    `br` names its own subject on stdout, so it is recoverable exactly rather
    than inferred. Parsed permissively -- the leading glyph is optional, since a
    decorated tick is a presentation detail this must not depend on.
    """
    found = []
    for line in br_output.splitlines():
        match = SUBJECT_LINE.match(line)
        if match and match.group(1) not in found:
            found.append(match.group(1))
    return found


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


def run_convergence(root: Path) -> tuple[int, str]:
    """The SAME invocation the R15 lane and `convergence_governance.rs` make.

    Timed out rather than trusted to return: it reads the whole tracker and the whole
    manifest, and a producer that hangs must not wedge every `br` call in the swarm.
    """
    try:
        completed = subprocess.run(
            [
                sys.executable,
                "-I",
                "-S",
                str(root / CONVERGENCE),
                "--root",
                str(root),
                "--check",
            ],
            capture_output=True,
            text=True,
            check=False,
            timeout=CONVERGENCE_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired:
        return 2, (
            f"convergence-governance did not answer within "
            f"{CONVERGENCE_TIMEOUT_SECONDS}s"
        )
    except OSError as error:
        return 2, f"convergence-governance could not be run: {error}"
    return completed.returncode, (completed.stdout + completed.stderr).strip()


def convergence_report(
    status: int, output: str, changed: list[str]
) -> str | None:
    """Format the R15 announcement, or None when the producer reported none.

    Pure, and separate from `obligation_report`, because the two obligations are met
    in DIFFERENT FILES by different edits: a coverage row lands in the manifest, a
    registry row in the policy. One banner covering both would send an author to the
    wrong file, which is this repository's own recorded misdirection shape.
    """
    if status == 0:
        return None
    if not any(needle in output for needle in CONVERGENCE_NEEDLES):
        # Every other convergence refusal -- an expired adoption, an unknown gate, a
        # malformed policy -- is somebody else's, and announcing it as YOUR filing
        # obligation would be worse than silence. Reported verbatim, unclassified.
        return (
            "br_obligation: convergence governance refused for a reason that is NOT "
            "an unregistered-bead obligation. Reporting it verbatim rather than "
            f"classifying it:\n{output}"
        )
    lines = [
        (
            "br_obligation: THIS ACT CREATED AN R15 REGISTRY OBLIGATION, and "
            "`cargo test` will redden the tree for EVERY pane until it is met."
        ),
        "",
        "The convergence-governance producer says:",
        output,
        "",
        (
            "Every bead at `in_progress` needs one row in "
            "ci/CONVERGENCE_GOVERNANCE_POLICY.json, whose class is one of "
            "implementation, prerequisite, verification, incident, additive or "
            "adoption. Insert the row as TEXT beside its neighbours -- "
            "re-serializing the file reformats every other pane's rows."
        ),
    ]
    if changed:
        lines += ["", "Beads this invocation moved: " + ", ".join(changed)]
    lines += [
        "",
        "Check it yourself with the same producer the lane uses:",
        f"  python3 -I -S {CONVERGENCE} --root . --check",
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
    # Captured so `br`'s own report of its subject can be read, then re-emitted
    # VERBATIM so the caller sees exactly what bare `br` would have shown. A
    # wrapper that swallows or reformats its subject's output is a worse tool
    # than the announcement is worth.
    completed = invoke_br(["br", *argv], check=False, capture_output=True, text=True)
    if getattr(completed, "stdout", None):
        sys.stdout.write(completed.stdout)
    if getattr(completed, "stderr", None):
        sys.stderr.write(completed.stderr)

    after = tracker_state(root)
    changed = sorted(
        identifier
        for identifier in set(after) | set(before)
        if before.get(identifier) != after.get(identifier)
    )
    mine = [i for i in acted_on(getattr(completed, "stdout", "") or "") if i in changed]
    # A bead that moved in the window and is NOT this act's subject belongs to
    # another pane. It is NAMED rather than dropped: a peer's bead crossing the
    # adoption boundary inside your window is precisely what will refuse YOUR
    # next commit, and hiding it would trade one confusing diagnosis for another.
    theirs = [i for i in changed if i not in mine]

    if theirs:
        print(file=sys.stderr)
        print(
            "br_obligation: ATTRIBUTION -- this act moved "
            + (", ".join(mine) if mine else "no bead this wrapper could name")
            + ".",
            file=sys.stderr,
        )
        print(
            "br_obligation: the tracker ALSO changed for "
            + ", ".join(theirs)
            + " inside the same window. Those are another pane's, arriving by "
            "auto-flush into the shared export. You do not owe their rows -- but "
            "an unmet obligation of theirs WILL refuse your next commit.",
            file=sys.stderr,
        )

    status, output = run_validator(root)
    report = obligation_report(status, output, changed)
    if report is not None:
        print(file=sys.stderr)
        print(report, file=sys.stderr)

    # Announced independently of the coverage one, and after it, because an act can
    # owe BOTH: claiming a bead you just filed crosses the adoption boundary and
    # enters the convergence registry's active set in one motion. Suppressing the
    # second when the first fires would hide exactly the case that costs most.
    r15_status, r15_output = run_convergence(root)
    r15_report = convergence_report(r15_status, r15_output, changed)
    if r15_report is not None:
        print(file=sys.stderr)
        print(r15_report, file=sys.stderr)

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

    # --- the R15 registry obligation, the fourth part of a filing ------------
    if convergence_report(0, "", []) is not None:
        failures.append("a passing convergence run must announce no obligation")

    r15_refusal = "convergence-governance: inconclusive; reason=active-unclassified: fln-example"
    r15 = convergence_report(2, r15_refusal, ["fln-example"])
    if r15 is None:
        failures.append("an active-unclassified refusal must be announced")
    else:
        if r15_refusal not in r15:
            failures.append("the R15 producer's own words must be repeated verbatim")
        if "fln-example" not in r15:
            failures.append("the moved bead must be named in the R15 announcement")
        if "CONVERGENCE_GOVERNANCE_POLICY.json" not in r15:
            failures.append(
                "the R15 announcement must name the file the row goes in — the two "
                "obligations are met in different files"
            )

    # ANTI-VACUITY, and it is the cell that does the work: every OTHER convergence
    # refusal must NOT be dressed up as this author's filing obligation. Without it
    # the classifier could return one banner for everything and both cells above
    # would still pass — which is how the coverage half's own anti-vacuity cell was
    # justified, and the same trap is available here one registry over.
    r15_unrelated = (
        "convergence-governance: inconclusive; reason=adoption-expired: fln-other:2026-01-01"
    )
    r15_other = convergence_report(2, r15_unrelated, [])
    if r15_other is None:
        failures.append("a non-obligation convergence refusal must still be reported")
    elif "THIS ACT CREATED AN R15 REGISTRY OBLIGATION" in r15_other:
        failures.append(
            "a non-obligation convergence refusal was mislabelled as an R15 obligation"
        )
    elif r15_unrelated not in r15_other:
        failures.append("a non-obligation convergence refusal must be reported verbatim")

    # The two announcements must stay DISTINGUISHABLE. A single banner would send an
    # author to the wrong file, and nothing else in this self-test would notice.
    coverage_banner = obligation_report(
        1, "beads crossed the adoption boundary without coverage rows: ['x']", []
    )
    if coverage_banner is not None and r15 is not None:
        if coverage_banner.splitlines()[0] == r15.splitlines()[0]:
            failures.append("the coverage and R15 announcements must not share a banner")

    # The producer must be the hook's, not a reimplementation.
    source = Path(__file__).read_text(encoding="utf-8")
    if (
        "validate-verification-manifest" not in source
        or "validate-bead-status" not in source
    ):
        failures.append("this script must invoke the real validator")
    if "convergence_governance.py" not in source:
        failures.append("this script must invoke the real convergence producer")
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
        command: list[str], *, check: bool, capture_output: bool = False, text: bool = False
    ) -> subprocess.CompletedProcess[str]:
        invocations.append(command)
        return subprocess.CompletedProcess(command, 0, stdout="", stderr="")

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
        command: list[str], *, check: bool, capture_output: bool = False, text: bool = False
    ) -> subprocess.CompletedProcess[str]:
        admitted_invocations.append(command)
        return subprocess.CompletedProcess(command, 0, stdout="", stderr="")

    admitted_argv = ["update", "fixture", "--status", "open"]
    admitted_status = execute_br_command(root, admitted_argv, invoke_br=admitted_br)
    if admitted_status != 0:
        failures.append(f"an admitted status returned {admitted_status}, not zero")
    if admitted_invocations != [["br", *admitted_argv]]:
        failures.append(
            f"an admitted status did not invoke br exactly once: {admitted_invocations!r}"
        )

    # ATTRIBUTION (franken_lean-xjjr): `br`'s own subject line is parsed, so the
    # announcement can separate the bead THIS act moved from beads a peer's
    # concurrent auto-flush moved in the same window.
    for rendered, expected in (
        ("\u2713 Created franken_lean-gii.30: a title", ["franken_lean-gii.30"]),
        ("Updated fln-abc1: a title", ["fln-abc1"]),
        ("\u2713 Closed franken_lean-gii.29: reason here", ["franken_lean-gii.29"]),
        ("Reopened fln-x9: t", ["fln-x9"]),
    ):
        if acted_on(rendered) != expected:
            failures.append(
                f"the subject parser read {acted_on(rendered)!r} from {rendered!r}, "
                f"expected {expected!r}"
            )

    # NEGATIVE CONTROL: output naming no subject must yield nothing, or the
    # parser would attribute every act to whatever id happened to appear.
    for noise in (
        "Nothing to export (no dirty issues)",
        "  1486 labels",
        "franken_lean-gii.30 is mentioned but not acted on",
    ):
        if acted_on(noise):
            failures.append(f"the subject parser invented {acted_on(noise)!r} from {noise!r}")

    # And a multi-line report names each subject once, in order.
    multi = "\u2713 Created a-1: x\nnoise\n\u2713 Created a-1: x\nUpdated b-2: y"
    if acted_on(multi) != ["a-1", "b-2"]:
        failures.append(f"multi-subject parse read {acted_on(multi)!r}")

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
