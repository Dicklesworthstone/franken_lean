#!/usr/bin/env -S python3 -I -S
"""Write a bead comment so it CANNOT be corrupted, and refuse the write if it was.

Bead `fln-qpkj`. A comment body passed as an inline shell word is expanded before `br` ever
sees it: a markdown backtick pair becomes a COMMAND SUBSTITUTION, the shell runs the enclosed
word and splices its output in, and `br` stores whatever arrives. The write reports success and
the durable record is already damaged. Bead comments are immutable, so the damage cannot be
repaired -- only annotated.

WHY THIS IS A WRITE-PATH TOOL AND NOT A SCANNER. Post-hoc detection was measured and is
unavailable: over 407 beads and 1502 stored comments, the two signatures with real recall are
saturated by this project's own house style -- `empty_parens` (169) by Rust call syntax quoted
in comments, `double_space_midline` (162) by column-aligned tables inside comments. 19.4% of
comments carry a signature and that figure is not a damage count. The corpus is adversarial to
its own detector *because the practice is good*. Refusing a corrupting write at the moment it is
made has no such problem.

TWO MECHANISMS, and the second is what makes this a guard rather than a convention:

  1. The body never transits a shell word. It is read exactly once from a FILE as UTF-8 and handed
     to `br` through an argv LIST, so no expansion of any kind is possible -- not backticks, not
     `$(...)`, not `$VAR`, not history expansion. Reading once also prevents a path mutation
     between deciding what was intended and asking `br` to open the file.
  2. The stored record is read BACK and compared to the intended bytes, and a mismatch REFUSES.
     That is exact rather than heuristic and cannot be saturated. It is also the only check that
     survives a future change in how `br` stores text, because it compares what landed against
     what was meant rather than reasoning about the path between them.

Mechanism 1 alone would be a convention; a convention cannot tell you it was followed. The
acceptance criteria of `fln-qpkj` ask for exactly this pairing, and require it to be shown both
ways: it must ACCEPT a legitimate body containing backticks (or it is a blanket refusal of
markdown) and it must REFUSE a body that arrived damaged.

Usage:
    br_comment.py write  <issue-id> <body-file> [--db PATH] [--author NAME]
    br_comment.py description <issue-id> <body-file> [--db PATH]
    br_comment.py verify <issue-id> <body-file> [--db PATH] [--comment-id N]
    br_comment.py self-test

`verify` exists so the refusal can be demonstrated against a comment written by the corrupting
path, which `write` by construction cannot produce.

Exit codes: 0 stored bytes match the intended bytes; 1 they do not, or the record could not be
read. A refusal names what differs rather than only that something does.
"""

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

BR_TIMEOUT_SECONDS = 30


class Refusal(RuntimeError):
    """A fail-closed guard outcome that should be rendered without a traceback."""


class Inconclusive(Refusal):
    """An outcome the guard cannot classify as either written or not written."""


def diagnostic(result):
    # `br --json` reports typed failures on stdout. Prefer that over incidental diagnostics on
    # stderr, and suppress the database engine's INFO telemetry in the child below.
    if result.stdout.strip():
        try:
            payload = json.loads(result.stdout)
        except json.JSONDecodeError:
            pass
        else:
            error = payload.get("error") if isinstance(payload, dict) else None
            if isinstance(error, dict):
                code = error.get("code")
                message = error.get("message")
                hint = error.get("hint")
                if isinstance(code, str) and isinstance(message, str):
                    suffix = f"; {hint}" if isinstance(hint, str) else ""
                    return f"{code}: {message}{suffix}"
    detail = result.stdout.strip() or result.stderr.strip()
    compact = " ".join(detail.split())
    return compact[:200] if compact else f"exit {result.returncode} with no diagnostic"


def br(args, db=None):
    cmd = ["br", "--no-auto-flush"]
    if db:
        cmd += ["--db", db]
    cmd += args
    env = os.environ.copy()
    env["RUST_LOG"] = "error"
    # An argv LIST, never a shell string. This is mechanism 1 and it is the whole reason the
    # body cannot be expanded on its way to `br`.
    try:
        return subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            encoding="utf-8",
            check=False,
            env=env,
            timeout=BR_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired as error:
        if args[:2] == ["comments", "add"] or args[:1] == ["update"]:
            raise Inconclusive(
                f"br did not finish within {BR_TIMEOUT_SECONDS}s; the write may already have "
                "landed. Inspect the issue before retrying"
            ) from error
        raise Inconclusive(
            f"br did not finish within {BR_TIMEOUT_SECONDS}s; no read-back verdict is available"
        ) from error
    except (OSError, UnicodeError) as error:
        raise Refusal(f"could not run br ({error})") from error


def parse_json(payload, context):
    try:
        return json.loads(payload)
    except json.JSONDecodeError as error:
        raise Refusal(f"{context} did not parse as JSON ({error})") from error


def body_of(comment, context):
    if not isinstance(comment, dict):
        raise Refusal(f"{context} is not a JSON object")
    for key in ("text", "body", "content"):
        if key in comment:
            body = comment[key]
            if isinstance(body, str):
                return body
            raise Refusal(f"{context}'s {key} field is not text")
    raise Refusal(f"{context} carries no text field")


def id_of(comment, context):
    if not isinstance(comment, dict):
        raise Refusal(f"{context} is not a JSON object")
    comment_id = comment.get("id")
    if (
        not isinstance(comment_id, int)
        or isinstance(comment_id, bool)
        or comment_id <= 0
    ):
        raise Refusal(f"{context} carries an invalid comment id")
    return comment_id


def validate_comment(comment, issue, context):
    id_of(comment, context)
    body_of(comment, context)
    if comment.get("issue_id") != issue:
        raise Refusal(f"{context} belongs to {comment.get('issue_id')!r}, not {issue!r}")
    return comment


def issue_from_record(payload, issue):
    record = parse_json(payload, f"{issue}'s record")
    if isinstance(record, list):
        if len(record) != 1:
            raise Refusal(
                f"{issue}'s record returned {len(record)} issue objects; expected exactly one"
            )
        record = record[0]
    if not isinstance(record, dict):
        raise Refusal(f"{issue}'s record is not a JSON object")
    if record.get("id") != issue:
        raise Refusal(f"read-back returned issue {record.get('id')!r}, not {issue!r}")
    return record


def comments_in_record(record, issue):
    comments = record.get("comments")
    if comments is None:
        return []
    if not isinstance(comments, list):
        raise Refusal(f"{issue}'s comments field is not a list")

    seen = set()
    for index, comment in enumerate(comments):
        context = f"{issue} comment at index {index}"
        validate_comment(comment, issue, context)
        comment_id = id_of(comment, context)
        if comment_id in seen:
            raise Refusal(f"{issue}'s record repeats comment id {comment_id}")
        seen.add(comment_id)
    return comments


def comments_from_record(payload, issue):
    return comments_in_record(issue_from_record(payload, issue), issue)


def stored_issue(issue, db, run_br=br):
    result = run_br(["show", issue, "--json"], db)
    if result.returncode != 0:
        raise Refusal(
            f"cannot read {issue} back ({diagnostic(result)}) — a write whose result "
            "cannot be read is refused, never reported as written"
        )
    return issue_from_record(result.stdout, issue)


def stored_comments(issue, db, run_br=br):
    return comments_in_record(stored_issue(issue, db, run_br), issue)


def created_comment(result, issue):
    if result.returncode != 0:
        raise Refusal(f"br refused the write ({diagnostic(result)})")
    comment = parse_json(result.stdout, f"{issue}'s write response")
    if isinstance(comment, list):
        if len(comment) != 1:
            raise Refusal(
                f"{issue}'s write response returned {len(comment)} comments; expected one"
            )
        comment = comment[0]
    return validate_comment(comment, issue, f"{issue}'s write response")


def write_and_read_back(issue, intended, db, author, run_br=br):
    # Passing `-m` from a shell is the defect this tool prevents. Here it is safe: `intended` is
    # an element of a subprocess argv list and never reaches a shell. It also means the bytes read
    # above are the bytes submitted, even if another process mutates the source path meanwhile.
    call = ["comments", "add", issue, "-m", intended]
    if author:
        call += ["--author", author]
    call += ["--json"]
    written = created_comment(run_br(call, db), issue)
    written_id = id_of(written, f"{issue}'s write response")

    # `--json` names the exact immutable record created by this process. A before/after set
    # difference is racy: a peer comment arriving in the same interval makes the result ambiguous
    # after our own comment has already landed and can induce a duplicate on retry.
    comments = stored_comments(issue, db, run_br)
    target = next(
        (comment for comment in comments if id_of(comment, f"{issue} comment") == written_id),
        None,
    )
    if target is None:
        raise Refusal(
            f"{issue}'s write response named comment {written_id}, but read-back did not contain it"
        )
    return target


def write_description_and_read_back(issue, intended, db, run_br=br):
    result = run_br(["update", issue, "--description", intended, "--json"], db)
    if result.returncode != 0:
        raise Refusal(f"br refused the description update ({diagnostic(result)})")
    response = parse_json(result.stdout, f"{issue}'s description-update response")
    if isinstance(response, list):
        if len(response) != 1:
            raise Refusal(
                f"{issue}'s description-update response returned {len(response)} issues; "
                "expected one"
            )
        response = response[0]
    response_id = response.get("id") if isinstance(response, dict) else None
    if response_id != issue:
        raise Refusal(
            f"description update returned issue {response_id!r}, not {issue!r}"
        )

    record = stored_issue(issue, db, run_br)
    stored = record.get("description")
    if not isinstance(stored, str):
        raise Refusal(f"{issue}'s read-back carries no text description")
    return stored


def select_comment(comments, issue, comment_id):
    if comment_id is not None:
        target = next(
            (
                comment
                for comment in comments
                if id_of(comment, f"{issue} comment") == comment_id
            ),
            None,
        )
        if target is None:
            raise Refusal(f"{issue} carries no comment {comment_id}")
        return target
    if not comments:
        raise Refusal(f"{issue} carries no comments to verify")
    return max(comments, key=lambda comment: id_of(comment, f"{issue} comment"))


def compare(intended, stored, issue, record_label, immutable):
    intended_bytes = intended.encode("utf-8")
    stored_bytes = stored.encode("utf-8")
    if stored_bytes == intended_bytes:
        print(f"br_comment: OK — {issue} {record_label} is BYTE-IDENTICAL to the intended "
              f"body ({len(intended_bytes)} bytes, {intended.count(chr(96))} backticks, "
              f"{intended.count('$')} dollar signs, all preserved).")
        return 0
    print(f"br_comment: REFUSED — {issue} {record_label} does NOT match the intended body.")
    print(f"  intended {len(intended_bytes)} bytes, {intended.count(chr(96))} backticks, "
          f"{intended.count('$')} dollar signs")
    print(f"  stored   {len(stored_bytes)} bytes, {stored.count(chr(96))} backticks, "
          f"{stored.count('$')} dollar signs")
    a, b = intended_bytes, stored_bytes
    at = next((i for i in range(min(len(a), len(b))) if a[i] != b[i]), min(len(a), len(b)))
    print(f"  first difference at UTF-8 byte {at}:")
    print(f"    intended …{a[max(0, at - 40):at + 40]!r}…")
    print(f"    stored   …{b[max(0, at - 40):at + 40]!r}…")
    if immutable:
        print("  A bead comment is IMMUTABLE: this cannot be repaired, only annotated. Do not "
              "retry blindly; the exact created comment already landed.")
    else:
        print("  The description is mutable, but this update did not remain byte-identical. "
              "Inspect current ownership and state before replacing it.")
    return 1


def read_body(path):
    try:
        raw = path.read_bytes()
    except OSError as error:
        raise Refusal(f"cannot read {path} ({error})") from error
    try:
        intended = raw.decode("utf-8")
    except UnicodeDecodeError as error:
        raise Refusal(f"{path} is not valid UTF-8 ({error})") from error
    if not intended.strip("\r\n"):
        raise Refusal("the body is empty — refusing rather than writing a blank record")
    if "\0" in intended:
        raise Refusal("the body contains a NUL byte, which cannot be represented in an argv entry")
    return intended


def self_test():
    issue = "fln-qpkj-self-test"
    intended = "The `canon` field and $(date) stay literal.\r\n\n"
    created = {
        "id": 41,
        "issue_id": issue,
        "author": "self-test",
        "text": intended,
    }
    concurrent = {
        "id": 42,
        "issue_id": issue,
        "author": "peer",
        "text": "peer comment that must not be selected",
    }
    calls = []

    def fake_br(args, db):
        calls.append((args, db))
        if args[:3] == ["comments", "add", issue]:
            return subprocess.CompletedProcess(args, 0, json.dumps(created), "")
        if args[:2] == ["update", issue]:
            return subprocess.CompletedProcess(args, 0, json.dumps([{"id": issue}]), "")
        if args == ["show", issue, "--json"]:
            record = [
                {
                    "id": issue,
                    "description": intended,
                    "comments": [created, concurrent],
                }
            ]
            return subprocess.CompletedProcess(args, 0, json.dumps(record), "")
        return subprocess.CompletedProcess(args, 2, "", "unexpected self-test command")

    target = write_and_read_back(issue, intended, "/scratch/beads.db", "self-test", fake_br)
    if id_of(target, "self-test target") != 41:
        raise Refusal("self-test selected a concurrent comment instead of the returned write id")
    expected_write = [
        "comments",
        "add",
        issue,
        "-m",
        intended,
        "--author",
        "self-test",
        "--json",
    ]
    if calls != [
        (expected_write, "/scratch/beads.db"),
        (["show", issue, "--json"], "/scratch/beads.db"),
    ]:
        raise Refusal(f"self-test observed an unexpected br call sequence: {calls!r}")
    if compare(intended, body_of(target, "self-test target"), issue, "comment 41", True) != 0:
        raise Refusal("self-test exact payload control refused")
    if compare(intended, intended[:-1], issue, "comment 41", True) != 1:
        raise Refusal("self-test accepted a missing trailing newline")
    description = write_description_and_read_back(
        issue, intended, "/scratch/beads.db", fake_br
    )
    if compare(intended, description, issue, "description", False) != 0:
        raise Refusal("self-test description payload control refused")
    expected_description = [
        "update",
        issue,
        "--description",
        intended,
        "--json",
    ]
    if calls[2:] != [
        (expected_description, "/scratch/beads.db"),
        (["show", issue, "--json"], "/scratch/beads.db"),
    ]:
        raise Refusal(f"self-test observed an unexpected description call sequence: {calls!r}")
    try:
        comments_from_record("[]", issue)
    except Refusal:
        pass
    else:
        raise Refusal("self-test accepted an empty issue-record response")
    failed = subprocess.CompletedProcess(
        [],
        3,
        json.dumps(
            {
                "error": {
                    "code": "ISSUE_NOT_FOUND",
                    "message": "Issue not found",
                    "hint": "inspect the id",
                }
            }
        ),
        "incidental stderr",
    )
    if diagnostic(failed) != "ISSUE_NOT_FOUND: Issue not found; inspect the id":
        raise Refusal("self-test lost br's typed failure diagnostic")

    print(
        "br_comment: SELF-TEST OK — exact-payload trailing-newline-drift "
        "returned-write-id description-payload malformed-schema typed-diagnostic"
    )
    return 0


def parser():
    parser = argparse.ArgumentParser(add_help=True)
    modes = parser.add_subparsers(dest="mode", required=True)

    write = modes.add_parser("write")
    write.add_argument("issue")
    write.add_argument("body_file")
    write.add_argument("--db")
    write.add_argument("--author")

    description = modes.add_parser("description")
    description.add_argument("issue")
    description.add_argument("body_file")
    description.add_argument("--db")

    verify = modes.add_parser("verify")
    verify.add_argument("issue")
    verify.add_argument("body_file")
    verify.add_argument("--db")
    verify.add_argument("--comment-id", type=int)

    modes.add_parser("self-test")
    return parser


def main():
    args = parser().parse_args()
    if args.mode == "self-test":
        return self_test()

    path = Path(args.body_file)
    if not path.is_file():
        raise Refusal(
            f"{path} is not a file — the body is read from a file so that it never becomes "
            "a shell word; there is no inline form on purpose"
        )
    intended = read_body(path)

    if args.mode == "description":
        stored = write_description_and_read_back(args.issue, intended, args.db)
        return compare(intended, stored, args.issue, "description", False)
    if args.mode == "write":
        target = write_and_read_back(args.issue, intended, args.db, args.author)
    else:
        comments = stored_comments(args.issue, args.db)
        target = select_comment(comments, args.issue, args.comment_id)
    context = f"{args.issue} comment"
    comment_id = id_of(target, context)
    return compare(
        intended,
        body_of(target, context),
        args.issue,
        f"comment {comment_id}",
        True,
    )


def entrypoint():
    try:
        return main()
    except Inconclusive as error:
        print(f"br_comment: INCONCLUSIVE — {error}", file=sys.stderr)
        return 1
    except Refusal as error:
        print(f"br_comment: REFUSED — {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(entrypoint())
