#!/usr/bin/env python3
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

  1. The body never transits a shell word. It is read from a FILE and handed to `br` through an
     argv LIST, so no expansion of any kind is possible -- not backticks, not `$(...)`, not
     `$VAR`, not history expansion.
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
    br_comment.py verify <issue-id> <body-file> [--db PATH] [--comment-id N]

`verify` exists so the refusal can be demonstrated against a comment written by the corrupting
path, which `write` by construction cannot produce.

Exit codes: 0 stored bytes match the intended bytes; 1 they do not, or the record could not be
read. A refusal names what differs rather than only that something does.
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path

# `br` strips a trailing newline from a comment body, which is a property of the tool and not
# of the text, so the comparison is over the body with trailing newlines removed from BOTH
# sides. Nothing else is normalised: interior whitespace, backticks and dollar signs are
# compared byte for byte, because those are exactly what the defect destroys.
def normalise(text: str) -> str:
    return text.rstrip("\n")


def br(args, db=None):
    cmd = ["br", "--no-auto-flush"]
    if db:
        cmd += ["--db", db]
    cmd += args
    # An argv LIST, never a shell string. This is mechanism 1 and it is the whole reason the
    # body cannot be expanded on its way to `br`.
    return subprocess.run(cmd, capture_output=True, text=True)


def stored_comments(issue, db):
    result = br(["show", issue, "--json"], db)
    if result.returncode != 0:
        sys.exit(f"br_comment: cannot read {issue} back ({result.stderr.strip()[:200]}) — a "
                 f"write whose result cannot be read is refused, never reported as written")
    try:
        record = json.loads(result.stdout)
    except json.JSONDecodeError as error:
        sys.exit(f"br_comment: {issue}'s record did not parse ({error}) — refusing")
    if isinstance(record, list):
        record = record[0]
    return record.get("comments") or []


def body_of(comment):
    for key in ("text", "body", "content"):
        if key in comment and isinstance(comment[key], str):
            return comment[key]
    return ""


def compare(intended, stored, issue, comment_id):
    if normalise(stored) == normalise(intended):
        print(f"br_comment: OK — {issue} comment {comment_id} is BYTE-IDENTICAL to the intended "
              f"body ({len(normalise(intended))} chars, {intended.count(chr(96))} backticks, "
              f"{intended.count('$')} dollar signs, all preserved).")
        return 0
    print(f"br_comment: REFUSED — {issue} comment {comment_id} does NOT match the intended body.")
    print(f"  intended {len(normalise(intended))} chars, {intended.count(chr(96))} backticks, "
          f"{intended.count('$')} dollar signs")
    print(f"  stored   {len(normalise(stored))} chars, {stored.count(chr(96))} backticks, "
          f"{stored.count('$')} dollar signs")
    a, b = normalise(intended), normalise(stored)
    at = next((i for i in range(min(len(a), len(b))) if a[i] != b[i]), min(len(a), len(b)))
    print(f"  first difference at char {at}:")
    print(f"    intended …{a[max(0, at - 40):at + 40]!r}…")
    print(f"    stored   …{b[max(0, at - 40):at + 40]!r}…")
    print("  A bead comment is IMMUTABLE: this cannot be repaired, only annotated. If this fired "
          "on a real write, the body reached `br` through a shell word — pass it with -f.")
    return 1


def main():
    parser = argparse.ArgumentParser(add_help=True)
    parser.add_argument("mode", choices=["write", "verify"])
    parser.add_argument("issue")
    parser.add_argument("body_file")
    parser.add_argument("--db")
    parser.add_argument("--author")
    parser.add_argument("--comment-id", type=int)
    args = parser.parse_args()

    path = Path(args.body_file)
    if not path.is_file():
        sys.exit(f"br_comment: {path} is not a file — the body is read from a file so that it "
                 f"never becomes a shell word; there is no inline form on purpose")
    intended = path.read_text(encoding="utf-8")
    if not normalise(intended):
        sys.exit("br_comment: the body is empty — refusing rather than writing a blank record")

    before = {c.get("id") for c in stored_comments(args.issue, args.db)}

    if args.mode == "write":
        call = ["comments", "add", args.issue, "-f", str(path)]
        if args.author:
            call += ["--author", args.author]
        result = br(call, args.db)
        if result.returncode != 0:
            sys.exit(f"br_comment: br refused the write ({result.stderr.strip()[:200]})")

    comments = stored_comments(args.issue, args.db)
    if args.comment_id is not None:
        target = next((c for c in comments if c.get("id") == args.comment_id), None)
        if target is None:
            sys.exit(f"br_comment: {args.issue} carries no comment {args.comment_id}")
    else:
        fresh = [c for c in comments if c.get("id") not in before]
        if args.mode == "write" and len(fresh) != 1:
            sys.exit(f"br_comment: expected exactly one new comment, found {len(fresh)} — "
                     f"refusing rather than guessing which one to verify")
        target = fresh[0] if fresh else (comments[-1] if comments else None)
        if target is None:
            sys.exit(f"br_comment: {args.issue} carries no comments to verify")

    return compare(intended, body_of(target), args.issue, target.get("id"))


if __name__ == "__main__":
    sys.exit(main())
