#!/usr/bin/env python3
"""The pinned option census: mechanical extraction of every option registration in the
Reference source tree (bead franken_lean-4xsz; plan D5/D9, Appendix census method).

Extracts, from vendor/lean4-src/src:
  - `[modifiers] register_builtin_option <name> : <Type> := { ... }` blocks
    (modifiers measured in the pin: `public`; the shape allows any word/attribute
    prefix so a new visibility keyword cannot silently hide a site)
  - `[modifiers] register_option <name> : <Type> := { ... }` blocks
  - `registerTraceClass <name> [(inherited := ...)]` sites -> Bool option
    `trace.<name>`, defValue false (Lean/Util/Trace.lean:379-385)
  - known DYNAMIC registration wrappers (`registerSet` linter sets), emitted as
    explicit dynamic rows rather than resolved values

TOTALITY DISCIPLINE, in two layers, because the first alone was measured
insufficient: (1) a recognized site that fails to parse becomes a BLOCKING row with
its anchor — never a skip; (2) the recognizer itself is RECONCILED against a raw
substring scan with an ANCHORED exclusion list — every raw keyword hit must be a
recognized site, an in-comment mention, or a named exclusion, and anything else
refuses the whole extraction. The first version of this script recognized 256 of 262
builtin sites because six carry a `public` modifier, and its per-site totality check
passed while the census was a sampler.

Output: NDJSON, schema fln.option-census/1, sorted by (name, source). Lean string
gaps (a `\\` before the newline) in descr values are joined per the language rule.
--verify runs the extraction twice and refuses on any byte difference.
"""

import argparse
import io
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SRC_ROOT = os.path.join(REPO, "vendor", "lean4-src", "src")
SCHEMA = "fln.option-census/1"

MOD = r"(?:(?:@\[[^\]]*\]|public|private|protected|scoped)\s+)*"
BUILTIN_RE = re.compile(
    rf"^\s*{MOD}register_builtin_option\s+([A-Za-z0-9_.«»]+)\s*:\s*(.+?)\s*:=\s*\{{\s*$"
)
PLAIN_RE = re.compile(
    rf"^\s*{MOD}register_option\s+([A-Za-z0-9_.«»]+)\s*:\s*(.+?)\s*:=\s*\{{\s*$"
)
TRACE_RE = re.compile(r"registerTraceClass\s+`+([A-Za-z0-9_.«»]+)(.*)$")
DYNAMIC_WRAPPERS = ("registerSet",)

# Raw keyword hits that are legitimately NOT registration sites, each pinned to its
# anchor so a new unrecognized shape anywhere else refuses the extraction loudly.
RECONCILE_EXCLUSIONS = {
    ("register_builtin_option", "vendor/lean4-src/src/Lean/Data/Options.lean:228"):
        "the registerBuiltinOption macro definition",
    ("register_builtin_option", "vendor/lean4-src/src/Lean/Linter/EnvLinter/Basic.lean:90"):
        "an error-message string quoting the keyword",
    ("register_option", "vendor/lean4-src/src/Lean/Data/Options.lean:231"):
        "the registerOption macro definition",
    ("registerTraceClass", "vendor/lean4-src/src/Lean/Util/Trace.lean:379"):
        "the registerTraceClass definition itself",
    ("registerSet", "vendor/lean4-src/src/Lean/Linter/Sets.lean:23"):
        "the registerSet definition itself",
}


def json_escape(s):
    out = []
    for ch in s:
        if ch == '"':
            out.append('\\"')
        elif ch == "\\":
            out.append("\\\\")
        elif ch == "\n":
            out.append("\\n")
        elif ch == "\t":
            out.append("\\t")
        elif ord(ch) < 0x20:
            out.append(f"\\u{ord(ch):04x}")
        else:
            out.append(ch)
    return "".join(out)


def emit(row):
    parts = []
    for k in sorted(row):
        v = row[k]
        if isinstance(v, bool):
            parts.append(f'"{k}":{"true" if v else "false"}')
        else:
            parts.append(f'"{k}":"{json_escape(str(v))}"')
    return "{" + ",".join(parts) + "}"


def comment_spans(lines):
    """Per line: True when the line is entirely inside a block comment or is a
    line comment. Tracks nested `/- ... -/` (including doc forms)."""
    flags = []
    depth = 0
    for line in lines:
        start_depth = depth
        i = 0
        while i < len(line) - 1:
            pair = line[i : i + 2]
            if pair == "/-":
                depth += 1
                i += 2
                continue
            if pair == "-/" and depth > 0:
                depth -= 1
                i += 2
                continue
            i += 1
        inside = start_depth > 0 and depth > 0
        line_comment = line.lstrip().startswith("--")
        flags.append(inside or (start_depth > 0) or line_comment)
    return flags


def join_string_gaps(value, lines, i):
    """Lean string gap: a backslash before the newline continues the literal on the
    next line after leading whitespace. Returns (joined_value, last_index)."""
    while value.rstrip().endswith("\\") and i + 1 < len(lines):
        i += 1
        value = value.rstrip()[:-1] + lines[i].lstrip()
    return value, i


def brace_delta(line, in_string=False):
    """Brace count OUTSIDE string literals — a descr mentioning `{x}` or a block
    whose closing brace trails the string's final line must not skew the depth.
    The first version counted raw braces and a string-gap descr swallowed its
    block's closing `}`, consuming 227 lines of BEq.lean including three real
    trace registrations."""
    delta = 0
    escaped = False
    for ch in line:
        if escaped:
            escaped = False
            continue
        if ch == "\\":
            escaped = True
            continue
        if ch == '"':
            in_string = not in_string
            continue
        if in_string:
            continue
        if ch == "{":
            delta += 1
        elif ch == "}":
            delta -= 1
    return delta


def parse_block(lines, start):
    fields = {}
    depth = 1
    i = start
    while i + 1 < len(lines) and depth > 0:
        i += 1
        line = lines[i]
        m = re.match(r"^\s*([A-Za-z][A-Za-z0-9_]*)\s*:=\s*(.+?)\s*$", line)
        if m:
            depth += brace_delta(line)
            value, joined_to = join_string_gaps(m.group(2), lines, i)
            if joined_to != i:
                # Continuation lines live inside the string until the final
                # one closes it; only that final line's post-string tail can
                # carry block braces.
                depth += brace_delta(lines[joined_to], in_string=True)
                i = joined_to
            fields.setdefault(m.group(1), value)
        else:
            depth += brace_delta(line)
    return (fields if depth == 0 else None), i


def extract():
    rows = []
    counts = {"builtin_option": 0, "option": 0, "trace_class": 0, "dynamic": 0, "blocking": 0}
    recognized_anchors = set()
    raw_hits = []  # (keyword, anchor, in_comment)

    lean_files = []
    for dirpath, dirnames, filenames in os.walk(SRC_ROOT):
        dirnames.sort()
        for f in sorted(filenames):
            if f.endswith(".lean"):
                lean_files.append(os.path.join(dirpath, f))
    if not lean_files:
        raise SystemExit("REFUSE: empty scan — no .lean files under the pinned tree")

    for path in lean_files:
        rel = os.path.relpath(path, REPO)
        with open(path, encoding="utf-8") as fh:
            lines = fh.read().splitlines()
        in_comment = comment_spans(lines)
        for n, line in enumerate(lines):
            for kw in ("register_builtin_option", "register_option",
                       "registerTraceClass", *DYNAMIC_WRAPPERS):
                # Word-boundary matching: `lean_register_option` (the C export
                # attribute) must not count as a `register_option` hit.
                if re.search(rf"(?<![A-Za-z0-9_]){kw}(?![A-Za-z0-9_])", line):
                    raw_hits.append((kw, f"{rel}:{n + 1}", in_comment[n]))
        i = 0
        while i < len(lines):
            line = lines[i]
            anchor = f"{rel}:{i + 1}"
            if in_comment[i]:
                i += 1
                continue
            consumed = False
            for kind, rx in (("builtin_option", BUILTIN_RE), ("option", PLAIN_RE)):
                m = rx.match(line)
                if not m:
                    continue
                recognized_anchors.add(anchor)
                fields, end = parse_block(lines, i)
                if fields is None or "defValue" not in fields:
                    counts["blocking"] += 1
                    rows.append({
                        "schema": SCHEMA, "kind": "blocking",
                        "reason": "unparseable-registration-block",
                        "name": m.group(1), "source": anchor,
                    })
                else:
                    counts[kind] += 1
                    rows.append({
                        "schema": SCHEMA, "kind": kind,
                        "name": m.group(1), "value_type": m.group(2),
                        "default": fields["defValue"].rstrip(","),
                        "descr": fields.get("descr", "").strip('"'),
                        "source": anchor,
                    })
                i = end
                consumed = True
                break
            if consumed:
                i += 1
                continue
            if "registerTraceClass" in line and "def registerTraceClass" not in line:
                m = TRACE_RE.search(line)
                recognized_anchors.add(anchor)
                if m:
                    counts["trace_class"] += 1
                    rows.append({
                        "schema": SCHEMA, "kind": "trace_class",
                        "name": f"trace.{m.group(1)}",
                        "value_type": "Bool", "default": "false",
                        "inherited": "inherited := true" in line,
                        "descr": "enable/disable tracing for the given module and submodules",
                        "source": anchor,
                    })
                else:
                    counts["blocking"] += 1
                    rows.append({
                        "schema": SCHEMA, "kind": "blocking",
                        "reason": "trace-class-site-without-literal-name",
                        "name": "?", "source": anchor,
                    })
                i += 1
                continue
            for wrapper in DYNAMIC_WRAPPERS:
                if re.search(rf"\b{wrapper}\b", line):
                    recognized_anchors.add(anchor)
                    counts["dynamic"] += 1
                    rows.append({
                        "schema": SCHEMA, "kind": "dynamic",
                        "reason": f"runtime-registration-via-{wrapper}",
                        "name": "?", "source": anchor,
                    })
                    break
            i += 1

    # THE RECONCILIATION: every raw hit is recognized, in a comment, covered by a
    # recognized multi-line block... no — blocks never contain the keyword — or a
    # named exclusion. Anything else refuses the extraction.
    unexplained = []
    for kw, anchor, commented in raw_hits:
        if anchor in recognized_anchors or commented:
            continue
        if (kw, anchor) in RECONCILE_EXCLUSIONS:
            continue
        unexplained.append((kw, anchor))
    if unexplained:
        for kw, anchor in unexplained[:20]:
            print(f"UNRECONCILED {kw} at {anchor}", file=sys.stderr)
        raise SystemExit(
            f"REFUSE: {len(unexplained)} raw keyword hits are neither recognized "
            "sites, comments, nor named exclusions — the recognizer is a sampler"
        )
    emitted = sum(counts.values())
    rows.sort(key=lambda r: (r.get("name", ""), r["source"]))
    buf = io.StringIO()
    for row in rows:
        buf.write(emit(row) + "\n")
    return buf.getvalue(), counts, emitted


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out")
    ap.add_argument("--verify", action="store_true")
    args = ap.parse_args()
    text, counts, emitted = extract()
    if args.verify:
        text2, _, _ = extract()
        if text != text2:
            raise SystemExit("REFUSE: two extractions differ — nondeterministic scan")
    if args.out:
        tmp = args.out + ".tmp"
        with open(tmp, "w", encoding="utf-8") as fh:
            fh.write(text)
        os.replace(tmp, args.out)
    else:
        sys.stdout.write(text)
    print(
        f"option-census: builtin={counts['builtin_option']} option={counts['option']} "
        f"trace={counts['trace_class']} dynamic={counts['dynamic']} "
        f"BLOCKING={counts['blocking']} total={emitted}",
        file=sys.stderr,
    )


if __name__ == "__main__":
    main()
