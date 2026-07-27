#!/usr/bin/env -S python3 -I -S
"""gen_abi_contract.py — D5/D9 contract extraction: the ABI contract from the pinned lean.h.

The law (plan Appendix B, beads franken_lean-53v and franken_lean-b7n8): layout
constants are DERIVED, never remembered. This checked-in script parses the PINNED
Reference header and renders five artifacts from ONE canonical extraction, so they
cannot disagree by construction:

  contracts/abi_inventory.json   — the canonical intermediate (schema fln-abi-contract/1)
  contracts/ABI_TARGET_LAYOUT.txt
                                 — target-indexed sizes, alignments, offsets, widths,
                                   tag values, and resolved layout constants
  ABI_CONTRACT.md                — the human contract, per-field provenance
  crates/fln-rt/src/abi.rs       — the Rust constants module Marrow compiles against
  crates/fln-unsafe-abi/src/contract.rs
                                 — the layout partition re-rendered `pub(crate)` for the
                                   boundary crate (bead fln-lld): strict downward layering
                                   (rank 2 cannot import fln-rt at rank 3) and the D3
                                   no-export scaffold both forbid sharing fln-rt's copy,
                                   so the same inventory is rendered twice — same digest,
                                   same provenance, drift-checked together

The upstream header is parsed as DATA (Oracle-Only Law D8: fixture/census mine);
nothing from it executes. Target layouts are observed by the clang shipped in the
pinned Reference toolchain, using compile-only LLVM constants and AST record-layout
dumps for every certified SUITE.lock target. No target binary executes and no host
layout is projected onto another target. Extraction is offline and deterministic:
no timestamps, no ambient include paths, fixed locale/timezone, source order preserved.

Usage:
  scripts/extract/gen_abi_contract.py           # (re)generate all five artifacts
  scripts/extract/gen_abi_contract.py --check   # regenerate in memory, byte-compare
                                                # against the checked-in artifacts;
                                                # exit 1 with first divergence on drift

Any parse anomaly (anchor drift in the pin, unexpected declaration shape) is a
loud failure with the offending line — never a silently narrower contract.
"""

import hashlib
import json
import os
import re
import subprocess
import sys
from bisect import bisect_right
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LEAN_H = ROOT / "vendor" / "lean4-src" / "src" / "include" / "lean" / "lean.h"
SUITE_LOCK = ROOT / "SUITE.lock"
INVENTORY_PATH = ROOT / "contracts" / "abi_inventory.json"
TARGET_LAYOUT_PATH = ROOT / "contracts" / "ABI_TARGET_LAYOUT.txt"
CONTRACT_PATH = ROOT / "ABI_CONTRACT.md"
RUST_PATH = ROOT / "crates" / "fln-rt" / "src" / "abi.rs"
BOUNDARY_RUST_PATH = ROOT / "crates" / "fln-unsafe-abi" / "src" / "contract.rs"

SCHEMA = "fln-abi-contract/1"
TARGET_LAYOUT_SCHEMA = "fln-abi-target-layout/1"
TARGET_LAYOUT_EXTRACTOR = "lean-h-clang-layout"
TARGET_LAYOUT_EXTRACTOR_VERSION = "1"
SRC_REL = "vendor/lean4-src/src/include/lean/lean.h"
TOOLCHAIN_HEADER_REL = "include/lean/lean.h"
CLANG_TIMEOUT_SECONDS = 30
MAX_CLANG_OUTPUT_BYTES = 4 * 1024 * 1024

# Object structs whose field layouts are contract (plan §6.2). Auxiliary structs
# (task_imp, external_class) are included: their fields are reachable from object
# headers and Marrow must know them.
TARGET_STRUCTS = [
    "lean_object",
    "lean_ctor_object",
    "lean_array_object",
    "lean_sarray_object",
    "lean_string_object",
    "lean_closure_object",
    "lean_ref_object",
    "lean_thunk_object",
    "lean_task_imp",
    "lean_task_object",
    "lean_promise_object",
    "lean_external_class",
    "lean_external_object",
]

# Layout #defines that are contract. Integer-valued ones become Rust consts;
# expression-valued ones are recorded verbatim with provenance.
LAYOUT_DEFINES = [
    "LEAN_CLOSURE_MAX_ARGS",
    "LEAN_OBJECT_SIZE_DELTA",
    "LEAN_MAX_SMALL_OBJECT_SIZE",
    "LEAN_MAX_CTOR_FIELDS",
    "LEAN_MAX_CTOR_SCALARS_SIZE",
    "LEAN_TASK_STATE_WAITING",
    "LEAN_TASK_STATE_RUNNING",
    "LEAN_TASK_STATE_FINISHED",
    "LEAN_MAX_SMALL_NAT",
    "LEAN_MAX_SMALL_INT",
    "LEAN_MIN_SMALL_INT",
]

OWNERSHIP_TYPEDEFS = [
    "lean_obj_arg",
    "b_lean_obj_arg",
    "u_lean_obj_arg",
    "lean_obj_res",
    "b_lean_obj_res",
]


def die(msg: str) -> "NoReturn":  # noqa: F821 - documentation type only
    print(f"gen_abi_contract: FATAL: {msg}", file=sys.stderr)
    sys.exit(1)


def read_pin() -> dict:
    for line in SUITE_LOCK.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if line.startswith("reference "):
            fields = dict(
                part.split("=", 1) for part in line.split()[2:] if "=" in part
            )
            if "tag" not in fields or "commit" not in fields:
                die(f"SUITE.lock reference row missing tag/commit: {line!r}")
            return {
                "repo": line.split()[1],
                "tag": fields["tag"],
                "commit": fields["commit"],
                "tree": fields.get("tree", ""),
            }
    die("SUITE.lock has no reference row")


def read_targets() -> list[str]:
    targets = []
    for line in SUITE_LOCK.read_text(encoding="utf-8").splitlines():
        line = line.split("#", 1)[0].strip()
        if line.startswith("target "):
            tokens = line.split()
            if len(tokens) != 2:
                die(f"SUITE.lock target row is not canonical: {line!r}")
            target = tokens[1]
            if not re.fullmatch(r"[A-Za-z0-9_.-]+", target):
                die(f"SUITE.lock target is not a safe target triple: {target!r}")
            if target in targets:
                die(f"SUITE.lock repeats target {target!r}")
            targets.append(target)
    if not targets:
        die("SUITE.lock has no certified target rows")
    return targets


def strip_comments(text: str) -> str:
    """Replace comment bodies with spaces, preserving length and newlines so
    byte offsets and line numbers survive."""
    out = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == "/" and i + 1 < n and text[i + 1] == "*":
            j = text.find("*/", i + 2)
            if j == -1:
                die("unterminated block comment in lean.h")
            j += 2
            out.append("".join(ch if ch == "\n" else " " for ch in text[i:j]))
            i = j
        elif c == "/" and i + 1 < n and text[i + 1] == "/":
            j = text.find("\n", i)
            j = n if j == -1 else j
            out.append(" " * (j - i))
            i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            out.append(text[i:j])
            i = j
        else:
            out.append(c)
            i += 1
    stripped = "".join(out)
    if len(stripped) != len(text):
        die("comment stripping changed text length (bug)")
    return stripped


class LineMap:
    def __init__(self, text: str):
        self.starts = [0]
        for i, ch in enumerate(text):
            if ch == "\n":
                self.starts.append(i + 1)

    def line(self, offset: int) -> int:
        return bisect_right(self.starts, offset)


def parse_tags(lines: list[str]) -> list[dict]:
    tags = []
    rx = re.compile(r"^#define\s+(Lean[A-Za-z]+)\s+(\d+)\s*$")
    for idx, raw in enumerate(lines, start=1):
        m = rx.match(raw)
        if m:
            tags.append({"name": m.group(1), "value": int(m.group(2)), "line": idx})
    if len(tags) != 13:
        die(f"expected exactly 13 object-tag #defines, found {len(tags)}: "
            f"{[t['name'] for t in tags]}")
    values = [t["value"] for t in tags]
    if sorted(values) != list(range(min(values), min(values) + 13)):
        die(f"object-tag values are not a contiguous run: {values}")
    return tags


def parse_layout_defines(lines: list[str]) -> list[dict]:
    found = {}
    rx = re.compile(r"^#define\s+(LEAN_[A-Z_0-9]+)\s+(.+?)\s*$")
    for idx, raw in enumerate(lines, start=1):
        m = rx.match(raw)
        if m and m.group(1) in LAYOUT_DEFINES and m.group(1) not in found:
            value = m.group(2).strip()
            entry = {"name": m.group(1), "line": idx}
            if re.fullmatch(r"\d+", value):
                entry["value"] = int(value)
            else:
                entry["expr"] = value
            found[m.group(1)] = entry
    missing = [n for n in LAYOUT_DEFINES if n not in found]
    if missing:
        die(f"layout #defines not found in lean.h: {missing}")
    return [found[n] for n in LAYOUT_DEFINES]


FIELD_RX = re.compile(
    r"^\s*(.+?)\s*\b([A-Za-z_]\w*)\s*(\[\s*\d*\s*\])?\s*(?::\s*(\d+))?\s*;\s*$"
)


def parse_structs(
    stripped: str, lmap: LineMap, selected_names: list[str] | None
) -> list[dict]:
    structs = []
    by_name = {}
    # Anonymous form: typedef struct { ... } name;  Named form: typedef struct tag { ... } name;
    rx = re.compile(r"typedef\s+struct(?:\s+(\w+))?\s*\{", re.M)
    for m in rx.finditer(stripped):
        brace_open = m.end() - 1
        depth, j = 1, brace_open + 1
        while j < len(stripped) and depth:
            if stripped[j] == "{":
                depth += 1
            elif stripped[j] == "}":
                depth -= 1
            j += 1
        tail = re.match(r"\s*(\w+)\s*;", stripped[j:])
        if not tail:
            continue
        name = tail.group(1)
        if selected_names is not None and name not in selected_names:
            continue
        body = stripped[m.end():j - 1]
        body_line0 = lmap.line(m.end())
        fields = []
        for k, fline in enumerate(body.split("\n")):
            if not fline.strip():
                continue
            fm = FIELD_RX.match(fline)
            if not fm:
                # tolerate non-field lines only if they are preprocessor lines
                if fline.strip().startswith("#"):
                    continue
                die(f"unparsed field line in struct {name}: {fline.strip()!r}")
            fields.append({
                "c_type": re.sub(r"\s+", " ", fm.group(1)).strip(),
                "name": fm.group(2),
                "flexible_array": fm.group(3) is not None and "0" not in (fm.group(3) or ""),
                "array": (fm.group(3) or "").replace(" ", "") or None,
                "bits": int(fm.group(4)) if fm.group(4) else None,
                "line": body_line0 + k,
            })
        if not fields:
            die(f"struct {name} parsed with zero fields")
        entry = {
            "name": name,
            "line_start": lmap.line(m.start()),
            "line_end": lmap.line(j),
            "fields": fields,
        }
        structs.append(entry)
        if name in by_name:
            die(f"duplicate public struct typedef in lean.h: {name}")
        by_name[name] = entry
    if selected_names is not None:
        missing = [name for name in selected_names if name not in by_name]
        if missing:
            die(f"selected ABI structs not found in lean.h: {missing}")
        # Preserve the reviewed object-model order for the pre-existing v1 inventory.
        return [by_name[name] for name in selected_names]
    if not structs:
        die("lean.h contains no public struct typedefs")
    # Full target-layout extraction is source-ordered and mechanically exhaustive.
    return structs


def parse_ownership(lines: list[str], raw_lines: list[str]) -> list[dict]:
    found = {}
    rx = re.compile(r"^typedef\s+lean_object\s*\*\s*(\w+)\s*;")
    for idx, raw in enumerate(lines, start=1):
        m = rx.match(raw)
        if m and m.group(1) in OWNERSHIP_TYPEDEFS:
            doc = ""
            dm = re.search(r"/\*\s*(.*?)\s*\*/", raw_lines[idx - 1])
            if dm:
                doc = dm.group(1)
            found[m.group(1)] = {"name": m.group(1), "doc": doc, "line": idx}
    missing = [n for n in OWNERSHIP_TYPEDEFS if n not in found]
    if missing:
        die(f"ownership typedefs not found: {missing}")
    return [found[n] for n in OWNERSHIP_TYPEDEFS]


def classify_ownership(param_text: str) -> str:
    if re.search(r"\bb_lean_obj_arg\b", param_text):
        return "borrowed_arg"
    if re.search(r"\bu_lean_obj_arg\b", param_text):
        return "unique_arg"
    if re.search(r"\blean_obj_arg\b", param_text):
        return "owned_arg"
    if re.search(r"\bb_lean_obj_res\b", param_text):
        return "borrowed_res"
    if re.search(r"\blean_obj_res\b", param_text):
        return "owned_res"
    if re.search(r"\blean_object\b", param_text):
        return "raw_object"
    return "value"


def split_params(args: str) -> list[str]:
    parts, depth, cur = [], 0, []
    for ch in args:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append("".join(cur))
            cur = []
        else:
            cur.append(ch)
    if cur:
        parts.append("".join(cur))
    return [re.sub(r"\s+", " ", p).strip() for p in parts if p.strip()]


TYPE_KEYWORDS = {
    "void", "int", "unsigned", "bool", "char", "float", "double", "size_t",
    "ptrdiff_t", "uint8_t", "uint16_t", "uint32_t", "uint64_t", "int8_t",
    "int16_t", "int32_t", "int64_t", "usize", "lean_obj_arg", "b_lean_obj_arg",
    "u_lean_obj_arg", "lean_obj_res", "b_lean_obj_res", "lean_object",
}


def parse_param(p: str) -> dict:
    if p == "void":
        return None
    m = re.match(r"^(.*?)([A-Za-z_]\w*)$", p)
    if m and m.group(1).strip() and m.group(2) not in TYPE_KEYWORDS:
        c_type, name = m.group(1).strip(), m.group(2)
    else:
        c_type, name = p, ""
    return {"c_type": c_type, "name": name, "ownership": classify_ownership(c_type or p)}


def scan_balanced(stripped: str, open_paren: int) -> int:
    depth, j = 1, open_paren + 1
    while j < len(stripped) and depth:
        if stripped[j] == "(":
            depth += 1
        elif stripped[j] == ")":
            depth -= 1
        j += 1
    return j  # index just past the closing paren


def parse_functions(stripped: str, lmap: LineMap) -> list[dict]:
    fns = []
    export_rx = re.compile(r"^[ \t]*LEAN_EXPORT[ \t]+([^\n;{]*?)\b(lean_\w+)[ \t]*\(", re.M)
    inline_rx = re.compile(
        r"^static[ \t]+inline[ \t]+(?:LEAN_ALWAYS_INLINE[ \t]+)?([^\n;{]*?)\b(lean_\w+)[ \t]*\(",
        re.M,
    )
    for kind, rx, terminator in (("export", export_rx, ";"), ("inline", inline_rx, "{")):
        for m in rx.finditer(stripped):
            close = scan_balanced(stripped, m.end() - 1)
            tail = stripped[close:close + 200].lstrip()
            if not tail.startswith(terminator):
                die(f"{kind} declaration for {m.group(2)} at line "
                    f"{lmap.line(m.start())} not terminated by {terminator!r}")
            ret = re.sub(r"\s+", " ", m.group(1)).strip()
            ret = re.sub(r"\b(LEAN_ALWAYS_INLINE|LEAN_NORETURN)\b", "", ret).strip()
            params = [p for p in (parse_param(x) for x in
                                  split_params(stripped[m.end():close - 1]))
                      if p is not None]
            fns.append({
                "name": m.group(2),
                "linkage": kind,
                "ret_c_type": ret,
                "ret_ownership": classify_ownership(ret),
                "params": params,
                "line": lmap.line(m.start()),
            })
    # Self-consistency: parsed counts must match raw pattern counts.
    raw_exports = len(re.findall(r"^[ \t]*LEAN_EXPORT\b", stripped, re.M))
    raw_inlines = len(re.findall(r"^static[ \t]+inline\b", stripped, re.M))
    n_export = sum(1 for f in fns if f["linkage"] == "export")
    n_inline = sum(1 for f in fns if f["linkage"] == "inline")
    if n_export != raw_exports:
        die(f"export census incomplete: parsed {n_export}, raw lines {raw_exports}")
    if n_inline != raw_inlines:
        die(f"inline census incomplete: parsed {n_inline}, raw lines {raw_inlines}")
    if n_export < 150 or n_inline < 400:
        die(f"census implausibly small (export={n_export}, inline={n_inline}) — anchor drift?")
    fns.sort(key=lambda f: (f["name"], f["line"]))
    return fns


def build_inventory() -> dict:
    text = LEAN_H.read_text(encoding="utf-8")
    raw_lines = text.splitlines()
    stripped = strip_comments(text)
    stripped_lines = stripped.splitlines()
    lmap = LineMap(text)
    pin = read_pin()
    return {
        "schema": SCHEMA,
        "pin": pin,
        "source": {
            "path": SRC_REL,
            "sha256": hashlib.sha256(text.encode("utf-8")).hexdigest(),
            "lines": len(raw_lines),
        },
        "tags": parse_tags(stripped_lines),
        "layout": parse_layout_defines(stripped_lines),
        "ownership": parse_ownership(stripped_lines, raw_lines),
        "structs": parse_structs(stripped, lmap, TARGET_STRUCTS),
        "functions": parse_functions(stripped, lmap),
    }


def fnv1a64_fields(domain: str, fields: list[bytes]) -> int:
    state = 0xCBF29CE484222325

    def update(payload: bytes) -> None:
        nonlocal state
        for byte in payload:
            state ^= byte
            state = (state * 0x00000100000001B3) & 0xFFFFFFFFFFFFFFFF

    update(domain.encode("ascii"))
    update(b"\0")
    for field in fields:
        update(len(field).to_bytes(8, "little"))
        update(field)
    return state


def labeled_fnv(value: int) -> str:
    return f"fnv1a64:{value:016x}"


def reference_toolchain(pin: dict) -> Path:
    tag = pin["tag"]
    if not re.fullmatch(r"v[0-9]+\.[0-9]+\.[0-9]+(?:[-.A-Za-z0-9]*)?", tag):
        die(f"Reference tag cannot map to an elan toolchain safely: {tag!r}")
    toolchain = (
        Path.home()
        / ".elan"
        / "toolchains"
        / f"leanprover--lean4---{tag}"
    )
    required = [
        toolchain / "bin" / "clang",
        toolchain / TOOLCHAIN_HEADER_REL,
        toolchain / "include" / "clang" / "stddef.h",
    ]
    missing = [str(path) for path in required if not path.is_file()]
    if missing:
        die(
            "pinned Reference toolchain is incomplete; local extraction requires "
            f"{toolchain}: missing {missing}"
        )
    return toolchain


def clang_base(toolchain: Path, target: str) -> list[str]:
    return [
        str(toolchain / "bin" / "clang"),
        f"--target={target}",
        "--sysroot",
        str(toolchain),
        "-nostdinc",
        "-isystem",
        str(toolchain / "include" / "clang"),
        "-I",
        str(toolchain / "include"),
        "-x",
        "c",
        "-std=c11",
        "-fno-color-diagnostics",
        "-Werror",
    ]


def run_clang(
    toolchain: Path,
    target: str,
    source: str,
    extra_args: list[str],
    purpose: str,
) -> tuple[str, str]:
    command = clang_base(toolchain, target) + extra_args + ["-"]
    environment = {
        "HOME": str(Path.home()),
        "LANG": "C",
        "LC_ALL": "C",
        "PATH": "/usr/bin:/bin",
        "TZ": "UTC",
    }
    try:
        completed = subprocess.run(
            command,
            input=source,
            text=True,
            capture_output=True,
            timeout=CLANG_TIMEOUT_SECONDS,
            check=False,
            env=environment,
        )
    except subprocess.TimeoutExpired:
        die(
            f"pinned clang {purpose} timed out after "
            f"{CLANG_TIMEOUT_SECONDS}s for target {target}"
        )
    output_bytes = len(completed.stdout.encode()) + len(completed.stderr.encode())
    if output_bytes > MAX_CLANG_OUTPUT_BYTES:
        die(
            f"pinned clang {purpose} emitted {output_bytes} bytes for target "
            f"{target}; bounded maximum is {MAX_CLANG_OUTPUT_BYTES}"
        )
    if completed.returncode != 0:
        detail = (completed.stderr or completed.stdout).strip()
        die(
            f"pinned clang {purpose} failed for target {target} "
            f"(exit {completed.returncode}): {detail}"
        )
    return completed.stdout, completed.stderr


def probe_name(*parts: str) -> str:
    name = "__".join(parts)
    if not re.fullmatch(r"[A-Za-z0-9_]+", name):
        die(f"internal probe identifier is not C-safe: {name!r}")
    return name


def build_probe_source(inv: dict) -> tuple[str, set[str]]:
    lines = [
        "#include <lean/lean.h>",
        "#include <limits.h>",
        "#define FLN_PROBE(name, expr) "
        "const long long fln_probe_##name = (long long)(expr)",
        "FLN_PROBE(pointer_bits, sizeof(void *) * CHAR_BIT);",
        "FLN_PROBE(size_t_bits, sizeof(size_t) * CHAR_BIT);",
        "FLN_PROBE(char_bits, CHAR_BIT);",
        "FLN_PROBE(int_bits, sizeof(int) * CHAR_BIT);",
        "FLN_PROBE(unsigned_bits, sizeof(unsigned) * CHAR_BIT);",
        "FLN_PROBE(long_bits, sizeof(long) * CHAR_BIT);",
        "FLN_PROBE(long_long_bits, sizeof(long long) * CHAR_BIT);",
        "FLN_PROBE(max_align_bytes, _Alignof(max_align_t));",
        "#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__",
        "FLN_PROBE(endianness, 0);",
        "#elif __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__",
        "FLN_PROBE(endianness, 1);",
        "#else",
        "#error unsupported target byte order",
        "#endif",
    ]
    names = {
        "pointer_bits",
        "size_t_bits",
        "char_bits",
        "int_bits",
        "unsigned_bits",
        "long_bits",
        "long_long_bits",
        "max_align_bytes",
        "endianness",
    }

    for define in inv["layout"]:
        name = probe_name("define", define["name"])
        names.add(name)
        lines.append(f"FLN_PROBE({name}, {define['name']});")

    for struct in inv["structs"]:
        struct_name = struct["name"]
        size_name = probe_name("struct", struct_name, "size")
        align_name = probe_name("struct", struct_name, "align")
        names.update((size_name, align_name))
        lines.append(f"FLN_PROBE({size_name}, sizeof({struct_name}));")
        lines.append(f"FLN_PROBE({align_name}, _Alignof({struct_name}));")
        for field in struct["fields"]:
            if field["bits"] is not None:
                continue
            field_name = field["name"]
            offset_name = probe_name("field", struct_name, field_name, "offset")
            names.add(offset_name)
            lines.append(
                f"FLN_PROBE({offset_name}, "
                f"__builtin_offsetof({struct_name}, {field_name}));"
            )
            if field["flexible_array"]:
                element_name = probe_name(
                    "field", struct_name, field_name, "element_size"
                )
                names.add(element_name)
                lines.append(
                    f"FLN_PROBE({element_name}, "
                    f"sizeof(*((({struct_name} *)0)->{field_name})));"
                )
            else:
                width_name = probe_name("field", struct_name, field_name, "size")
                names.add(width_name)
                lines.append(
                    f"FLN_PROBE({width_name}, "
                    f"sizeof((({struct_name} *)0)->{field_name}));"
                )

    # A complete object forces clang's bitfield record-layout dump without executing
    # any target code. Other offsets and widths come from compile-time LLVM constants.
    lines.append("lean_object fln_probe_record_layout_lean_object;")
    return "\n".join(lines) + "\n", names


IR_VALUE_RX = re.compile(
    r"^@fln_probe_([A-Za-z0-9_]+)\s*=.*\bconstant\s+i[0-9]+\s+(-?[0-9]+),",
    re.M,
)


def parse_ir_values(ir: str, expected: set[str], target: str) -> dict[str, int]:
    values = {}
    for match in IR_VALUE_RX.finditer(ir):
        name = match.group(1)
        if name in values:
            die(f"pinned clang repeated LLVM probe constant {name!r} for {target}")
        values[name] = int(match.group(2))
    missing = sorted(expected - values.keys())
    extra = sorted(values.keys() - expected)
    if missing or extra:
        die(
            f"pinned clang LLVM probe set differs for {target}: "
            f"missing={missing} extra={extra}"
        )
    triple = re.search(r'^target triple = "([^"]+)"$', ir, re.M)
    if triple is None or triple.group(1) != target:
        die(
            f"pinned clang normalized target unexpectedly: requested={target!r} "
            f"emitted={triple.group(1) if triple else None!r}"
        )
    return values


def parse_lean_object_bitfields(
    layout_output: str, inv: dict, target: str
) -> dict[str, tuple[int, int]]:
    blocks = layout_output.split("*** Dumping AST Record Layout")
    block = next(
        (
            candidate
            for candidate in blocks
            if re.search(r"^\s*0\s+\|\s+lean_object\s*$", candidate, re.M)
        ),
        None,
    )
    if block is None:
        die(f"pinned clang did not emit lean_object record layout for {target}")
    size_align = re.search(r"\[sizeof=([0-9]+), align=([0-9]+)\]", block)
    if size_align is None:
        die(f"lean_object record layout lacks size/alignment for {target}")

    expected = {
        field["name"]: field["bits"]
        for struct in inv["structs"]
        if struct["name"] == "lean_object"
        for field in struct["fields"]
        if field["bits"] is not None
    }
    observed = {}
    bitfield_rx = re.compile(
        r"^\s*([0-9]+):([0-9]+)-([0-9]+)\s+\|\s+"
        r"unsigned(?:\s+int)?\s+(m_[A-Za-z0-9_]+)\s*$",
        re.M,
    )
    for match in bitfield_rx.finditer(block):
        byte_offset = int(match.group(1))
        first_bit = int(match.group(2))
        last_bit = int(match.group(3))
        name = match.group(4)
        if name not in expected:
            continue
        width = last_bit - first_bit + 1
        if width != expected[name]:
            die(
                f"lean_object bitfield {name} width drift for {target}: "
                f"header={expected[name]} clang={width}"
            )
        observed[name] = (byte_offset * 8 + first_bit, width)
    missing = sorted(expected.keys() - observed.keys())
    if missing:
        die(f"pinned clang omitted lean_object bitfields for {target}: {missing}")
    return observed


def classify_data_model(values: dict[str, int], target: str) -> str:
    shape = (
        values["int_bits"],
        values["long_bits"],
        values["pointer_bits"],
        values["size_t_bits"],
    )
    models = {
        (32, 64, 64, 64): "lp64",
        (32, 32, 64, 64): "llp64",
        (32, 32, 32, 32): "ilp32",
    }
    model = models.get(shape)
    if model is None:
        die(
            f"target {target} has an unclassified C data model "
            f"(int,long,pointer,size_t)={shape}; publication is inconclusive"
        )
    return model


def extract_target_layout(inv: dict, toolchain: Path, target: str) -> dict:
    source, expected = build_probe_source(inv)
    ir, ir_stderr = run_clang(
        toolchain,
        target,
        source,
        ["-S", "-emit-llvm", "-o", "-"],
        "LLVM constant extraction",
    )
    if ir_stderr.strip():
        die(
            f"pinned clang LLVM constant extraction emitted unexpected stderr "
            f"for {target}: {ir_stderr.strip()}"
        )
    values = parse_ir_values(ir, expected, target)
    layout_stdout, layout_stderr = run_clang(
        toolchain,
        target,
        source,
        ["-Xclang", "-fdump-record-layouts", "-fsyntax-only"],
        "record-layout extraction",
    )
    bitfields = parse_lean_object_bitfields(
        layout_stdout + "\n" + layout_stderr, inv, target
    )
    endianness = {0: "little", 1: "big"}.get(values["endianness"])
    if endianness is None:
        die(f"target {target} emitted unknown endianness code {values['endianness']}")
    data_model = classify_data_model(values, target)

    structs = []
    for struct in inv["structs"]:
        struct_name = struct["name"]
        fields = []
        for field in struct["fields"]:
            field_name = field["name"]
            if field["bits"] is not None:
                offset_bits, width_bits = bitfields[field_name]
                storage = "bitfield"
                element_width_bits = 0
            else:
                offset = values[
                    probe_name("field", struct_name, field_name, "offset")
                ]
                offset_bits = offset * values["char_bits"]
                if field["flexible_array"]:
                    width_bits = 0
                    element_width_bits = (
                        values[
                            probe_name(
                                "field",
                                struct_name,
                                field_name,
                                "element_size",
                            )
                        ]
                        * values["char_bits"]
                    )
                    storage = "flexible-array"
                else:
                    width_bits = (
                        values[probe_name("field", struct_name, field_name, "size")]
                        * values["char_bits"]
                    )
                    element_width_bits = 0
                    storage = "scalar"
            fields.append(
                {
                    "name": field_name,
                    "offset_bits": offset_bits,
                    "width_bits": width_bits,
                    "element_width_bits": element_width_bits,
                    "storage": storage,
                    "source_line": field["line"],
                }
            )
        structs.append(
            {
                "name": struct_name,
                "size_bytes": values[probe_name("struct", struct_name, "size")],
                "align_bytes": values[probe_name("struct", struct_name, "align")],
                "source_line_start": struct["line_start"],
                "source_line_end": struct["line_end"],
                "fields": fields,
            }
        )

    endian_class = {"little": "le", "big": "be"}[endianness]
    return {
        "data_model": data_model,
        "abi_class": f"{data_model}-{endian_class}",
        "endianness": endianness,
        "pointer_bits": values["pointer_bits"],
        "size_t_bits": values["size_t_bits"],
        "char_bits": values["char_bits"],
        "int_bits": values["int_bits"],
        "unsigned_bits": values["unsigned_bits"],
        "long_bits": values["long_bits"],
        "long_long_bits": values["long_long_bits"],
        "max_align_bytes": values["max_align_bytes"],
        "layout": [
            {
                "name": define["name"],
                "value": values[probe_name("define", define["name"])],
                "source_line": define["line"],
            }
            for define in inv["layout"]
        ],
        "tags": [
            {
                "name": tag["name"],
                "value": tag["value"],
                "source_line": tag["line"],
            }
            for tag in inv["tags"]
        ],
        "structs": structs,
    }


def render_target_layout(inv: dict) -> str:
    pin = inv["pin"]
    toolchain = reference_toolchain(pin)
    toolchain_header = toolchain / TOOLCHAIN_HEADER_REL
    toolchain_bytes = toolchain_header.read_bytes()
    vendor_bytes = LEAN_H.read_bytes()
    if toolchain_bytes != vendor_bytes:
        die(
            "pinned toolchain lean.h differs from the vendored Reference source: "
            f"toolchain_sha256={hashlib.sha256(toolchain_bytes).hexdigest()} "
            f"vendor_sha256={hashlib.sha256(vendor_bytes).hexdigest()}"
        )
    header_sha = hashlib.sha256(toolchain_bytes).hexdigest()
    targets = read_targets()
    vendor_text = vendor_bytes.decode("utf-8")
    layout_inventory = dict(inv)
    layout_inventory["structs"] = parse_structs(
        strip_comments(vendor_text), LineMap(vendor_text), None
    )

    output = [
        f"schema {TARGET_LAYOUT_SCHEMA}",
        f"extractor {TARGET_LAYOUT_EXTRACTOR} "
        f"version={TARGET_LAYOUT_EXTRACTOR_VERSION}",
        "source path=include/lean/lean.h authority=SUITE.lock:reference "
        f"sha256={header_sha}",
        f"target-count {len(targets)}",
    ]
    for index, target in enumerate(targets, start=1):
        key = f"target:{index:04}"
        layout = extract_target_layout(layout_inventory, toolchain, target)
        block = [
            f"target {key} abi-class={layout['abi_class']} "
            f"data-model={layout['data_model']} endianness={layout['endianness']} "
            f"pointer-bits={layout['pointer_bits']} "
            f"size-t-bits={layout['size_t_bits']} char-bits={layout['char_bits']} "
            f"int-bits={layout['int_bits']} unsigned-bits={layout['unsigned_bits']} "
            f"long-bits={layout['long_bits']} "
            f"long-long-bits={layout['long_long_bits']} "
            f"max-align-bytes={layout['max_align_bytes']}"
        ]
        for define in layout["layout"]:
            block.append(
                f"define {key} name={define['name']} value={define['value']} "
                f"source-line={define['source_line']}"
            )
        for tag in layout["tags"]:
            block.append(
                f"tag {key} name={tag['name']} value={tag['value']} "
                f"source-line={tag['source_line']}"
            )
        for struct in layout["structs"]:
            block.append(
                f"struct {key} name={struct['name']} "
                f"size-bytes={struct['size_bytes']} align-bytes={struct['align_bytes']} "
                f"source-lines={struct['source_line_start']}-{struct['source_line_end']}"
            )
            for field in struct["fields"]:
                block.append(
                    f"field {key} struct={struct['name']} name={field['name']} "
                    f"offset-bits={field['offset_bits']} "
                    f"width-bits={field['width_bits']} storage={field['storage']} "
                    f"element-width-bits={field['element_width_bits']} "
                    f"source-line={field['source_line']}"
                )
        block_bytes = ("\n".join(block) + "\n").encode("utf-8")
        output.extend(block)
        output.append(
            f"target-root {key} "
            f"{labeled_fnv(fnv1a64_fields('fln.abi-target-layout.target-root/1', [block_bytes]))}"
        )

    prefix = "\n".join(output) + "\n"
    root = labeled_fnv(
        fnv1a64_fields(
            "fln.abi-target-layout.inventory-root/1", [prefix.encode("utf-8")]
        )
    )
    return prefix + f"inventory-root {root}\n"


# ---------------------------------------------------------------- rendering

def render_inventory(inv: dict) -> str:
    return json.dumps(inv, indent=1, sort_keys=True, ensure_ascii=True) + "\n"


def const_name(tag: str) -> str:
    # LeanMaxCtorTag -> TAG_MAX_CTOR_TAG-ish; keep it mechanical: split camel case.
    words = re.findall(r"[A-Z]+(?![a-z])|[A-Z][a-z0-9]*", tag)
    assert words[0] == "Lean"
    return "TAG_" + "_".join(w.upper() for w in words[1:])


def rust_ownership(o: str) -> str:
    return {
        "owned_arg": "OwnedArg",
        "borrowed_arg": "BorrowedArg",
        "unique_arg": "UniqueArg",
        "owned_res": "OwnedRes",
        "borrowed_res": "BorrowedRes",
        "raw_object": "RawObject",
        "value": "Value",
    }[o]


def render_rust(inv: dict, digest: str) -> str:
    pin = inv["pin"]
    src = inv["source"]
    w = []
    w.append("//! Marrow's ABI constants — **@generated** by `scripts/extract/gen_abi_contract.py`. DO NOT EDIT.")
    w.append("//!")
    w.append(f"//! Extracted from the pinned Reference header `{src['path']}`")
    w.append(f"//! ({pin['repo']} {pin['tag']}, commit {pin['commit']}).")
    w.append("//! The extraction law (plan Appendix B, Rule D5/D9): layout constants are")
    w.append("//! derived, never remembered. Regenerate with the script; CI fails on drift")
    w.append("//! among pin, `ABI_CONTRACT.md`, `contracts/abi_inventory.json`, and this file.")
    w.append("")
    w.append("/// BLAKE-independent binding to the canonical inventory this module was rendered from")
    w.append("/// (SHA-256 of `contracts/abi_inventory.json`).")
    w.append(f'pub const INVENTORY_DIGEST: &str = "{digest}";')
    w.append(f'/// The Reference pin this contract is extracted from.')
    w.append(f'pub const PIN_TAG: &str = "{pin["tag"]}";')
    w.append(f'pub const PIN_COMMIT: &str = "{pin["commit"]}";')
    w.append(f"/// SHA-256 of the pinned `lean.h` these constants were derived from.")
    w.append(f'pub const LEAN_H_SHA256: &str = "{src["sha256"]}";')
    w.append("")
    w.append("// ---- object tags (lean.h tag block) ------------------------------------")
    for t in inv["tags"]:
        w.append(f"/// `#define {t['name']} {t['value']}` — {src['path']}:{t['line']}")
        w.append(f"pub const {const_name(t['name'])}: u8 = {t['value']};")
    w.append("")
    w.append("// ---- layout constants ---------------------------------------------------")
    for d in inv["layout"]:
        if "value" in d:
            w.append(f"/// `#define {d['name']}` — {src['path']}:{d['line']}")
            w.append(f"pub const {d['name'].removeprefix('LEAN_')}: usize = {d['value']};")
        else:
            w.append(f"/// `#define {d['name']} {d['expr']}` — {src['path']}:{d['line']} (expression; platform-dependent width)")
            w.append(f'pub const {d["name"].removeprefix("LEAN_")}_EXPR: &str = "{d["expr"]}";')
    w.append("")
    w.append("// ---- ownership conventions ---------------------------------------------")
    w.append("/// Per-parameter / per-result ownership classes of the `lean_*` C ABI")
    w.append("/// (the five `lean.h` typedefs plus raw/value).")
    w.append("#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]")
    w.append("pub enum Ownership {")
    w.append("    /// `lean_obj_arg` — standard owned (consumed) argument.")
    w.append("    OwnedArg,")
    w.append("    /// `b_lean_obj_arg` — borrowed argument; caller retains ownership.")
    w.append("    BorrowedArg,")
    w.append("    /// `u_lean_obj_arg` — unique (RC=1) argument; destructive update allowed.")
    w.append("    UniqueArg,")
    w.append("    /// `lean_obj_res` — owned result; caller must consume.")
    w.append("    OwnedRes,")
    w.append("    /// `b_lean_obj_res` — borrowed result; caller must not decrement.")
    w.append("    BorrowedRes,")
    w.append("    /// bare `lean_object *` — raw pointer outside the ownership typedefs.")
    w.append("    RawObject,")
    w.append("    /// non-object scalar/value parameter or result.")
    w.append("    Value,")
    w.append("}")
    w.append("")
    w.append("// ---- object layout tables ----------------------------------------------")
    w.append("/// One C struct field of the object model, with provenance.")
    w.append("#[derive(Debug, Clone, Copy, PartialEq, Eq)]")
    w.append("pub struct FieldSpec {")
    w.append("    pub name: &'static str,")
    w.append("    pub c_type: &'static str,")
    w.append("    /// bit width when the field is a C bitfield")
    w.append("    pub bits: Option<u8>,")
    w.append("    /// `Some(\"[]\")`/`Some(\"[N]\")` for array fields (flexible arrays are `[]`)")
    w.append("    pub array: Option<&'static str>,")
    w.append(f"    /// 1-based line in `{src['path']}`")
    w.append("    pub line: u32,")
    w.append("}")
    w.append("")
    w.append("#[derive(Debug, Clone, Copy, PartialEq, Eq)]")
    w.append("pub struct StructSpec {")
    w.append("    pub name: &'static str,")
    w.append("    pub fields: &'static [FieldSpec],")
    w.append(f"    /// 1-based start line in `{src['path']}`")
    w.append("    pub line: u32,")
    w.append("}")
    w.append("")
    for s in inv["structs"]:
        ident = s["name"].upper()
        w.append(f"/// `{s['name']}` — {src['path']}:{s['line_start']}-{s['line_end']}")
        w.append(f"pub const {ident}_FIELDS: &[FieldSpec] = &[")
        for f in s["fields"]:
            bits = f"Some({f['bits']})" if f["bits"] is not None else "None"
            arr = f"Some(\"{f['array']}\")" if f["array"] else "None"
            w.append(
                f'    FieldSpec {{ name: "{f["name"]}", c_type: "{f["c_type"]}", '
                f"bits: {bits}, array: {arr}, line: {f['line']} }},"
            )
        w.append("];")
    w.append("")
    w.append("/// Every object-model struct, in contract order.")
    w.append("pub const OBJECT_STRUCTS: &[StructSpec] = &[")
    for s in inv["structs"]:
        w.append(
            f'    StructSpec {{ name: "{s["name"]}", fields: {s["name"].upper()}_FIELDS, '
            f"line: {s['line_start']} }},"
        )
    w.append("];")
    w.append("")
    w.append("// ---- exported / inline function census ---------------------------------")
    w.append("#[derive(Debug, Clone, Copy, PartialEq, Eq)]")
    w.append("pub enum Linkage {")
    w.append("    /// `LEAN_EXPORT` prototype (symbol exported from the runtime)")
    w.append("    Export,")
    w.append("    /// `static inline` definition in `lean.h` (compiled into callers)")
    w.append("    Inline,")
    w.append("}")
    w.append("")
    w.append("#[derive(Debug, Clone, Copy, PartialEq, Eq)]")
    w.append("pub struct AbiParam {")
    w.append("    pub c_type: &'static str,")
    w.append("    pub name: &'static str,")
    w.append("    pub ownership: Ownership,")
    w.append("}")
    w.append("")
    w.append("#[derive(Debug, Clone, Copy, PartialEq, Eq)]")
    w.append("pub struct AbiFn {")
    w.append("    pub name: &'static str,")
    w.append("    pub linkage: Linkage,")
    w.append("    pub ret_c_type: &'static str,")
    w.append("    pub ret_ownership: Ownership,")
    w.append("    pub params: &'static [AbiParam],")
    w.append(f"    /// 1-based line in `{src['path']}`. Platform `#if` branches may")
    w.append("    /// declare the same name twice; rows are keyed by (name, line).")
    w.append("    pub line: u32,")
    w.append("}")
    w.append("")
    n_export = sum(1 for f in inv["functions"] if f["linkage"] == "export")
    n_inline = len(inv["functions"]) - n_export
    w.append(f"/// The full `lean.h` function census: {n_export} `LEAN_EXPORT` prototypes and")
    w.append(f"/// {n_inline} `static inline` definitions, sorted by (name, line).")
    w.append("pub static FUNCTION_CENSUS: &[AbiFn] = &[")
    for f in inv["functions"]:
        params = ", ".join(
            f'AbiParam {{ c_type: "{p["c_type"]}", name: "{p["name"]}", '
            f"ownership: Ownership::{rust_ownership(p['ownership'])} }}"
            for p in f["params"]
        )
        linkage = "Export" if f["linkage"] == "export" else "Inline"
        w.append(
            f'    AbiFn {{ name: "{f["name"]}", linkage: Linkage::{linkage}, '
            f'ret_c_type: "{f["ret_c_type"]}", '
            f"ret_ownership: Ownership::{rust_ownership(f['ret_ownership'])}, "
            f"params: &[{params}], line: {f['line']} }},"
        )
    w.append("];")
    w.append("")
    return "\n".join(w) + "\n"


def render_rust_boundary(inv: dict, digest: str) -> str:
    """The layout partition of the contract, re-rendered for `fln-unsafe-abi`.

    Everything is `pub(crate)`: the D3 scaffold guard (FLN-STRUCT-022) rejects
    bare `pub` items in boundary crates until the no-admission export covenant
    exists, and strict downward layering (FLN-STRUCT-007) forbids rank 2 from
    importing `fln-rt`'s rendering at rank 3. The function census is NOT
    re-rendered here — the boundary crate compiles against layouts, not the
    symbol census; the census stays single-sourced in `fln-rt::abi`.
    """
    pin = inv["pin"]
    src = inv["source"]
    w = []
    w.append("//! Marrow boundary-crate layout contract — **@generated** by `scripts/extract/gen_abi_contract.py`. DO NOT EDIT.")
    w.append("//!")
    w.append(f"//! Extracted from the pinned Reference header `{src['path']}`")
    w.append(f"//! ({pin['repo']} {pin['tag']}, commit {pin['commit']}).")
    w.append("//! Layout partition only (tags, layout constants, struct field tables);")
    w.append("//! the function census is single-sourced in `fln-rt::abi`. Rendered")
    w.append("//! `pub(crate)` for the D3 boundary crate; same inventory, same digest,")
    w.append("//! drift-checked together with the other three artifacts.")
    w.append("")
    w.append("// Generated tables are referenced from tests and layout asserts; items that")
    w.append("// are provenance-only (pin binding) may be unused in some build profiles.")
    w.append("#![allow(dead_code)]")
    w.append("")
    w.append("/// SHA-256 of `contracts/abi_inventory.json` this module was rendered from.")
    w.append(f'pub(crate) const INVENTORY_DIGEST: &str = "{digest}";')
    w.append("/// The Reference pin this contract is extracted from.")
    w.append(f'pub(crate) const PIN_TAG: &str = "{pin["tag"]}";')
    w.append(f'pub(crate) const PIN_COMMIT: &str = "{pin["commit"]}";')
    w.append("/// SHA-256 of the pinned `lean.h` these constants were derived from.")
    w.append(f'pub(crate) const LEAN_H_SHA256: &str = "{src["sha256"]}";')
    w.append("")
    w.append("// ---- object tags (lean.h tag block) ------------------------------------")
    for t in inv["tags"]:
        w.append(f"/// `#define {t['name']} {t['value']}` — {src['path']}:{t['line']}")
        w.append(f"pub(crate) const {const_name(t['name'])}: u8 = {t['value']};")
    w.append("")
    w.append("// ---- layout constants ---------------------------------------------------")
    for d in inv["layout"]:
        if "value" in d:
            w.append(f"/// `#define {d['name']}` — {src['path']}:{d['line']}")
            w.append(f"pub(crate) const {d['name'].removeprefix('LEAN_')}: usize = {d['value']};")
        else:
            w.append(f"/// `#define {d['name']} {d['expr']}` — {src['path']}:{d['line']} (expression; platform-dependent width)")
            w.append(f'pub(crate) const {d["name"].removeprefix("LEAN_")}_EXPR: &str = "{d["expr"]}";')
    w.append("")
    w.append("// ---- object layout tables ----------------------------------------------")
    w.append("/// One C struct field of the object model, with provenance.")
    w.append("#[derive(Debug, Clone, Copy, PartialEq, Eq)]")
    w.append("pub(crate) struct FieldSpec {")
    w.append("    pub(crate) name: &'static str,")
    w.append("    pub(crate) c_type: &'static str,")
    w.append("    /// bit width when the field is a C bitfield")
    w.append("    pub(crate) bits: Option<u8>,")
    w.append("    /// `Some(\"[]\")`/`Some(\"[N]\")` for array fields (flexible arrays are `[]`)")
    w.append("    pub(crate) array: Option<&'static str>,")
    w.append(f"    /// 1-based line in `{src['path']}`")
    w.append("    pub(crate) line: u32,")
    w.append("}")
    w.append("")
    w.append("#[derive(Debug, Clone, Copy, PartialEq, Eq)]")
    w.append("pub(crate) struct StructSpec {")
    w.append("    pub(crate) name: &'static str,")
    w.append("    pub(crate) fields: &'static [FieldSpec],")
    w.append(f"    /// 1-based start line in `{src['path']}`")
    w.append("    pub(crate) line: u32,")
    w.append("}")
    w.append("")
    for s in inv["structs"]:
        ident = s["name"].upper()
        w.append(f"/// `{s['name']}` — {src['path']}:{s['line_start']}-{s['line_end']}")
        w.append(f"pub(crate) const {ident}_FIELDS: &[FieldSpec] = &[")
        for f in s["fields"]:
            bits = f"Some({f['bits']})" if f["bits"] is not None else "None"
            arr = f"Some(\"{f['array']}\")" if f["array"] else "None"
            w.append(
                f'    FieldSpec {{ name: "{f["name"]}", c_type: "{f["c_type"]}", '
                f"bits: {bits}, array: {arr}, line: {f['line']} }},"
            )
        w.append("];")
    w.append("")
    w.append("/// Every object-model struct, in contract order.")
    w.append("pub(crate) const OBJECT_STRUCTS: &[StructSpec] = &[")
    for s in inv["structs"]:
        w.append(
            f'    StructSpec {{ name: "{s["name"]}", fields: {s["name"].upper()}_FIELDS, '
            f"line: {s['line_start']} }},"
        )
    w.append("];")
    w.append("")
    return "\n".join(w) + "\n"


def render_markdown(inv: dict, digest: str) -> str:
    pin = inv["pin"]
    src = inv["source"]
    w = []
    w.append("# ABI_CONTRACT.md — the `lean_object` ABI at the pin")
    w.append("")
    w.append("> **@generated** by `scripts/extract/gen_abi_contract.py` (Rule D5/D9, plan Appendix B). DO NOT EDIT.")
    w.append("> Layout constants are derived, never remembered; regenerate with the script.")
    w.append(">")
    # D5/D9: an artifact may not assert provenance its producer did not establish. Measured
    # for bead `franken_lean-6tqy`: this extractor verifies NONE of the three pin fields —
    # no tree identity is computed, and unlike its OLEAN sibling it never compares the tag or
    # the commit against the pinned toolchain. What it does establish is byte-identity between
    # the vendored `lean.h` and the installed pinned toolchain's own copy, which is a real
    # independent oracle and is stated as such rather than left to be inferred from the pin.
    w.append(f"> pin: `{pin['repo']}` `{pin['tag']}` commit `{pin['commit']}`")
    if pin["tree"]:
        w.append(f"> — tree `{pin['tree']}`")
    w.append("> — all three pin fields above are **transcribed from `SUITE.lock` and NOT")
    w.append(">   established by this extractor**: it verifies neither the tag, the commit,")
    w.append(">   nor the tree. Tree identity is verified by `scripts/verify_vendor_tree.sh`,")
    w.append(">   which the contract lanes run before extraction.")
    w.append("> — what this extractor **does** establish: the vendored source below is")
    w.append(">   byte-identical to the installed pinned toolchain's own copy of it, and the")
    w.append(">   extraction fails if they differ.")
    w.append(f"> source: `{src['path']}` ({src['lines']} lines, sha256 `{src['sha256']}`)")
    w.append(f"> inventory: `contracts/abi_inventory.json` sha256 `{digest}`")
    w.append(f"> rust: `crates/fln-rt/src/abi.rs` (rendered from the same inventory)")
    w.append(f"> rust (boundary): `crates/fln-unsafe-abi/src/contract.rs` (layout partition, `pub(crate)`, same inventory)")
    w.append("")
    w.append("Scope of this slice (bead franken_lean-53v): object tags, layout constants,")
    w.append("object-header and object-struct field layouts, ownership conventions, and the")
    w.append("full `lean.h` function census with per-parameter ownership classes. The")
    w.append("per-symbol status taxonomy (NativeSafe / RawPlatform / CompatWrapper /")
    w.append("ReferenceSemanticAdapter / Unsupported) is a reviewed **policy join** against")
    w.append("this census and lands with the Marrow implementation beads — no symbol below")
    w.append("is implicitly classified by its absence.")
    w.append("")
    w.append("## 1. Object tags")
    w.append("")
    w.append("| tag | value | provenance |")
    w.append("|---|---|---|")
    for t in inv["tags"]:
        w.append(f"| `{t['name']}` | {t['value']} | `{src['path']}:{t['line']}` |")
    w.append("")
    w.append("Constructor objects use tags `0..=LeanMaxCtorTag`; every value above is a")
    w.append("special object category.")
    w.append("")
    w.append("## 2. Layout constants")
    w.append("")
    w.append("| constant | value | provenance |")
    w.append("|---|---|---|")
    for d in inv["layout"]:
        val = str(d["value"]) if "value" in d else f"`{d['expr']}` (expression)"
        w.append(f"| `{d['name']}` | {val} | `{src['path']}:{d['line']}` |")
    w.append("")
    w.append("## 3. Ownership conventions")
    w.append("")
    w.append("| typedef | meaning | provenance |")
    w.append("|---|---|---|")
    for o in inv["ownership"]:
        w.append(f"| `{o['name']}` | {o['doc'] or '(see lean.h comment block)'} | `{src['path']}:{o['line']}` |")
    w.append("")
    w.append("The reference-count field `m_rc` encodes thread-state: `> 0` single-threaded,")
    w.append("`< 0` multi-threaded (atomic), `== 0` persistent (no RC; compacted regions).")
    w.append("")
    w.append("## 4. Object structs")
    w.append("")
    for s in inv["structs"]:
        w.append(f"### `{s['name']}` — `{src['path']}:{s['line_start']}-{s['line_end']}`")
        w.append("")
        w.append("| field | C type | bits | array | line |")
        w.append("|---|---|---|---|---|")
        for f in s["fields"]:
            bits = str(f["bits"]) if f["bits"] is not None else "—"
            arr = f"`{f['array']}`" if f["array"] else "—"
            w.append(f"| `{f['name']}` | `{f['c_type']}` | {bits} | {arr} | {f['line']} |")
        w.append("")
    w.append("## 5. Function census")
    w.append("")
    n_export = sum(1 for f in inv["functions"] if f["linkage"] == "export")
    n_inline = len(inv["functions"]) - n_export
    w.append(f"{n_export} `LEAN_EXPORT` prototypes; {n_inline} `static inline` definitions.")
    w.append("Ownership classes: `owned_arg`/`borrowed_arg`/`unique_arg` (`lean_obj_arg`/")
    w.append("`b_lean_obj_arg`/`u_lean_obj_arg`), `owned_res`/`borrowed_res`, `raw_object`")
    w.append("(bare `lean_object *`), `value` (non-object). Duplicate names arise from")
    w.append("platform `#if` branches and are intentional; rows are keyed by (name, line).")
    w.append("")
    w.append("| symbol | linkage | signature (ownership) | line |")
    w.append("|---|---|---|---|")
    for f in inv["functions"]:
        sig = ", ".join(
            (p["name"] + ": " if p["name"] else "") + p["ownership"]
            for p in f["params"]
        ) or "()"
        w.append(f"| `{f['name']}` | {f['linkage']} | ({sig}) -> {f['ret_ownership']} | {f['line']} |")
    w.append("")
    return "\n".join(w) + "\n"


def atomic_publish(path: Path, text: str) -> str:
    payload = text.encode("utf-8")
    if path.exists() and path.read_bytes() == payload:
        return "unchanged"
    candidate = path.with_name(path.name + ".candidate")
    try:
        with candidate.open("xb") as output:
            output.write(payload)
            output.flush()
            os.fsync(output.fileno())
    except FileExistsError:
        die(
            f"interrupted publication candidate exists: "
            f"{candidate.relative_to(ROOT)}"
        )
    except OSError as error:
        die(
            f"cannot write publication candidate "
            f"{candidate.relative_to(ROOT)}: {error}"
        )
    try:
        os.replace(candidate, path)
        directory_flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
        directory_fd = os.open(path.parent, directory_flags)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    except OSError as error:
        die(
            f"atomic publication failed for {path.relative_to(ROOT)}; "
            f"candidate state is retained when available: {error}"
        )
    return "published"


def main() -> int:
    arguments = sys.argv[1:]
    unknown = [argument for argument in arguments if argument != "--check"]
    if unknown:
        die(f"unknown arguments: {unknown}; supported usage is optional --check")
    check = "--check" in arguments
    inv = build_inventory()
    inventory_text = render_inventory(inv)
    target_layout_text = render_target_layout(inv)
    digest = hashlib.sha256(inventory_text.encode("utf-8")).hexdigest()
    outputs = [
        (INVENTORY_PATH, inventory_text),
        (TARGET_LAYOUT_PATH, target_layout_text),
        (CONTRACT_PATH, render_markdown(inv, digest)),
        (RUST_PATH, render_rust(inv, digest)),
        (BOUNDARY_RUST_PATH, render_rust_boundary(inv, digest)),
    ]
    if check:
        for path, want in outputs:
            candidate = path.with_name(path.name + ".candidate")
            if candidate.exists():
                print(
                    f"gen_abi_contract: DRIFT: "
                    f"{candidate.relative_to(ROOT)} exists",
                    file=sys.stderr,
                )
                return 1
            if not path.exists():
                print(f"gen_abi_contract: DRIFT: {path.relative_to(ROOT)} missing", file=sys.stderr)
                return 1
            have = path.read_text(encoding="utf-8")
            if have != want:
                for i, (hl, wl) in enumerate(
                    zip(have.splitlines(), want.splitlines()), start=1
                ):
                    if hl != wl:
                        print(
                            f"gen_abi_contract: DRIFT: {path.relative_to(ROOT)}:{i}\n"
                            f"  checked-in: {hl!r}\n  regenerated: {wl!r}",
                            file=sys.stderr,
                        )
                        break
                else:
                    print(
                        f"gen_abi_contract: DRIFT: {path.relative_to(ROOT)} length differs "
                        f"({len(have)} vs {len(want)} bytes)",
                        file=sys.stderr,
                    )
                return 1
        print(f"gen_abi_contract: check OK ({len(outputs)} artifacts, "
              f"{len(inv['functions'])} census rows, "
              f"{len(read_targets())} target layout rows, "
              f"inventory digest {digest[:16]}…)")
        return 0
    INVENTORY_PATH.parent.mkdir(parents=True, exist_ok=True)
    for path, text in outputs:
        action = atomic_publish(path, text)
        print(
            f"gen_abi_contract: {action} {path.relative_to(ROOT)} "
            f"({len(text)} bytes)"
        )
    print(f"gen_abi_contract: {len(inv['functions'])} census rows "
          f"({sum(1 for f in inv['functions'] if f['linkage'] == 'export')} export), "
          f"{len(read_targets())} target layout rows, "
          f"inventory digest {digest}")
    return 0


if __name__ == "__main__":
    hostile_python = sorted(name for name in os.environ if name.startswith("PYTHON"))
    if not all(
        (
            sys.flags.isolated,
            sys.flags.ignore_environment,
            sys.flags.no_site,
            sys.flags.no_user_site,
            sys.flags.safe_path,
        )
    ):
        print("gen_abi_contract: sealed_interpreter_unsealed_startup", file=sys.stderr)
        raise SystemExit(2)
    if hostile_python:
        print(
            "gen_abi_contract: sealed_interpreter_hostile_environment names="
            + ",".join(hostile_python),
            file=sys.stderr,
        )
        raise SystemExit(2)
    sys.exit(main())
