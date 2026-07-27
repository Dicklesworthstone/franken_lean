#!/usr/bin/env -S python3 -I -S
"""gen_olean_contract.py — D5/D9 contract extraction: the .olean/.ilean contract from the pin.

The law (plan Appendix B, bead franken_lean-53v): format constants are DERIVED,
never remembered. This checked-in script parses the PINNED Reference sources —
the olean writer/loader (`src/library/module.cpp`), the compactor
(`src/runtime/compact.{h,cpp}`), and the Lean-side module structures
(`src/Lean/Elab/Frontend.lean`, `src/Lean/Environment.lean`, `src/Lean/Setup.lean`,
`src/Lean/Server/References.lean`) — and renders five artifacts from ONE
canonical inventory, so they cannot disagree by construction:

  contracts/olean_inventory.json  — the canonical intermediate (schema fln-olean-contract/1)
  contracts/OLEAN_ILEAN_FORMAT.txt
                                  — exact rooted format facts and pinned-artifact observations
  OLEAN_CONTRACT.md               — the human contract, per-field provenance
  crates/fln-olean/src/format.rs  — the Rust constants module Grimoire compiles against
  crates/fln-rt/src/region_contract.rs
                                  — the Rust region-partition contract

Upstream sources are parsed as DATA (Oracle-Only Law D8); nothing executes.
Header offsets are computed from the generated target ABI table and verified
against the pin's own packing static_assert. Anchors to compactor internals are
FOUND by symbol search at extraction time, never hand-copied line numbers.

Usage:
  scripts/extract/gen_olean_contract.py           # (re)generate all artifacts atomically
  scripts/extract/gen_olean_contract.py --check   # byte-compare against checked-in
                                                  # artifacts; exit 1 on drift
"""

import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from urllib.parse import quote

ROOT = Path(__file__).resolve().parents[2]
VENDOR = ROOT / "vendor" / "lean4-src"
MODULE_CPP = VENDOR / "src" / "library" / "module.cpp"
COMPACT_CPP = VENDOR / "src" / "runtime" / "compact.cpp"
COMPACT_H = VENDOR / "src" / "runtime" / "compact.h"
ENVIRONMENT_LEAN = VENDOR / "src" / "Lean" / "Environment.lean"
SETUP_LEAN = VENDOR / "src" / "Lean" / "Setup.lean"
REFERENCES_LEAN = VENDOR / "src" / "Lean" / "Server" / "References.lean"
LSP_INTERNAL_LEAN = VENDOR / "src" / "Lean" / "Data" / "Lsp" / "Internal.lean"
COMPACTED_REGION_LEAN = VENDOR / "src" / "Lean" / "CompactedRegion.lean"
FRONTEND_LEAN = VENDOR / "src" / "Lean" / "Elab" / "Frontend.lean"
SUITE_LOCK = ROOT / "SUITE.lock"
ABI_TARGET_LAYOUT_PATH = ROOT / "contracts" / "ABI_TARGET_LAYOUT.txt"

INVENTORY_PATH = ROOT / "contracts" / "olean_inventory.json"
EXACT_FORMAT_PATH = ROOT / "contracts" / "OLEAN_ILEAN_FORMAT.txt"
CONTRACT_PATH = ROOT / "OLEAN_CONTRACT.md"
RUST_PATH = ROOT / "crates" / "fln-olean" / "src" / "format.rs"
REGION_RUST_PATH = ROOT / "crates" / "fln-rt" / "src" / "region_contract.rs"

SCHEMA = "fln-olean-contract/1"
EXACT_FORMAT_SCHEMA = "fln-olean-ilean-format/1"
EXACT_FORMAT_EXTRACTOR = "lean-format-source-and-pin-artifacts"
EXACT_FORMAT_EXTRACTOR_VERSION = "1"
MAX_ARTIFACT_FILES = 4_096
MAX_ILEAN_BYTES = 4 * 1024 * 1024
MAX_ILEAN_CORPUS_BYTES = 512 * 1024 * 1024

# Compactor anchors: (relative path, symbol regex, role). Line numbers are FOUND
# at extraction time by searching for the definition; drift moves them mechanically.
COMPACTOR_ANCHORS = [
    ("src/library/module.cpp", r"const size_t ALIGN = ", "region payload/base alignment"),
    ("src/runtime/compact.cpp", r"void object_compactor::insert_string", "string layout: header + inline UTF-8, no interior pointers"),
    ("src/runtime/compact.cpp", r"void object_compactor::insert_mpz", "bignum layout: limbs copied after the mpz object; one interior pointer rewritten"),
    ("src/runtime/compact.cpp", r"bool object_compactor::insert_closure", "closure layout (v3 only): m_fun offsets recorded for the trailer relocation table"),
    ("src/runtime/compact.cpp", r"object \* region_reader::fix_object_ptr", "load-side pointer fixup: address mapped back to buffer by base-address search"),
    ("src/runtime/compact.cpp", r"object \* region_reader::read\(\)", "load walk: mmap-at-base fast path, else sequential object walk with fixups"),
    ("src/runtime/compact.h", r"class LEAN_EXPORT object_compactor \{", "save-side compactor state"),
    ("src/runtime/compact.h", r"class LEAN_EXPORT region_reader \{", "load-side reader state"),
]


def die(msg: str) -> "NoReturn":  # noqa: F821 - documentation type only
    print(f"gen_olean_contract: FATAL: {msg}", file=sys.stderr)
    sys.exit(1)


def read_pin() -> dict:
    for line in SUITE_LOCK.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if line.startswith("reference "):
            fields = dict(p.split("=", 1) for p in line.split()[2:] if "=" in p)
            return {
                "repo": line.split()[1],
                "tag": fields["tag"],
                "commit": fields["commit"],
                "tree": fields.get("tree", ""),
            }
    die("SUITE.lock has no reference row")


def src_meta(path: Path) -> dict:
    text = path.read_text(encoding="utf-8")
    return {
        "path": str(path.relative_to(ROOT)),
        "sha256": hashlib.sha256(text.encode("utf-8")).hexdigest(),
        "lines": len(text.splitlines()),
    }


C_FIELD_RX = re.compile(
    r"^\s*(char|uint8_t|size_t)\s+(\w+)\s*(\[\s*(\d*)\s*\])?\s*(?:=[^;]*)?(;|=\s*$)"
)


def parse_olean_header(text: str, sizeof_size_t: int) -> dict:
    lines = text.splitlines()
    start = next(
        (i for i, line in enumerate(lines, 1) if "struct olean_header {" in line),
        None,
    )
    if start is None:
        die("struct olean_header not found in module.cpp")
    fields = []
    offset = 0
    magic = None
    i = start
    while i < len(lines):
        raw = lines[i]
        i += 1
        if raw.strip().startswith("};"):
            break
        m = C_FIELD_RX.match(raw)
        if not m:
            continue
        c_type, name, arr, arr_n = m.group(1), m.group(2), m.group(3), m.group(4)
        if arr is not None and arr_n == "":
            size = 0  # flexible array member
        elif arr is not None:
            size = int(arr_n) * (1 if c_type in ("char", "uint8_t") else sizeof_size_t)
        elif c_type in ("char", "uint8_t"):
            size = 1
        elif c_type == "size_t":
            size = sizeof_size_t
        else:
            die(f"unknown field type in olean_header: {raw.strip()!r}")
        if name == "marker":
            mm = re.search(r"\{([^}]*)\}", raw)
            if not mm:
                die("marker field has no initializer")
            magic = "".join(re.findall(r"'(.)'", mm.group(1)))
        fields.append({
            "name": name,
            "c_type": c_type + (arr.replace(" ", "") if arr else ""),
            "offset": offset,
            "size": size,
            "line": i,
        })
        offset += size
    if magic is None:
        die("olean magic not extracted")
    fixed_size = offset  # flexible member contributes 0
    # Verify against the pin's own packing static_assert.
    am = re.search(
        r"static_assert\(sizeof\(olean_header\) == ([0-9+\s]+)\+ sizeof\(size_t\)", text
    )
    if not am:
        die("olean_header packing static_assert not found")
    asserted = sum(int(x) for x in am.group(1).split("+") if x.strip()) + sizeof_size_t
    if asserted != fixed_size:
        die(f"header size mismatch: computed {fixed_size}, static_assert says {asserted}")
    return {"magic": magic, "size": fixed_size, "fields": fields, "line": start}


def parse_versions(text: str) -> dict:
    written = sorted(
        {int(m.group(1)) for m in re.finditer(r"header\.version = (\d+);", text)}
    )
    acc = re.search(r"header\.version != (\d+) && header\.version != (\d+)", text)
    if not written or not acc:
        die("olean version writer/acceptance sites not found in module.cpp")
    accepted = sorted({int(acc.group(1)), int(acc.group(2))})
    if written != accepted:
        die(f"written versions {written} differ from accepted versions {accepted}")
    line = text[:acc.start()].count("\n") + 1
    return {"accepted": accepted, "acceptance_line": line}


def parse_align(text: str) -> dict:
    m = re.search(r"const size_t ALIGN = 1LL<<(\d+);", text)
    if not m:
        die("region ALIGN constant not found in module.cpp")
    return {"value": 1 << int(m.group(1)), "line": text[:m.start()].count("\n") + 1}


LEAN_FIELD_RX = re.compile(r"^  (\w+)\s*:\s*(.+?)(?:\s*:=\s*(.+?))?\s*$")


def parse_lean_structure(path: Path, name: str) -> dict:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    start = next(
        (
            i
            for i, line in enumerate(lines, 1)
            if line.startswith(f"structure {name} ")
        ),
        None,
    )
    if start is None:
        die(f"structure {name} not found in {path.name}")
    fields = []
    in_doc = False
    i = start
    while i < len(lines):
        raw = lines[i]
        i += 1
        s = raw.strip()
        if in_doc:
            if s.endswith("-/"):
                in_doc = False
            continue
        if s.startswith("/--"):
            in_doc = not s.endswith("-/")
            continue
        if s.startswith("deriving") or (raw and not raw.startswith(" ")):
            break
        m = LEAN_FIELD_RX.match(raw)
        if m:
            fields.append({
                "name": m.group(1),
                "lean_type": m.group(2).strip(),
                "default": m.group(3).strip() if m.group(3) else None,
                "line": i,
            })
    if not fields:
        die(f"structure {name} parsed with zero fields")
    return {
        "name": name,
        "path": str(path.relative_to(ROOT)),
        "line": start,
        "fields": fields,
    }


def find_anchors() -> list[dict]:
    anchors = []
    for rel, symbol_rx, role in COMPACTOR_ANCHORS:
        path = ROOT / "vendor" / "lean4-src" / rel
        lines = path.read_text(encoding="utf-8").splitlines()
        hits = [i for i, line in enumerate(lines, 1) if re.search(symbol_rx, line)]
        if len(hits) != 1:
            die(f"anchor {symbol_rx!r} in {rel}: expected exactly 1 hit, got {len(hits)}")
        anchors.append({
            "path": f"vendor/lean4-src/{rel}",
            "line": hits[0],
            "symbol": symbol_rx.replace("\\", ""),
            "role": role,
        })
    return anchors


def read_targets() -> list[str]:
    targets = []
    for raw in SUITE_LOCK.read_text(encoding="utf-8").splitlines():
        line = raw.split("#", 1)[0].strip()
        if not line.startswith("target "):
            continue
        tokens = line.split()
        if len(tokens) != 2 or not re.fullmatch(r"[A-Za-z0-9_.-]+", tokens[1]):
            die(f"SUITE.lock target row is not canonical: {raw!r}")
        if tokens[1] in targets:
            die(f"SUITE.lock repeats target {tokens[1]!r}")
        targets.append(tokens[1])
    if not targets:
        die("SUITE.lock has no certified target rows")
    return targets


def parse_abi_targets() -> list[dict]:
    """Read opaque target facts from b7n8's mechanically extracted ABI table.

    Target triples remain in SUITE.lock. This parser joins by positional
    `target:NNNN` keys and never republishes a triple or pin value.
    """
    text = ABI_TARGET_LAYOUT_PATH.read_text(encoding="utf-8")
    if not text.endswith("\n") or "\r" in text:
        die("contracts/ABI_TARGET_LAYOUT.txt is not canonical LF text")
    lines = text.splitlines()
    if len(lines) < 6 or lines[0] != "schema fln-abi-target-layout/1":
        die("contracts/ABI_TARGET_LAYOUT.txt has the wrong or missing schema")
    if lines[1] != "extractor lean-h-clang-layout version=1":
        die("contracts/ABI_TARGET_LAYOUT.txt has an unknown extractor")
    count_match = re.fullmatch(r"target-count ([0-9]+)", lines[3])
    if not count_match:
        die("contracts/ABI_TARGET_LAYOUT.txt has no canonical target-count row")
    expected_targets = read_targets()
    if int(count_match.group(1)) != len(expected_targets):
        die(
            "ABI target matrix does not match SUITE.lock: "
            f"{count_match.group(1)} vs {len(expected_targets)}"
        )
    target_rx = re.compile(
        r"target (target:[0-9]{4}) abi-class=([a-z0-9-]+) "
        r"data-model=([a-z0-9]+) endianness=(little|big) "
        r"pointer-bits=([0-9]+) size-t-bits=([0-9]+) "
        r"char-bits=([0-9]+) int-bits=([0-9]+) "
        r"unsigned-bits=([0-9]+) long-bits=([0-9]+) "
        r"long-long-bits=([0-9]+) max-align-bytes=([0-9]+)"
    )
    targets = []
    for line in lines:
        match = target_rx.fullmatch(line)
        if not match:
            continue
        key, abi_class, model, endian, *numbers = match.groups()
        expected_key = f"target:{len(targets) + 1:04}"
        if key != expected_key:
            die(f"ABI target key {key!r} is not the expected {expected_key!r}")
        widths = [int(value) for value in numbers]
        target = {
            "key": key,
            "abi_class": abi_class,
            "data_model": model,
            "endianness": endian,
            "pointer_bits": widths[0],
            "size_t_bits": widths[1],
            "char_bits": widths[2],
            "int_bits": widths[3],
            "unsigned_bits": widths[4],
            "long_bits": widths[5],
            "long_long_bits": widths[6],
            "max_align_bytes": widths[7],
        }
        if target["size_t_bits"] % 8 != 0 or target["char_bits"] != 8:
            die(f"ABI target {key} has a non-byte size_t or non-8-bit byte")
        targets.append(target)
    if len(targets) != len(expected_targets):
        die(
            "ABI target table target-row count differs from its header: "
            f"{len(targets)} vs {len(expected_targets)}"
        )
    return targets


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
        toolchain / "bin" / "lean",
        toolchain / "lib" / "lean" / "Init.olean",
        toolchain / "lib" / "lean" / "Init.ilean",
    ]
    missing = [str(path) for path in required if not path.is_file()]
    if missing:
        die(
            "pinned Reference toolchain is incomplete; local extraction requires "
            f"{toolchain}: missing {missing}"
        )
    return toolchain


def verify_toolchain_identity(toolchain: Path, pin: dict, targets: list[str]) -> int:
    command = [str(toolchain / "bin" / "lean"), "--version"]
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
            text=True,
            capture_output=True,
            timeout=30,
            check=False,
            env=environment,
        )
    except subprocess.TimeoutExpired:
        die("pinned Reference `lean --version` timed out after 30 seconds")
    if completed.returncode != 0:
        die(
            "pinned Reference `lean --version` failed: "
            f"{(completed.stderr or completed.stdout).strip()}"
        )
    version = completed.stdout.strip()
    match = re.fullmatch(
        r"Lean \(version ([^,]+), ([A-Za-z0-9_.-]+), "
        r"commit ([0-9a-f]{40}), Release\)",
        version,
    )
    if not match:
        die(f"pinned Reference reports an unknown version shape: {version!r}")
    observed_version, observed_target, observed_commit = match.groups()
    if observed_version != pin["tag"].removeprefix("v") or observed_commit != pin["commit"]:
        die(
            "pinned Reference binary identity differs from SUITE.lock: "
            f"version={observed_version} commit={observed_commit}"
        )
    try:
        return targets.index(observed_target)
    except ValueError:
        die(
            "pinned Reference binary target is absent from SUITE.lock: "
            f"{observed_target!r}"
        )


def unique_line(path: Path, pattern: str) -> int:
    regex = re.compile(pattern)
    hits = [
        index
        for index, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1)
        if regex.search(line)
    ]
    if len(hits) != 1:
        die(
            f"{path.relative_to(ROOT)} anchor {pattern!r}: "
            f"expected exactly 1 hit, got {len(hits)}"
        )
    return hits[0]


def extract_inductive_constructors(path: Path, name: str) -> list[dict]:
    lines = path.read_text(encoding="utf-8").splitlines()
    start = next(
        (
            index
            for index, line in enumerate(lines, 1)
            if line.startswith(f"inductive {name}")
        ),
        None,
    )
    if start is None:
        die(f"inductive {name} not found in {path.relative_to(ROOT)}")
    constructors = []
    in_doc = False
    for index in range(start, len(lines)):
        raw = lines[index]
        stripped = raw.strip()
        if in_doc:
            if stripped.endswith("-/"):
                in_doc = False
            continue
        if stripped.startswith("/--"):
            in_doc = not stripped.endswith("-/")
            continue
        match = re.match(r"^\s*\|\s+([A-Za-z«»_][A-Za-z0-9«»_]*)\b(.*)$", raw)
        if match:
            constructors.append(
                {
                    "name": match.group(1).replace("«", "").replace("»", ""),
                    "signature": match.group(2).strip(),
                    "line": index + 1,
                }
            )
            continue
        if constructors and stripped and not raw.startswith(" "):
            break
    if not constructors:
        die(f"inductive {name} parsed with zero constructors")
    return constructors


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


def fact_token(value: str) -> str:
    token = quote(value, safe="._:/,;=+()[]{}*-")
    if not token or any(character.isspace() for character in token):
        die(f"format fact did not produce one canonical token: {value!r}")
    return token


def source_locator(path: Path, line: int) -> str:
    if line <= 0:
        die(f"invalid source line {line} for {path}")
    return f"{path.relative_to(ROOT)}:{line}"


def format_row(
    key: str,
    category: str,
    fact: str,
    source: str,
) -> dict:
    if not re.fullmatch(r"[A-Za-z0-9_.:/-]+", key):
        die(f"format row key is not canonical: {key!r}")
    if not re.fullmatch(r"[a-z0-9-]+", category):
        die(f"format row category is not canonical: {category!r}")
    if not source or any(character.isspace() for character in source):
        die(f"format source locator is not canonical: {source!r}")
    return {
        "key": key,
        "category": category,
        "fact": fact_token(fact),
        "source": source,
    }


def json_kind(value: object) -> str:
    if value is None:
        return "null"
    if isinstance(value, bool):
        return "boolean"
    if isinstance(value, (int, float)):
        return "number"
    if isinstance(value, str):
        return "string"
    if isinstance(value, list):
        return "array"
    if isinstance(value, dict):
        return "object"
    die(f"unrecognized JSON value type: {type(value).__name__}")


def is_compact_json(payload: bytes) -> bool:
    """Return whether JSON text has no formatting whitespace outside strings."""
    in_string = False
    escaped = False
    for byte in payload:
        if in_string:
            if escaped:
                escaped = False
            elif byte == ord("\\"):
                escaped = True
            elif byte == ord('"'):
                in_string = False
        elif byte == ord('"'):
            in_string = True
        elif byte in b" \t\r\n":
            return False
    return not in_string and not escaped


def build_inventory() -> dict:
    module_text = MODULE_CPP.read_text(encoding="utf-8")
    abi_targets = parse_abi_targets()
    sizeof_size_t = abi_targets[0]["size_t_bits"] // 8
    ilean = parse_lean_structure(REFERENCES_LEAN, "Ilean")
    version_field = next(f for f in ilean["fields"] if f["name"] == "version")
    if not version_field["default"] or not version_field["default"].isdigit():
        die(f"Ilean.version has no integer default: {version_field}")
    return {
        "schema": SCHEMA,
        "pin": read_pin(),
        "sources": [
            src_meta(p)
            for p in (
                MODULE_CPP, COMPACT_CPP, COMPACT_H,
                ENVIRONMENT_LEAN, SETUP_LEAN, REFERENCES_LEAN,
            )
        ],
        "sizeof_size_t": sizeof_size_t,
        "header": parse_olean_header(module_text, sizeof_size_t),
        "versions": parse_versions(module_text),
        "region_align": parse_align(module_text),
        "module_data": parse_lean_structure(ENVIRONMENT_LEAN, "ModuleData"),
        "import_": parse_lean_structure(SETUP_LEAN, "Import"),
        "ilean": ilean,
        "ilean_version": int(version_field["default"]),
        "compactor_anchors": find_anchors(),
    }


def hash_corpus_record(digest: object, path: str, payload: bytes) -> None:
    path_bytes = path.encode("utf-8")
    digest.update(len(path_bytes).to_bytes(8, "little"))  # type: ignore[attr-defined]
    digest.update(path_bytes)  # type: ignore[attr-defined]
    digest.update(len(payload).to_bytes(8, "little"))  # type: ignore[attr-defined]
    digest.update(payload)  # type: ignore[attr-defined]


def inspect_ilean_corpus(toolchain: Path, expected_epoch: int) -> dict:
    root = toolchain / "lib" / "lean"
    paths = sorted(root.rglob("*.ilean"), key=lambda path: path.relative_to(root).as_posix())
    if not paths or len(paths) > MAX_ARTIFACT_FILES:
        die(
            "pinned ILEAN corpus file count is outside the bounded range "
            f"1..={MAX_ARTIFACT_FILES}: {len(paths)}"
        )
    digest = hashlib.sha256(b"fln.ilean-artifact-corpus/1\0")
    total_bytes = 0
    largest_bytes = 0
    nonempty_references = 0
    nonempty_decls = 0
    reference_rows = 0
    decl_rows = 0
    reference_constructor_counts = {"c": 0, "f": 0}
    import_flag_shapes = set()
    expected_keys = {"version", "module", "directImports", "references", "decls"}
    expected_kinds = {
        "version": "number",
        "module": "string",
        "directImports": "array",
        "references": "object",
        "decls": "object",
    }
    observed_key_order = None
    witness_sha256 = None
    witness_size = None
    witness_module = None
    witness = None
    for path in paths:
        relative = path.relative_to(root).as_posix()
        size = path.stat().st_size
        if size > MAX_ILEAN_BYTES:
            die(
                f"pinned ILEAN artifact {relative} is {size} bytes; "
                f"bounded maximum is {MAX_ILEAN_BYTES}"
            )
        total_bytes += size
        if total_bytes > MAX_ILEAN_CORPUS_BYTES:
            die(
                "pinned ILEAN corpus exceeds the bounded total "
                f"{MAX_ILEAN_CORPUS_BYTES} bytes"
            )
        largest_bytes = max(largest_bytes, size)
        payload = path.read_bytes()
        if len(payload) != size:
            die(f"pinned ILEAN artifact changed while reading: {relative}")
        if (
            not payload.startswith(b"{")
            or not payload.endswith(b"}")
            or not is_compact_json(payload)
        ):
            die(
                f"pinned ILEAN artifact {relative} is not one compact JSON object "
                "without trailing bytes"
            )
        try:
            value = json.loads(payload)
        except (UnicodeDecodeError, json.JSONDecodeError) as error:
            die(f"pinned ILEAN artifact is not strict JSON: {relative}: {error}")
        if not isinstance(value, dict) or set(value) != expected_keys:
            die(
                f"pinned ILEAN artifact {relative} top-level keys differ: "
                f"{list(value) if isinstance(value, dict) else type(value).__name__}"
            )
        kinds = {key: json_kind(item) for key, item in value.items()}
        if kinds != expected_kinds:
            die(f"pinned ILEAN artifact {relative} field kinds differ: {kinds}")
        if value["version"] != expected_epoch:
            die(
                f"pinned ILEAN artifact {relative} has epoch "
                f"{value['version']!r}, expected {expected_epoch}"
            )
        key_order = tuple(value)
        if observed_key_order is None:
            observed_key_order = key_order
        elif key_order != observed_key_order:
            die(
                f"pinned ILEAN producer key order differs in {relative}: "
                f"{key_order} vs {observed_key_order}"
            )
        for index, import_info in enumerate(value["directImports"]):
            if (
                not isinstance(import_info, list)
                or len(import_info) != 4
                or not isinstance(import_info[0], str)
                or any(not isinstance(flag, bool) for flag in import_info[1:])
            ):
                die(
                    f"pinned ILEAN artifact {relative} directImports[{index}] "
                    "is not [string,bool,bool,bool]"
                )
            import_flag_shapes.add(tuple(import_info[1:]))
        nonempty_references += bool(value["references"])
        nonempty_decls += bool(value["decls"])
        reference_rows += len(value["references"])
        decl_rows += len(value["decls"])
        for encoded_ident in value["references"]:
            if (
                not encoded_ident.startswith("{")
                or not encoded_ident.endswith("}")
                or not is_compact_json(encoded_ident.encode("utf-8"))
            ):
                die(
                    f"pinned ILEAN artifact {relative} reference key is not compact "
                    f"JSON: {encoded_ident!r}"
                )
            try:
                ident = json.loads(encoded_ident)
            except json.JSONDecodeError as error:
                die(
                    f"pinned ILEAN artifact {relative} has a non-JSON reference key: "
                    f"{encoded_ident!r}: {error}"
                )
            if not isinstance(ident, dict) or len(ident) != 1:
                die(
                    f"pinned ILEAN artifact {relative} reference key is not one "
                    f"RefIdent constructor: {encoded_ident!r}"
                )
            constructor, fields = next(iter(ident.items()))
            expected_fields = {"c": {"m", "n"}, "f": {"m", "i"}}.get(constructor)
            if (
                expected_fields is None
                or not isinstance(fields, dict)
                or set(fields) != expected_fields
                or any(not isinstance(field, str) for field in fields.values())
            ):
                die(
                    f"pinned ILEAN artifact {relative} reference key has an "
                    f"unknown compact shape: {encoded_ident!r}"
                )
            reference_constructor_counts[constructor] += 1
        file_digest = hashlib.sha256(payload).digest()
        hash_corpus_record(digest, relative, file_digest)
        if relative == "Init.ilean":
            witness_sha256 = file_digest.hex()
            witness_size = size
            witness_module = value["module"]
            witness = value
    if (
        witness_sha256 is None
        or witness_size is None
        or witness_module != "Init"
        or witness is None
    ):
        die("pinned ILEAN corpus has no valid lib/lean/Init.ilean witness")
    if observed_key_order != tuple(sorted(expected_keys)):
        die(
            "pinned ILEAN producer no longer emits canonical lexical object-key order: "
            f"{observed_key_order}"
        )
    return {
        "file_count": len(paths),
        "total_bytes": total_bytes,
        "largest_bytes": largest_bytes,
        "nonempty_references": nonempty_references,
        "nonempty_decls": nonempty_decls,
        "reference_rows": reference_rows,
        "decl_rows": decl_rows,
        "reference_constructor_counts": reference_constructor_counts,
        "import_flag_shapes": sorted(import_flag_shapes),
        "key_order": list(observed_key_order),
        "root": f"sha256:{digest.hexdigest()}",
        "witness_sha256": witness_sha256,
        "witness_size": witness_size,
        "witness": witness,
    }


def decode_ascii_field(data: bytes, field: dict, header: dict) -> str:
    """Decode one ASCII header field, or refuse in a typed way.

    A bare ``.decode("ascii")`` here raises ``UnicodeDecodeError`` as an unhandled traceback.
    That is not a corrupt-file path: it is what a *revised upstream header* looks like, because
    a layout whose offsets have moved reads real artifact bytes through the wrong window. The
    doctrine is that malformed input must not panic and that a panic is never a user diagnostic
    (FL-INV-07, "inconclusive is not rejected"), so this refuses through ``die`` — the same typed
    idiom the truncation branch of ``decode_olean_header`` already uses.
    """
    try:
        return data.decode("ascii")
    except UnicodeDecodeError:
        die(
            f"OLEAN header field {field['name']!r} at offset {field['offset']} "
            f"(field size {field['size']}, header size {header['size']}) is not ASCII: "
            f"{data.hex()} — the checked-in layout does not describe these bytes, which is "
            "what a revised upstream header looks like; re-extract against the pin"
        )


def decode_olean_header(payload: bytes, header: dict, target: dict) -> dict:
    if len(payload) < header["size"]:
        die(
            f"OLEAN artifact is truncated before its {header['size']}-byte fixed header"
        )
    byteorder = target["endianness"]
    values = {}
    for field in header["fields"]:
        start = field["offset"]
        end = start + field["size"]
        data = payload[start:end]
        if field["name"] == "marker":
            values["marker"] = decode_ascii_field(data, field, header)
        elif field["name"] in ("version", "flags"):
            values[field["name"]] = data[0]
        elif field["name"] in ("lean_version", "githash"):
            values[field["name"]] = decode_ascii_field(
                data.rstrip(b"\0"), field, header
            )
        elif field["name"] == "base_addr":
            values["base_addr"] = int.from_bytes(data, byteorder=byteorder)
    return values


def inspect_olean_corpus(
    toolchain: Path,
    pin: dict,
    target: dict,
    header: dict,
    accepted_versions: list[int],
) -> dict:
    root = toolchain / "lib" / "lean"
    paths = sorted(root.rglob("*.olean"), key=lambda path: path.relative_to(root).as_posix())
    if not paths or len(paths) > MAX_ARTIFACT_FILES:
        die(
            "pinned OLEAN corpus file count is outside the bounded range "
            f"1..={MAX_ARTIFACT_FILES}: {len(paths)}"
        )
    digest = hashlib.sha256(b"fln.olean-header-corpus/1\0")
    observed_versions = set()
    observed_flags = set()
    largest_bytes = 0
    witness_sha256 = None
    witness_size = None
    for path in paths:
        relative = path.relative_to(root).as_posix()
        size = path.stat().st_size
        largest_bytes = max(largest_bytes, size)
        with path.open("rb") as artifact:
            payload = artifact.read(header["size"])
        decoded = decode_olean_header(payload, header, target)
        if decoded["marker"] != header["magic"]:
            die(f"pinned OLEAN artifact {relative} has invalid magic")
        if decoded["version"] not in accepted_versions:
            die(
                f"pinned OLEAN artifact {relative} has unsupported epoch "
                f"{decoded['version']}"
            )
        if decoded["lean_version"] != pin["tag"].removeprefix("v"):
            die(
                f"pinned OLEAN artifact {relative} version field differs: "
                f"{decoded['lean_version']!r}"
            )
        if decoded["githash"] != pin["commit"]:
            die(
                f"pinned OLEAN artifact {relative} commit field differs: "
                f"{decoded['githash']!r}"
            )
        observed_versions.add(decoded["version"])
        observed_flags.add(decoded["flags"])
        record = payload + size.to_bytes(8, "little")
        hash_corpus_record(digest, relative, record)
        if relative == "Init.olean":
            full_payload = path.read_bytes()
            witness_sha256 = hashlib.sha256(full_payload).hexdigest()
            witness_size = len(full_payload)
    if witness_sha256 is None or witness_size is None:
        die("pinned OLEAN corpus has no lib/lean/Init.olean witness")
    return {
        "file_count": len(paths),
        "largest_bytes": largest_bytes,
        "observed_versions": sorted(observed_versions),
        "observed_flags": sorted(observed_flags),
        "root": f"sha256:{digest.hexdigest()}",
        "witness_sha256": witness_sha256,
        "witness_size": witness_size,
    }


def build_ilean_rows(inv: dict, toolchain: Path) -> list[dict]:
    rows = []
    corpus = inspect_ilean_corpus(toolchain, inv["ilean_version"])
    rows.append(
        format_row(
            "artifact-corpus",
            "artifact-corpus",
            "files={file_count};bytes={total_bytes};largest={largest_bytes};"
            "nonempty-references={nonempty_references};nonempty-decls={nonempty_decls};"
            "reference-rows={reference_rows};decl-rows={decl_rows};"
            "framing=single-compact-object;"
            "root={root};witness=lib/lean/Init.ilean;"
            "witness-bytes={witness_size};witness-sha256={witness_sha256}".format(**corpus),
            "toolchain:lib/lean",
        )
    )
    rows.append(
        format_row(
            "artifact-key-order",
            "encoding",
            f"lexical={','.join(corpus['key_order'])}",
            "toolchain:lib/lean/Init.ilean",
        )
    )
    flag_shapes = ",".join(
        "".join("1" if flag else "0" for flag in shape)
        for shape in corpus["import_flag_shapes"]
    )
    rows.append(
        format_row(
            "artifact-import-shapes",
            "encoding",
            f"boolean-tuples={flag_shapes}",
            "toolchain:lib/lean",
        )
    )
    constructor_counts = corpus["reference_constructor_counts"]
    rows.append(
        format_row(
            "artifact-reference-constructors",
            "encoding",
            f"c={constructor_counts['c']};f={constructor_counts['f']};"
            "keys=strict-compact-json",
            "toolchain:lib/lean",
        )
    )

    ilean = inv["ilean"]
    rows.append(
        format_row(
            "epoch",
            "epoch",
            f"supported={inv['ilean_version']};unknown=reject",
            source_locator(
                ROOT / ilean["path"],
                next(field["line"] for field in ilean["fields"] if field["name"] == "version"),
            ),
        )
    )
    witness = corpus["witness"]
    for ordinal, field in enumerate(ilean["fields"]):
        if field["name"] not in witness:
            die(f"Init.ilean witness lacks source field {field['name']!r}")
        rows.append(
            format_row(
                f"field:{ordinal:04}",
                "field",
                f"ordinal={ordinal};name={field['name']};"
                f"lean-type={field['lean_type']};json-kind={json_kind(witness[field['name']])};"
                "required=true",
                source_locator(ROOT / ilean["path"], field["line"]),
            )
        )
    deriving_line = unique_line(REFERENCES_LEAN, r"^\s*deriving FromJson, ToJson$")
    rows.append(
        format_row(
            "top-level-codec",
            "encoding",
            "from-json=derived;to-json=derived;container=object",
            source_locator(REFERENCES_LEAN, deriving_line),
        )
    )
    producer_line = unique_line(
        FRONTEND_LEAN,
        r"IO\.FS\.writeFile ileanFileName \$ Json\.compress \$ toJson ilean",
    )
    rows.append(
        format_row(
            "producer",
            "producer",
            "value=ToJson(Ilean);renderer=Json.compress;sink=IO.FS.writeFile;"
            "trailing-newline=false",
            source_locator(FRONTEND_LEAN, producer_line),
        )
    )

    import_info = parse_lean_structure(LSP_INTERNAL_LEAN, "ImportInfo")
    import_to_json_line = unique_line(
        LSP_INTERNAL_LEAN,
        r"toJson info := Json\.arr #\[info\.module, info\.isPrivate, info\.isAll, info\.isMeta\]",
    )
    expected_import_fields = ["module", "isPrivate", "isAll", "isMeta"]
    if [field["name"] for field in import_info["fields"]] != expected_import_fields:
        die("ImportInfo declaration order differs from its compact JSON serializer")
    for ordinal, field in enumerate(import_info["fields"]):
        json_type = "string" if ordinal == 0 else "boolean"
        rows.append(
            format_row(
                f"import-field:{ordinal:04}",
                "import-field",
                f"ordinal={ordinal};name={field['name']};json-kind={json_type}",
                source_locator(LSP_INTERNAL_LEAN, field["line"]),
            )
        )
    rows.append(
        format_row(
            "import-codec",
            "encoding",
            "container=array;length=4;order=module,isPrivate,isAll,isMeta;other-shape=reject",
            source_locator(LSP_INTERNAL_LEAN, import_to_json_line),
        )
    )

    decl_info = parse_lean_structure(LSP_INTERNAL_LEAN, "DeclInfo")
    if len(decl_info["fields"]) != 8:
        die(f"DeclInfo must have exactly 8 positional fields, got {len(decl_info['fields'])}")
    decl_length_line = unique_line(LSP_INTERNAL_LEAN, r"if xs\.size != 8 then")
    for ordinal, field in enumerate(decl_info["fields"]):
        rows.append(
            format_row(
                f"decl-field:{ordinal:04}",
                "decl-field",
                f"ordinal={ordinal};name={field['name']};json-kind=number",
                source_locator(LSP_INTERNAL_LEAN, field["line"]),
            )
        )
    rows.append(
        format_row(
            "decl-codec",
            "encoding",
            "container=array;length=8;other-length=reject",
            source_locator(LSP_INTERNAL_LEAN, decl_length_line),
        )
    )
    decls_line = unique_line(
        LSP_INTERNAL_LEAN,
        r"toJson m := Json\.mkObj <\| m\.toList\.map fun \(declName, info\)",
    )
    rows.append(
        format_row(
            "decls-codec",
            "decls",
            "container=object;key=declaration-name-string;value=DeclInfo;"
            "order=Std.TreeMap-String-Ord",
            source_locator(LSP_INTERNAL_LEAN, decls_line),
        )
    )

    ref_constructors = extract_inductive_constructors(
        LSP_INTERNAL_LEAN, "RefIdentJsonRepr"
    )
    for ordinal, constructor in enumerate(ref_constructors):
        json_shape = {
            "c": "object(c:object(m:string,n:string))",
            "f": "object(f:object(m:string,i:string))",
        }.get(constructor["name"])
        if json_shape is None:
            die(
                "RefIdentJsonRepr gained an unknown constructor: "
                f"{constructor['name']!r}"
            )
        rows.append(
            format_row(
                f"ref-ident-constructor:{ordinal:04}",
                "ref-ident-constructor",
                f"ordinal={ordinal};name={constructor['name']};"
                f"signature={constructor['signature']};json-shape={json_shape}",
                source_locator(LSP_INTERNAL_LEAN, constructor["line"]),
            )
        )
    module_refs_line = unique_line(
        LSP_INTERNAL_LEAN,
        r"toJson m := Json\.mkObj <\| m\.toList\.map fun \(ident, info\)",
    )
    rows.append(
        format_row(
            "module-refs-codec",
            "module-refs",
            "container=object;key=Json.compress(RefIdentJsonRepr);value=RefInfo;"
            "order=Std.TreeMap-RefIdent-Ord",
            source_locator(LSP_INTERNAL_LEAN, module_refs_line),
        )
    )
    location_length_line = unique_line(
        LSP_INTERNAL_LEAN, r"a\.size ≠ 4 ∧ a\.size ≠ 5"
    )
    rows.append(
        format_row(
            "location-codec",
            "location",
            "container=array;lengths=4,5;slot4=optional-parent-decl;other-length=reject",
            source_locator(LSP_INTERNAL_LEAN, location_length_line),
        )
    )
    ref_info_line = unique_line(
        LSP_INTERNAL_LEAN, r'\("definition", toJson \$ i\.definition\?'
    )
    rows.append(
        format_row(
            "ref-info-codec",
            "encoding",
            "container=object;keys=definition,usages;"
            "definition=null-or-location;usages=array-of-location",
            source_locator(LSP_INTERNAL_LEAN, ref_info_line),
        )
    )

    load_start = unique_line(
        REFERENCES_LEAN, r"^def load \(path : System\.FilePath\) : IO Ilean := do$"
    )
    load_end = unique_line(REFERENCES_LEAN, r"^end Ilean$")
    load_body = "\n".join(
        REFERENCES_LEAN.read_text(encoding="utf-8").splitlines()[load_start - 1 : load_end]
    )
    if re.search(r"\bilean\.version\b|version\s*(?:!=|==|<|>)", load_body):
        die("Ilean.load gained an epoch comparison; update validation semantics")
    for ordinal, (fact, pattern) in enumerate(
        [
            ("read=FS.readFile", r"let content ← FS\.readFile path"),
            ("parse=Json.parse", r"Json\.parse content >>= fromJson\?"),
            ("decode=FromJson", r"Json\.parse content >>= fromJson\?"),
            ("error=throwServerError", r"throwServerError"),
        ]
    ):
        rows.append(
            format_row(
                f"loader:{ordinal:04}",
                "loader",
                f"ordinal={ordinal};{fact}",
                source_locator(REFERENCES_LEAN, unique_line(REFERENCES_LEAN, pattern)),
            )
        )
    rows.append(
        format_row(
            "validation-epoch",
            "validation",
            "upstream-loader=decoded-not-compared;contract-consumer=reject-unknown",
            source_locator(REFERENCES_LEAN, load_start),
        )
    )
    return rows


def build_olean_rows(
    inv: dict,
    toolchain: Path,
    target: dict,
    include_artifact_corpus: bool,
) -> list[dict]:
    rows = []
    module_text = MODULE_CPP.read_text(encoding="utf-8")
    compact_text = COMPACT_CPP.read_text(encoding="utf-8")
    size_t_bytes = target["size_t_bits"] // 8
    header = parse_olean_header(module_text, size_t_bytes)
    if include_artifact_corpus:
        corpus = inspect_olean_corpus(
            toolchain,
            inv["pin"],
            target,
            header,
            inv["versions"]["accepted"],
        )
        rows.append(
            format_row(
                "artifact-corpus",
                "artifact-corpus",
                "files={file_count};largest={largest_bytes};versions={versions};flags={flags};"
                "root={root};witness=lib/lean/Init.olean;"
                "witness-bytes={witness_size};witness-sha256={witness_sha256}".format(
                    file_count=corpus["file_count"],
                    largest_bytes=corpus["largest_bytes"],
                    versions=",".join(map(str, corpus["observed_versions"])),
                    flags=",".join(map(str, corpus["observed_flags"])),
                    root=corpus["root"],
                    witness_size=corpus["witness_size"],
                    witness_sha256=corpus["witness_sha256"],
                ),
                "toolchain:lib/lean",
            )
        )
        observed_flags = corpus["observed_flags"]
    else:
        rows.append(
            format_row(
                "artifact-corpus",
                "artifact-corpus",
                "state=unavailable;reason=pinned-toolchain-host-mismatch",
                "toolchain:unavailable",
            )
        )
        observed_flags = []
    rows.append(
        format_row(
            "target",
            "target",
            f"abi-class={target['abi_class']};endianness={target['endianness']};"
            f"pointer-bits={target['pointer_bits']};size-t-bits={target['size_t_bits']}",
            f"contracts/ABI_TARGET_LAYOUT.txt:{target['key']}",
        )
    )
    rows.append(
        format_row(
            "header",
            "header",
            f"magic={header['magic']};size-bytes={header['size']};"
            f"field-count={len(header['fields'])}",
            source_locator(MODULE_CPP, header["line"]),
        )
    )
    for ordinal, field in enumerate(header["fields"]):
        rows.append(
            format_row(
                f"header-field:{ordinal:04}",
                "header-field",
                f"ordinal={ordinal};name={field['name']};c-type={field['c_type']};"
                f"offset={field['offset']};size={field['size']}",
                source_locator(MODULE_CPP, field["line"]),
            )
        )

    writer_sites = []
    for match in re.finditer(r"header\.version = ([0-9]+);", module_text):
        writer_sites.append(
            (
                int(match.group(1)),
                module_text[: match.start()].count("\n") + 1,
            )
        )
    if sorted(version for version, _ in writer_sites) != inv["versions"]["accepted"]:
        die("OLEAN writer version sites differ from loader acceptance")
    for version, line in sorted(writer_sites):
        rows.append(
            format_row(
                f"version:{version:04}",
                "version",
                f"epoch={version};writer=present;loader=accepted",
                source_locator(MODULE_CPP, line),
            )
        )

    section_specs = [
        (2, 0, "header", f"bytes={header['size']}", r"header\.version = 2;"),
        (2, 1, "compacted-data", "length=remaining-file", r"compactor\.size\(\) - file_offset - sizeof\(olean_header\)"),
        (3, 0, "header", f"bytes={header['size']}", r"header\.version = 3;"),
        (3, 1, "data-size", f"scalar=size_t;bits={target['size_t_bits']}", r"out\.write\(reinterpret_cast<char const \*>\(&data_size\)"),
        (3, 2, "compacted-data", "length=data-size", r"out\.write\(static_cast<char const \*>\(compactor\.data\(\)\) \+ data_offset, data_size\)"),
        (3, 3, "closure-count", "scalar=uint32;bits=32", r"out\.write\(reinterpret_cast<char const \*>\(&num_closure_offsets\)"),
        (3, 4, "closure-offsets", "scalar=uint64;bits=64;count=closure-count", r"out\.write\(reinterpret_cast<char const \*>\(file_offsets\.data\(\)\)"),
        (3, 5, "library-count", "scalar=uint32;bits=32", r"out\.write\(reinterpret_cast<char const \*>\(&n\), sizeof\(n\)\)"),
        (3, 6, "library-rows", f"tuple=size_t,uint32,bytes;size-t-bits={target['size_t_bits']}", r"out\.write\(reinterpret_cast<char const \*>\(&lib\.base_addr\)"),
    ]
    for version, ordinal, name, fact, pattern in section_specs:
        rows.append(
            format_row(
                f"section:v{version}:{ordinal:04}",
                "section",
                f"ordinal={ordinal};epoch={version};name={name};{fact}",
                source_locator(MODULE_CPP, unique_line(MODULE_CPP, pattern)),
            )
        )
    rows.append(
        format_row(
            "scalar-encoding",
            "scalar",
            f"endianness={target['endianness']};encoding=native-target;"
            f"size-t-bits={target['size_t_bits']};u32-bits=32;u64-bits=64",
            source_locator(
                MODULE_CPP,
                unique_line(
                    MODULE_CPP,
                    r"out\.write\(reinterpret_cast<char const \*>\(&data_size\)",
                ),
            ),
        )
    )
    rows.append(
        format_row(
            "flags",
            "flag",
            "bit0=bignum-encoding;bits1-7=reserved;"
            f"artifact-values={','.join(map(str, observed_flags)) or 'unavailable'}",
            source_locator(MODULE_CPP, unique_line(MODULE_CPP, r"^\s*uint8_t flags =$")),
        )
    )

    dispatch = []
    for line_number, line in enumerate(compact_text.splitlines(), 1):
        match = re.search(
            r"case (Lean[A-Za-z]+):\s+(.+?);(?:\s+break;)?\s*$", line
        )
        if match and 480 <= line_number <= 520:
            dispatch.append((match.group(1), match.group(2).strip(), line_number))
    if len(dispatch) != 11:
        die(f"expected 11 compactor dispatch cases, found {len(dispatch)}")
    for ordinal, (tag, action, line) in enumerate(dispatch):
        rows.append(
            format_row(
                f"compactor-dispatch:{ordinal:04}",
                "compactor",
                f"ordinal={ordinal};tag={tag};action={action}",
                source_locator(COMPACT_CPP, line),
            )
        )
    default_line = unique_line(
        COMPACT_CPP, r"default:\s+r = insert_constructor\(curr\); break;"
    )
    rows.append(
        format_row(
            f"compactor-dispatch:{len(dispatch):04}",
            "compactor",
            f"ordinal={len(dispatch)};tag=constructor;action=insert_constructor(curr)",
            source_locator(COMPACT_CPP, default_line),
        )
    )
    for key, fact, pattern in [
        (
            "sharing:pointer-identity",
            "mechanism=m_obj_table;identity=source-pointer;result=saved-offset",
            r"m_obj_table\.find\(o\)",
        ),
        (
            "sharing:structural",
            "mechanism=m_max_sharing_table;key=object-bytes;result=reused-offset",
            r"m_max_sharing_table->m_table\.find\(k\)",
        ),
        (
            "sharing:cross-part",
            "mechanism=retained-compactor;tables=persist-across-save-calls",
            r"Keeping the full compactor alive preserves both",
        ),
        (
            "sharing:root",
            f"position=first-word;width-bits={target['pointer_bits']};encoding=logical-address",
            r"\*root = to_offset\(o\);",
        ),
        (
            "sharing:null-sentinel",
            "value=max-size-t-minus-one;parity=even;scalar-collision=false",
            r"g_null_offset = reinterpret_cast<object_offset>",
        ),
    ]:
        path = MODULE_CPP if "cross-part" in key else COMPACT_CPP
        rows.append(
            format_row(
                key,
                "sharing",
                fact,
                source_locator(path, unique_line(path, pattern)),
            )
        )
    for key, fact, path, pattern in [
        (
            "relocation:self",
            "saved=base-address-plus-buffer-offset;load=physical-buffer-plus-offset",
            COMPACT_CPP,
            r"return reinterpret_cast<object\*>\(static_cast<char\*>\(m_begin\)",
        ),
        (
            "relocation:dependency",
            "lookup=sorted-base-range;overlap=reject",
            COMPACT_CPP,
            r"dep regions have overlapping `base_addr` ranges",
        ),
        (
            "relocation:closure-offset",
            "offset=data-relative-m_fun;scalar=uint64",
            MODULE_CPP,
            r"file_offsets\.push_back\(static_cast<uint64_t>",
        ),
        (
            "relocation:closure-library",
            "identity=opaque-loader-id;mapping=saved-base-to-current-base",
            MODULE_CPP,
            r"library required for closure relocation is not loaded",
        ),
    ]:
        rows.append(
            format_row(
                key,
                "relocation",
                fact,
                source_locator(path, unique_line(path, pattern)),
            )
        )

    levels = extract_inductive_constructors(ENVIRONMENT_LEAN, "OLeanLevel")
    suffixes = {"exported": "base", "server": ".server", "private": ".private"}
    if [level["name"] for level in levels] != list(suffixes):
        die(f"OLeanLevel order differs from filename policy: {levels}")
    for ordinal, level in enumerate(levels):
        suffix_pattern = {
            "exported": r"\| \.exported => base$",
            "server": r'\| \.server\s+=> base\.addExtension "server"$',
            "private": r'\| \.private\s+=> base\.addExtension "private"$',
        }[level["name"]]
        suffix_line = unique_line(ENVIRONMENT_LEAN, suffix_pattern)
        rows.append(
            format_row(
                f"level:{ordinal:04}",
                "level",
                f"ordinal={ordinal};name={level['name']};suffix={suffixes[level['name']]}",
                source_locator(ENVIRONMENT_LEAN, suffix_line),
            )
        )

    for ordinal, field in enumerate(inv["module_data"]["fields"]):
        rows.append(
            format_row(
                f"module-field:{ordinal:04}",
                "module-field",
                f"ordinal={ordinal};name={field['name']};lean-type={field['lean_type']}",
                source_locator(ROOT / inv["module_data"]["path"], field["line"]),
            )
        )
    opaque_line = unique_line(
        ENVIRONMENT_LEAN, r"^opaque EnvExtensionEntrySpec : NonemptyType"
    )
    rows.append(
        format_row(
            "extension-entry",
            "extension",
            "payload=opaque;container=Array(Name,Array(EnvExtensionEntry));"
            "empty-extensions=omitted;unknown-payload=preserve",
            source_locator(ENVIRONMENT_LEAN, opaque_line),
        )
    )
    parts_line = unique_line(ENVIRONMENT_LEAN, r"saveModuleDataParts env\.mainModule #\[")
    rows.append(
        format_row(
            "extension-level-order",
            "extension",
            "parts=exported,server,private;order=exact",
            source_locator(ENVIRONMENT_LEAN, parts_line),
        )
    )
    for key, fact, pattern in [
        (
            "validation:short-header",
            "class=corrupt;outcome=reject-invalid-header",
            r"read_size != sizeof\(header\)",
        ),
        (
            "validation:magic",
            "class=corrupt;outcome=reject-invalid-header",
            r"memcmp\(header\.marker, default_header\.marker",
        ),
        (
            "validation:epoch",
            "class=epoch-mismatch;accepted=2,3;unknown=reject-incompatible-header",
            r"header\.version != 2 && header\.version != 3",
        ),
        (
            "validation:flags",
            "class=unsupported-encoding;outcome=reject-incompatible-header",
            r"header\.flags != default_header\.flags",
        ),
        (
            "validation:pin",
            "class=pin-mismatch;mode=conditional-LEAN_CHECK_OLEAN_VERSION;"
            "outcome=reject-incompatible-header",
            r"strncmp\(header\.githash, LEAN_GITHASH",
        ),
    ]:
        rows.append(
            format_row(
                key,
                "validation",
                fact,
                source_locator(MODULE_CPP, unique_line(MODULE_CPP, pattern)),
            )
        )
    return rows


def render_exact_format(inv: dict) -> str:
    pin = inv["pin"]
    targets = read_targets()
    abi_targets = parse_abi_targets()
    toolchain = reference_toolchain(pin)
    host_target_index = verify_toolchain_identity(toolchain, pin, targets)
    sources = [
        ("abi-target-layout", ABI_TARGET_LAYOUT_PATH, "derived-target-layout"),
        ("compact-cpp", COMPACT_CPP, "SUITE.lock:reference"),
        ("compact-h", COMPACT_H, "SUITE.lock:reference"),
        ("compacted-region-lean", COMPACTED_REGION_LEAN, "SUITE.lock:reference"),
        ("environment-lean", ENVIRONMENT_LEAN, "SUITE.lock:reference"),
        ("frontend-lean", FRONTEND_LEAN, "SUITE.lock:reference"),
        ("lsp-internal-lean", LSP_INTERNAL_LEAN, "SUITE.lock:reference"),
        ("module-cpp", MODULE_CPP, "SUITE.lock:reference"),
        ("references-lean", REFERENCES_LEAN, "SUITE.lock:reference"),
        ("setup-lean", SETUP_LEAN, "SUITE.lock:reference"),
    ]
    output = [
        f"schema {EXACT_FORMAT_SCHEMA}",
        f"extractor {EXACT_FORMAT_EXTRACTOR} version={EXACT_FORMAT_EXTRACTOR_VERSION}",
    ]
    for key, path, authority in sorted(sources):
        payload = path.read_bytes()
        output.append(
            f"source {key} path={path.relative_to(ROOT)} authority={authority} "
            f"sha256={hashlib.sha256(payload).hexdigest()}"
        )
    output.append(f"target-count {len(abi_targets)}")

    sections = [("ilean", "abi-class=none", build_ilean_rows(inv, toolchain))]
    for index, target in enumerate(abi_targets):
        name = f"olean:{target['key']}"
        rows = build_olean_rows(
            inv,
            toolchain,
            target,
            include_artifact_corpus=index == host_target_index,
        )
        sections.append((name, f"abi-class={target['abi_class']}", rows))

    for name, classification, rows in sections:
        rows = sorted(rows, key=lambda row: row["key"].encode("utf-8"))
        if len({row["key"] for row in rows}) != len(rows):
            die(f"exact format section {name} contains duplicate row keys")
        block = [f"section {name} {classification} row-count={len(rows)}"]
        for row in rows:
            block.append(
                f"row {row['key']} category={row['category']} "
                f"fact={row['fact']} source={row['source']}"
            )
        block_bytes = ("\n".join(block) + "\n").encode("utf-8")
        output.extend(block)
        output.append(
            f"section-root {name} "
            f"{labeled_fnv(fnv1a64_fields('fln.olean-ilean-format.section-root/1', [block_bytes]))}"
        )

    prefix = "\n".join(output) + "\n"
    inventory_root = labeled_fnv(
        fnv1a64_fields(
            "fln.olean-ilean-format.inventory-root/1",
            [prefix.encode("utf-8")],
        )
    )
    return prefix + f"inventory-root {inventory_root}\n"


# ---------------------------------------------------------------- rendering

def render_inventory(inv: dict) -> str:
    return json.dumps(inv, indent=1, sort_keys=True, ensure_ascii=True) + "\n"


def render_rust(inv: dict, digest: str) -> str:
    pin = inv["pin"]
    hdr = inv["header"]
    mod_rel = "vendor/lean4-src/src/library/module.cpp"
    w = []
    w.append("//! Grimoire's `.olean`/`.ilean` format constants — **@generated** by")
    w.append("//! `scripts/extract/gen_olean_contract.py`. DO NOT EDIT.")
    w.append("//!")
    w.append(f"//! Extracted from the pinned Reference ({pin['repo']} {pin['tag']},")
    w.append(f"//! commit {pin['commit']}): the olean writer/loader, the")
    w.append("//! compactor, and the Lean-side module structures. The extraction law (plan")
    w.append("//! Appendix B, Rule D5/D9): format constants are derived, never remembered.")
    w.append("//! Header offsets follow the LP64 law (`size_t` = 8 bytes) and are verified")
    w.append("//! against the pin's own packing `static_assert` at extraction time.")
    w.append("")
    w.append("/// SHA-256 of `contracts/olean_inventory.json`, the canonical inventory this")
    w.append("/// module was rendered from.")
    w.append(f'pub const INVENTORY_DIGEST: &str = "{digest}";')
    w.append(f'pub const PIN_TAG: &str = "{pin["tag"]}";')
    w.append(f'pub const PIN_COMMIT: &str = "{pin["commit"]}";')
    w.append("")
    if not hdr["magic"].isascii() or not hdr["magic"].isalnum():
        die(f"magic not a plain ASCII token: {hdr['magic']!r}")
    w.append(f"/// `.olean` magic bytes — {mod_rel}:{hdr['line']}")
    w.append(f'pub const OLEAN_MAGIC: [u8; {len(hdr["magic"])}] = *b"{hdr["magic"]}";')
    w.append("/// Fixed header size in bytes on LP64 (verified against the pin's static_assert).")
    w.append(f"pub const OLEAN_HEADER_SIZE: usize = {hdr['size']};")
    versions = ", ".join(str(v) for v in inv["versions"]["accepted"])
    w.append(f"/// Format versions the pinned loader accepts — {mod_rel}:{inv['versions']['acceptance_line']}")
    w.append(f"pub const OLEAN_ACCEPTED_VERSIONS: &[u8] = &[{versions}];")
    w.append(f"/// Region payload/base alignment — {mod_rel}:{inv['region_align']['line']}")
    w.append(f"pub const REGION_ALIGN: usize = {inv['region_align']['value']};")
    w.append(f"/// `.ilean` JSON format version — {inv['ilean']['path']}:{inv['ilean']['fields'][0]['line']}")
    w.append(f"pub const ILEAN_VERSION: u64 = {inv['ilean_version']};")
    w.append("")
    w.append("/// One fixed header field: byte offset, byte size, and provenance.")
    w.append("#[derive(Debug, Clone, Copy, PartialEq, Eq)]")
    w.append("pub struct HeaderField {")
    w.append("    pub name: &'static str,")
    w.append("    pub c_type: &'static str,")
    w.append("    pub offset: usize,")
    w.append("    /// 0 marks the trailing flexible array member")
    w.append("    pub size: usize,")
    w.append(f"    /// 1-based line in `{mod_rel}`")
    w.append("    pub line: u32,")
    w.append("}")
    w.append("")
    w.append(f"/// The on-disk `olean_header` — {mod_rel}:{hdr['line']}, in file order.")
    w.append("pub const OLEAN_HEADER_FIELDS: &[HeaderField] = &[")
    for f in hdr["fields"]:
        w.append(
            f'    HeaderField {{ name: "{f["name"]}", c_type: "{f["c_type"]}", '
            f"offset: {f['offset']}, size: {f['size']}, line: {f['line']} }},"
        )
    w.append("];")
    w.append("")
    w.append("/// One Lean-side structure field (name, type, default) with provenance.")
    w.append("#[derive(Debug, Clone, Copy, PartialEq, Eq)]")
    w.append("pub struct LeanField {")
    w.append("    pub name: &'static str,")
    w.append("    pub lean_type: &'static str,")
    w.append("    pub default: Option<&'static str>,")
    w.append("    pub line: u32,")
    w.append("}")
    w.append("")
    for key, ident in (("module_data", "MODULE_DATA"), ("import_", "IMPORT"), ("ilean", "ILEAN")):
        s = inv[key]
        w.append(f"/// `structure {s['name']}` — {s['path']}:{s['line']}, in declaration order")
        w.append("/// (the compacted object graph is the wire format; field order is layout).")
        w.append(f"pub const {ident}_FIELDS: &[LeanField] = &[")
        for f in s["fields"]:
            default = f'Some("{f["default"]}")' if f["default"] else "None"
            w.append(
                f'    LeanField {{ name: "{f["name"]}", lean_type: "{f["lean_type"]}", '
                f"default: {default}, line: {f['line']} }},"
            )
        w.append("];")
        w.append("")
    return "\n".join(w) + "\n"


def render_rust_region_partition(inv: dict, digest: str) -> str:
    """The region-envelope partition re-rendered for `fln-rt` (bead fln-wgp).

    Marrow's region engine (§6.4) shares the compacted-region code path with
    the Grimoire codec, and its tests parse the olean envelope to reach the
    region payload — but fln-rt (rank 3) cannot import fln-olean's rendering
    (rank 5, strictly-downward layering), so the envelope subset is rendered
    twice from the same inventory: magic, header size/fields, accepted
    versions, and the region alignment law. `pub(crate)`: the partition is
    engine-internal; the codec surface stays fln-olean's.
    """
    pin = inv["pin"]
    hdr = inv["header"]
    mod_rel = "vendor/lean4-src/src/library/module.cpp"
    w = []
    w.append("//! Marrow's region-envelope contract partition — **@generated** by")
    w.append("//! `scripts/extract/gen_olean_contract.py`. DO NOT EDIT.")
    w.append("//!")
    w.append(f"//! Extracted from the pinned Reference ({pin['repo']} {pin['tag']},")
    w.append(f"//! commit {pin['commit']}). Envelope subset only (magic, header")
    w.append("//! fields, accepted versions, region alignment); the full format")
    w.append("//! contract is single-sourced in `fln-olean::format`. Rendered")
    w.append("//! `pub(crate)` for the region engine; same inventory, same digest,")
    w.append("//! drift-checked together with the other three artifacts.")
    w.append("")
    w.append("// Provenance-only items may be unused in some build profiles.")
    w.append("#![allow(dead_code)]")
    w.append("")
    w.append("/// SHA-256 of `contracts/olean_inventory.json` this partition was rendered from.")
    w.append(f'pub(crate) const INVENTORY_DIGEST: &str = "{digest}";')
    w.append(f'pub(crate) const PIN_TAG: &str = "{pin["tag"]}";')
    w.append(f'pub(crate) const PIN_COMMIT: &str = "{pin["commit"]}";')
    w.append("")
    w.append(f"/// `.olean` magic bytes — {mod_rel}:{hdr['line']}")
    w.append(f'pub(crate) const OLEAN_MAGIC: [u8; {len(hdr["magic"])}] = *b"{hdr["magic"]}";')
    w.append("/// Fixed header size in bytes on LP64 (verified against the pin's static_assert).")
    w.append(f"pub(crate) const OLEAN_HEADER_SIZE: usize = {hdr['size']};")
    versions = ", ".join(str(v) for v in inv["versions"]["accepted"])
    w.append(f"/// Format versions the pinned loader accepts — {mod_rel}:{inv['versions']['acceptance_line']}")
    w.append(f"pub(crate) const OLEAN_ACCEPTED_VERSIONS: &[u8] = &[{versions}];")
    w.append(f"/// Region payload/base alignment — {mod_rel}:{inv['region_align']['line']}")
    w.append(f"pub(crate) const REGION_ALIGN: usize = {inv['region_align']['value']};")
    w.append("")
    w.append("/// One fixed header field: byte offset, byte size, and provenance.")
    w.append("#[derive(Debug, Clone, Copy, PartialEq, Eq)]")
    w.append("pub(crate) struct HeaderField {")
    w.append("    pub(crate) name: &'static str,")
    w.append("    pub(crate) c_type: &'static str,")
    w.append("    pub(crate) offset: usize,")
    w.append("    /// 0 marks the trailing flexible array member")
    w.append("    pub(crate) size: usize,")
    w.append(f"    /// 1-based line in `{mod_rel}`")
    w.append("    pub(crate) line: u32,")
    w.append("}")
    w.append("")
    w.append(f"/// The on-disk `olean_header` — {mod_rel}:{hdr['line']}, in file order.")
    w.append("pub(crate) const OLEAN_HEADER_FIELDS: &[HeaderField] = &[")
    for f in hdr["fields"]:
        w.append(
            f'    HeaderField {{ name: "{f["name"]}", c_type: "{f["c_type"]}", '
            f"offset: {f['offset']}, size: {f['size']}, line: {f['line']} }},"
        )
    w.append("];")
    w.append("")
    return "\n".join(w) + "\n"


def render_markdown(inv: dict, digest: str) -> str:
    pin = inv["pin"]
    hdr = inv["header"]
    mod_rel = "vendor/lean4-src/src/library/module.cpp"
    w = []
    w.append("# OLEAN_CONTRACT.md — the `.olean`/`.ilean` format at the pin")
    w.append("")
    w.append("> **@generated** by `scripts/extract/gen_olean_contract.py` (Rule D5/D9, plan Appendix B). DO NOT EDIT.")
    w.append("> Format constants are derived, never remembered; regenerate with the script.")
    w.append(">")
    # D5/D9: an artifact may not assert provenance its producer did not establish. This
    # extractor DOES establish the tag and the commit — they are cross-checked against the
    # pinned Reference binary's own `lean --version` and against every pinned `.olean`
    # artifact's `lean_version` and `githash` fields. It does NOT establish the tree: no tree
    # identity is computed anywhere in this file (bead `franken_lean-6tqy`). Rendering all
    # three in one voice let a transcribed field read as a verified one.
    w.append(f"> pin: `{pin['repo']}` `{pin['tag']}` commit `{pin['commit']}`")
    w.append("> — tag and commit are **established here**: cross-checked against the pinned")
    w.append(">   Reference binary's `lean --version` and against every pinned `.olean`")
    w.append(">   artifact's `lean_version` and `githash` fields.")
    if pin["tree"]:
        w.append(f"> — tree `{pin['tree']}` is **transcribed from `SUITE.lock` and NOT")
        w.append(">   established by this extractor**. What is bound here is *content*: a")
        w.append(">   sha256 is recorded below for each source read, so any change to those")
        w.append(">   files is caught — while a staged tree differing from the pin in a file")
        w.append(">   this extractor does not read is not. Tree identity is verified by")
        w.append(">   `scripts/verify_vendor_tree.sh`, which the contract lanes run before")
        w.append(">   extraction; this line records the pin, it does not attest to it.")
    w.append(f"> inventory: `contracts/olean_inventory.json` sha256 `{digest}`")
    w.append("> rust: `crates/fln-olean/src/format.rs` (rendered from the same inventory)")
    w.append(">")
    w.append("> sources:")
    for s in inv["sources"]:
        w.append(f"> - `{s['path']}` ({s['lines']} lines, sha256 `{s['sha256']}`)")
    w.append("")
    w.append("## 1. The fixed header")
    w.append("")
    w.append(f"Magic `\"{hdr['magic']}\"`; fixed size **{hdr['size']} bytes** on LP64")
    w.append(f"(`size_t` = {inv['sizeof_size_t']}; offsets computed under that law and verified")
    w.append(f"against the pin's packing `static_assert`). Struct at `{mod_rel}:{hdr['line']}`.")
    w.append("")
    w.append("| offset | size | field | C type | provenance |")
    w.append("|---|---|---|---|---|")
    for f in hdr["fields"]:
        size = str(f["size"]) if f["size"] else "flexible"
        w.append(f"| {f['offset']} | {size} | `{f['name']}` | `{f['c_type']}` | `{mod_rel}:{f['line']}` |")
    w.append("")
    accepted = inv["versions"]["accepted"]
    w.append(f"Accepted versions: **{', '.join(map(str, accepted))}**")
    w.append(f"(`{mod_rel}:{inv['versions']['acceptance_line']}`). v2 is the default format:")
    w.append("compacted data begins immediately at the end of the fixed header. v3")
    w.append("(`CompactedRegion.save (allowClosures := true)`) appends length-prefixed")
    w.append("sections after the header: `size_t data_size`, the compacted data, a")
    w.append("`uint32 num_closure_offsets` + `uint64` array of data-relative closure")
    w.append("`m_fun` offsets, and a `uint32 num_libs` relocation table of")
    w.append("`(size_t base_addr, uint32 id_len, char id[id_len])` rows (documented in the")
    w.append("header comment block itself). `flags` bit 0 records whether persisted bignums")
    w.append("use the GMP encoding; bits 1–7 are reserved.")
    w.append("")
    w.append(f"Region payload and base address are aligned to **{inv['region_align']['value']}**")
    w.append(f"bytes (`{mod_rel}:{inv['region_align']['line']}`). The file is mmapped at")
    w.append("`base_addr` when possible; every interior pointer was rewritten at save time to")
    w.append("`buffer_offset + base_addr`, so the mmap fast path needs no fixup at all, and")
    w.append("the fallback walk relocates pointer-by-pointer.")
    w.append("")
    w.append("## 2. The compacted object graph")
    w.append("")
    w.append("There is no field-by-field serializer: the Lean object graph **is** the wire")
    w.append("format. The compactor copies objects into a contiguous buffer (8-byte aligned,")
    w.append("zero-initialized), dedups by pointer identity and structural sharing, stores")
    w.append("the root as the first word of the data region, and rejects external objects.")
    w.append("Mechanically-found anchors into the pinned implementation:")
    w.append("")
    w.append("| anchor | role |")
    w.append("|---|---|")
    for a in inv["compactor_anchors"]:
        w.append(f"| `{a['path']}:{a['line']}` (`{a['symbol']}`) | {a['role']} |")
    w.append("")
    w.append("## 3. Lean-side module structures")
    w.append("")
    for key in ("module_data", "import_", "ilean"):
        s = inv[key]
        w.append(f"### `structure {s['name']}` — `{s['path']}:{s['line']}`")
        w.append("")
        w.append("| # | field | type | default | line |")
        w.append("|---|---|---|---|---|")
        for i, f in enumerate(s["fields"]):
            default = f"`{f['default']}`" if f["default"] else "—"
            w.append(f"| {i} | `{f['name']}` | `{f['lean_type']}` | {default} | {f['line']} |")
        w.append("")
    w.append("`.ilean` is a JSON document (`FromJson`/`ToJson`), format version")
    w.append(f"**{inv['ilean_version']}**. `EnvExtensionEntry` payloads are opaque by")
    w.append("construction — each extension defines its own encoding via `exportEntriesFn`;")
    w.append("Grimoire preserves unknown payloads losslessly and never guesses (bead")
    w.append("franken_lean-y24 consumes this contract).")
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
            "interrupted publication candidate exists: "
            f"{candidate.relative_to(ROOT)}"
        )
    except OSError as error:
        die(
            "cannot write publication candidate "
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
    output_paths = [
        INVENTORY_PATH,
        EXACT_FORMAT_PATH,
        CONTRACT_PATH,
        RUST_PATH,
        REGION_RUST_PATH,
    ]
    if check:
        for path in output_paths:
            candidate = path.with_name(path.name + ".candidate")
            if candidate.exists():
                print(
                    "gen_olean_contract: DRIFT: "
                    f"{candidate.relative_to(ROOT)} exists",
                    file=sys.stderr,
                )
                return 1
    inv = build_inventory()
    inventory_text = render_inventory(inv)
    exact_format_text = render_exact_format(inv)
    digest = hashlib.sha256(inventory_text.encode("utf-8")).hexdigest()
    outputs = [
        (INVENTORY_PATH, inventory_text),
        (EXACT_FORMAT_PATH, exact_format_text),
        (CONTRACT_PATH, render_markdown(inv, digest)),
        (RUST_PATH, render_rust(inv, digest)),
        (REGION_RUST_PATH, render_rust_region_partition(inv, digest)),
    ]
    if check:
        for path, want in outputs:
            if not path.exists():
                print(f"gen_olean_contract: DRIFT: {path.relative_to(ROOT)} missing", file=sys.stderr)
                return 1
            have = path.read_text(encoding="utf-8")
            if have != want:
                for i, (hl, wl) in enumerate(
                    zip(have.splitlines(), want.splitlines()), start=1
                ):
                    if hl != wl:
                        print(
                            f"gen_olean_contract: DRIFT: {path.relative_to(ROOT)}:{i}\n"
                            f"  checked-in: {hl!r}\n  regenerated: {wl!r}",
                            file=sys.stderr,
                        )
                        break
                else:
                    print(
                        f"gen_olean_contract: DRIFT: {path.relative_to(ROOT)} length differs "
                        f"({len(have)} vs {len(want)} bytes)",
                        file=sys.stderr,
                    )
                return 1
        print(f"gen_olean_contract: check OK ({len(outputs)} artifacts, "
              f"header size {inv['header']['size']}, "
              f"inventory digest {digest[:16]}…)")
        return 0
    INVENTORY_PATH.parent.mkdir(parents=True, exist_ok=True)
    for path, text in outputs:
        action = atomic_publish(path, text)
        print(
            f"gen_olean_contract: {action} {path.relative_to(ROOT)} "
            f"({len(text)} bytes)"
        )
    print(f"gen_olean_contract: header {inv['header']['size']} bytes, versions "
          f"{inv['versions']['accepted']}, align {inv['region_align']['value']}, "
          f"ilean v{inv['ilean_version']}, inventory digest {digest}")
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
        print("gen_olean_contract: sealed_interpreter_unsealed_startup", file=sys.stderr)
        raise SystemExit(2)
    if hostile_python:
        print(
            "gen_olean_contract: sealed_interpreter_hostile_environment names="
            + ",".join(hostile_python),
            file=sys.stderr,
        )
        raise SystemExit(2)
    sys.exit(main())
