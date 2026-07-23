#!/usr/bin/env python3
"""gen_olean_contract.py — D5/D9 contract extraction: the .olean/.ilean contract from the pin.

The law (plan Appendix B, bead franken_lean-53v): format constants are DERIVED,
never remembered. This checked-in script parses the PINNED Reference sources —
the olean writer/loader (`src/library/module.cpp`), the compactor
(`src/runtime/compact.{h,cpp}`), and the Lean-side module structures
(`src/Lean/Environment.lean`, `src/Lean/Setup.lean`,
`src/Lean/Server/References.lean`) — and renders three artifacts from ONE
canonical inventory, so they cannot disagree by construction:

  contracts/olean_inventory.json  — the canonical intermediate (schema fln-olean-contract/1)
  OLEAN_CONTRACT.md               — the human contract, per-field provenance
  crates/fln-olean/src/format.rs  — the Rust constants module Grimoire compiles against

Upstream sources are parsed as DATA (Oracle-Only Law D8); nothing executes.
Header offsets are computed under the LP64 law (size_t = 8 bytes) and verified
against the pin's own packing static_assert. Anchors to compactor internals are
FOUND by symbol search at extraction time, never hand-copied line numbers.

Usage:
  scripts/extract/gen_olean_contract.py           # (re)generate all three artifacts
  scripts/extract/gen_olean_contract.py --check   # byte-compare against checked-in
                                                  # artifacts; exit 2 on drift
"""

import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
VENDOR = ROOT / "vendor" / "lean4-src"
MODULE_CPP = VENDOR / "src" / "library" / "module.cpp"
COMPACT_CPP = VENDOR / "src" / "runtime" / "compact.cpp"
COMPACT_H = VENDOR / "src" / "runtime" / "compact.h"
ENVIRONMENT_LEAN = VENDOR / "src" / "Lean" / "Environment.lean"
SETUP_LEAN = VENDOR / "src" / "Lean" / "Setup.lean"
REFERENCES_LEAN = VENDOR / "src" / "Lean" / "Server" / "References.lean"
SUITE_LOCK = ROOT / "SUITE.lock"

INVENTORY_PATH = ROOT / "contracts" / "olean_inventory.json"
CONTRACT_PATH = ROOT / "OLEAN_CONTRACT.md"
RUST_PATH = ROOT / "crates" / "fln-olean" / "src" / "format.rs"
REGION_RUST_PATH = ROOT / "crates" / "fln-rt" / "src" / "region_contract.rs"

SCHEMA = "fln-olean-contract/1"
SIZEOF_SIZE_T = 8  # the LP64 law; verified against the pin's static_assert below

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


def parse_olean_header(text: str) -> dict:
    lines = text.splitlines()
    start = next((i for i, l in enumerate(lines, 1) if "struct olean_header {" in l), None)
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
            size = int(arr_n) * (1 if c_type in ("char", "uint8_t") else SIZEOF_SIZE_T)
        elif c_type in ("char", "uint8_t"):
            size = 1
        elif c_type == "size_t":
            size = SIZEOF_SIZE_T
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
    asserted = sum(int(x) for x in am.group(1).split("+") if x.strip()) + SIZEOF_SIZE_T
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
        (i for i, l in enumerate(lines, 1) if l.startswith(f"structure {name} ")), None
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
        hits = [i for i, l in enumerate(lines, 1) if re.search(symbol_rx, l)]
        if len(hits) != 1:
            die(f"anchor {symbol_rx!r} in {rel}: expected exactly 1 hit, got {len(hits)}")
        anchors.append({
            "path": f"vendor/lean4-src/{rel}",
            "line": hits[0],
            "symbol": symbol_rx.replace("\\", ""),
            "role": role,
        })
    return anchors


def build_inventory() -> dict:
    module_text = MODULE_CPP.read_text(encoding="utf-8")
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
        "sizeof_size_t": SIZEOF_SIZE_T,
        "header": parse_olean_header(module_text),
        "versions": parse_versions(module_text),
        "region_align": parse_align(module_text),
        "module_data": parse_lean_structure(ENVIRONMENT_LEAN, "ModuleData"),
        "import_": parse_lean_structure(SETUP_LEAN, "Import"),
        "ilean": ilean,
        "ilean_version": int(version_field["default"]),
        "compactor_anchors": find_anchors(),
    }


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
    w.append(f"/// Fixed header size in bytes on LP64 (verified against the pin's static_assert).")
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
    w.append(f"> pin: `{pin['repo']}` `{pin['tag']}` commit `{pin['commit']}`" + (f" tree `{pin['tree']}`" if pin["tree"] else ""))
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
    w.append(f"`.ilean` is a JSON document (`FromJson`/`ToJson`), format version")
    w.append(f"**{inv['ilean_version']}**. `EnvExtensionEntry` payloads are opaque by")
    w.append("construction — each extension defines its own encoding via `exportEntriesFn`;")
    w.append("Grimoire preserves unknown payloads losslessly and never guesses (bead")
    w.append("franken_lean-y24 consumes this contract).")
    w.append("")
    return "\n".join(w) + "\n"


def main() -> int:
    check = "--check" in sys.argv[1:]
    inv = build_inventory()
    inventory_text = render_inventory(inv)
    digest = hashlib.sha256(inventory_text.encode("utf-8")).hexdigest()
    outputs = [
        (INVENTORY_PATH, inventory_text),
        (CONTRACT_PATH, render_markdown(inv, digest)),
        (RUST_PATH, render_rust(inv, digest)),
        (REGION_RUST_PATH, render_rust_region_partition(inv, digest)),
    ]
    if check:
        for path, want in outputs:
            if not path.exists():
                print(f"gen_olean_contract: DRIFT: {path.relative_to(ROOT)} missing", file=sys.stderr)
                return 2
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
                return 2
        print(f"gen_olean_contract: check OK (3 artifacts, header size {inv['header']['size']}, "
              f"inventory digest {digest[:16]}…)")
        return 0
    INVENTORY_PATH.parent.mkdir(parents=True, exist_ok=True)
    for path, text in outputs:
        path.write_text(text, encoding="utf-8")
        print(f"gen_olean_contract: wrote {path.relative_to(ROOT)} ({len(text)} bytes)")
    print(f"gen_olean_contract: header {inv['header']['size']} bytes, versions "
          f"{inv['versions']['accepted']}, align {inv['region_align']['value']}, "
          f"ilean v{inv['ilean_version']}, inventory digest {digest}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
