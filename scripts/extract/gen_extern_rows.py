#!/usr/bin/env -S python3 -I -S
"""gen_extern_rows.py — generate the canonical W5 extern row contract and its
Rust projection (bead franken_lean-pw6t).

Joins four authorities into one canonical row per `@[extern]` declaration at the
pin:

  contracts/extern_census.tsv            the 954 extern rows (tracked)
  contracts/builtin_environment*.tsv     telescope, hashes, safety, attributes,
                                         effect class (untracked shards; verified
                                         against EXTERN_BUILTIN_ENVIRONMENT.txt
                                         before one byte of them is read)
  contracts/builtin_partition.tsv        the Mirror partition (untracked shard,
                                         verified the same way)
  ABI_CONTRACT.md                        per-symbol ownership signatures
                                         (tracked, mechanically extracted)

and emits:

  contracts/EXTERN_ROW_CONTRACT.txt      the canonical contract (tracked)
  crates/fln-vm/src/extern_table_generated.rs
                                         the Rust projection (tracked)

Modes:
  (no args)     generate and publish atomically (candidate -> fsync -> rename)
  --check       regenerate in memory and byte-diff the committed artifacts;
                exit 1 on any drift, exit 3 when the untracked shards are absent
  --validate    validate the committed artifacts structurally and by root
                recompute WITHOUT touching the shards (works on every machine)
  --recover     complete an interrupted publication (candidate files present)
  --print-root  print the committed contract-root

Exit taxonomy (census_materialize.sh precedent):
  0 success / no drift
  1 decided failure (drift, disagreement, invalid artifacts)
  2 setup or internal fault (usage, unreadable input, malformed shard)
  3 inconclusive — no source could supply the untracked shards on this machine
"""

import hashlib
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

EXTERN_CENSUS = ROOT / "contracts" / "extern_census.tsv"
ENV_SHARDS = [
    ROOT / "contracts" / "builtin_environment.tsv",
    ROOT / "contracts" / "builtin_environment.001.tsv",
    ROOT / "contracts" / "builtin_environment.002.tsv",
]
PARTITION_SHARD = ROOT / "contracts" / "builtin_partition.tsv"
ENVELOPE = ROOT / "contracts" / "EXTERN_BUILTIN_ENVIRONMENT.txt"
ABI_CONTRACT = ROOT / "ABI_CONTRACT.md"
SUITE_LOCK = ROOT / "SUITE.lock"
CONTRACT_PATH = ROOT / "contracts" / "EXTERN_ROW_CONTRACT.txt"
RUST_PATH = ROOT / "crates" / "fln-vm" / "src" / "extern_table_generated.rs"

CONTRACT_SCHEMA = "fln-extern-row-contract/1"
CONTRACT_NAME = "ExternRowContractV1"
SEMANTIC_SCHEMA = "fln.extern-rows.semantic/1"
TELEMETRY_SCHEMA = "fln.extern-rows.telemetry/1"
ROW_ROOT_DOMAIN = "fln.extern-row/1"
CONTRACT_ROOT_DOMAIN = "fln.extern-row-contract/1"
ROOT_PLACEHOLDER = "fnv1a64:EXTERN_ROW_CONTRACT_ROOT"

EXPECTED_ROW_COUNT = 954

CANDIDATE_SUFFIX = ".candidate"


def die(message, code=1):
    print(f"gen_extern_rows: {message}", file=sys.stderr)
    return code


def read_text(path):
    try:
        data = path.read_bytes()
    except OSError as error:
        raise GenerationFault(f"{relative(path)} is unreadable: {error}")
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as error:
        raise GenerationFault(f"{relative(path)} is not UTF-8: {error}")
    if not text.endswith("\n"):
        raise GenerationFault(f"{relative(path)} does not end in a final newline")
    return text


def relative(path):
    return str(path.relative_to(ROOT))


class GenerationFault(Exception):
    pass


class ShardsAbsent(Exception):
    pass


# --- the hash framing (mirror of fln-vm/src/extern_row.rs; the tests re-implement
# it a third time, so a one-sided drift has nowhere to hide) ----------------------

def fnv(payload: bytes) -> str:
    value = 0xCBF29CE484222325
    for byte in payload:
        value ^= byte
        value = (value * 0x100000001B3) & 0xFFFFFFFFFFFFFFFF
    return f"fnv1a64:{value:016x}"


def framed_hash(domain: str, fields) -> str:
    payload = b""
    for field in [domain, *fields]:
        encoded = field.encode("utf-8")
        payload += len(encoded).to_bytes(8, "little") + encoded
    return fnv(payload)


_SAFE = frozenset(
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-._~/:$"
)


def percent_encode(value: str) -> str:
    out = []
    for byte in value.encode("utf-8"):
        char = chr(byte)
        if char in _SAFE:
            out.append(char)
        else:
            out.append(f"%{byte:02X}")
    return "".join(out)


def percent_decode(value: str) -> str:
    out = bytearray()
    index = 0
    raw = value.encode("utf-8")
    while index < len(raw):
        if raw[index] != ord("%"):
            out.append(raw[index])
            index += 1
            continue
        if index + 2 >= len(raw):
            raise GenerationFault(f"truncated percent escape in {value!r}")
        try:
            out.append(int(raw[index + 1 : index + 3].decode("ascii"), 16))
        except ValueError:
            raise GenerationFault(f"invalid percent escape in {value!r}")
        index += 3
    try:
        return out.decode("utf-8")
    except UnicodeDecodeError:
        raise GenerationFault(f"percent-decoded value is not UTF-8: {value!r}")


def render_fields(fields) -> str:
    return " ".join(f"{key}={percent_encode(value)}" for key, value in fields)


# --- inputs --------------------------------------------------------------------

def reference_identity():
    """The pinned Reference, cross-checked between SUITE.lock and the epoch
    manifest: repo, tag, and commit must agree in both places or nothing here
    means anything. Grammar: `reference <org/repo> tag=<tag> commit=<hash>
    tree=<hash>` (fln-suite-lock/1)."""
    reference_rows = []
    for line in read_text(SUITE_LOCK).splitlines():
        if line.startswith("#") or not line.strip():
            continue
        tokens = line.split()
        if tokens and tokens[0] == "reference":
            reference_rows.append(tokens)
    if len(reference_rows) != 1:
        raise GenerationFault(
            f"SUITE.lock must carry exactly one reference row, found {len(reference_rows)}"
        )
    tokens = reference_rows[0]
    if len(tokens) < 3:
        raise GenerationFault("SUITE.lock reference row is malformed")
    repo = tokens[1]
    fields = dict(token.split("=", 1) for token in tokens[2:] if "=" in token)
    tag = fields.get("tag")
    commit = fields.get("commit")
    tree = fields.get("tree")
    if not repo or not tag or not commit or not tree:
        raise GenerationFault("SUITE.lock reference row is missing repo/tag/commit/tree")
    manifest_path = ROOT / "tribunal" / "epochs" / tag / "MANIFEST.txt"
    if manifest_path.is_file():
        manifest = read_text(manifest_path)
        for needle in (repo, tag, commit):
            if needle not in manifest:
                raise GenerationFault(
                    f"{relative(manifest_path)} disagrees with SUITE.lock on {needle!r}"
                )
    return repo, tag, commit, tree


def sha256_file(path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_shards():
    """The untracked shards are verified against the tracked envelope before one
    byte of their content is trusted. Absent shards are a typed inconclusive,
    never a failure and never a pass."""
    if not ENVELOPE.is_file():
        raise GenerationFault(f"{relative(ENVELOPE)} is missing")
    envelope = {}
    for line in read_text(ENVELOPE).splitlines():
        if line.startswith("#") or not line.strip():
            continue
        key, _, value = line.partition("\t")
        envelope[key] = value
    if any(not shard.is_file() for shard in [*ENV_SHARDS, PARTITION_SHARD]):
        raise ShardsAbsent("builtin environment/partition shards are not on disk")
    payload = b"".join(shard.read_bytes() for shard in ENV_SHARDS)
    group = hashlib.sha256(payload).hexdigest()
    if group != envelope.get("builtin-environment-sha256"):
        raise GenerationFault(
            "builtin-environment group digest disagrees with the envelope: "
            f"got {group}, envelope says {envelope.get('builtin-environment-sha256')}"
        )
    partition = sha256_file(PARTITION_SHARD)
    if partition != envelope.get("builtin-partition-sha256"):
        raise GenerationFault(
            "builtin-partition digest disagrees with the envelope: "
            f"got {partition}, envelope says {envelope.get('builtin-partition-sha256')}"
        )
    extern = sha256_file(EXTERN_CENSUS)
    if extern != envelope.get("extern-census-sha256"):
        raise GenerationFault(
            "extern-census digest disagrees with the envelope: "
            f"got {extern}, envelope says {envelope.get('extern-census-sha256')}"
        )
    return {
        "builtin-environment-sha256": group,
        "builtin-partition-sha256": partition,
        "extern-census-sha256": extern,
    }


def parse_extern_census():
    rows = []
    saw_schema = False
    declared = None
    for line in read_text(EXTERN_CENSUS).splitlines():
        if line.startswith("#"):
            continue
        if line.startswith("schema\t") or line == "schema fln-extern-census/1":
            saw_schema = True
            continue
        if line.startswith("extern_count\t"):
            declared = int(line.split("\t")[1])
            continue
        if line.startswith("constant_count\t") or line.startswith("columns\t"):
            continue
        if line.startswith("extern\t"):
            fields = line.split("\t")
            if len(fields) != 7:
                raise GenerationFault(
                    f"{relative(EXTERN_CENSUS)}: extern row has {len(fields)} fields, expected 7"
                )
            rows.append(fields[1:])
    if not saw_schema:
        raise GenerationFault(f"{relative(EXTERN_CENSUS)}: schema row missing")
    if declared != len(rows):
        raise GenerationFault(
            f"{relative(EXTERN_CENSUS)}: declared extern_count {declared} != {len(rows)} rows"
        )
    return rows


def parse_environment():
    env = {}
    for shard in ENV_SHARDS:
        for line in read_text(shard).splitlines():
            if not line.startswith("observed\t"):
                continue
            fields = line.split("\t")
            if len(fields) != 16:
                continue
            env[fields[2]] = fields
    return env


def parse_partition():
    partition = {}
    for line in read_text(PARTITION_SHARD).splitlines():
        if not line.startswith("partition\t"):
            continue
        fields = line.split("\t")
        if len(fields) >= 4:
            partition[fields[1]] = (fields[2], fields[3])
    return partition


def parse_abi_signatures():
    signatures = {}
    conflicts = []
    for line in read_text(ABI_CONTRACT).splitlines():
        if not line.startswith("| `"):
            continue
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if len(cells) < 4 or cells[0] in ("symbol", "---") or cells[0].startswith("---"):
            continue
        symbol = cells[0].strip("`")
        signature = cells[2]
        if symbol in signatures and signatures[symbol] != signature:
            conflicts.append(symbol)
        signatures.setdefault(symbol, signature)
    if conflicts:
        raise GenerationFault(
            "ABI_CONTRACT.md carries conflicting signatures for: "
            + ", ".join(sorted(conflicts)[:5])
        )
    return signatures


# --- the join ------------------------------------------------------------------

EFFECT_CLASSES = {
    "pure",
    "toolchain-monad",
    "io",
    "monad-transformer",
    "task",
    "state",
    "effect",
}
SAFETY_CLASSES = {"safe", "partial", "unsafe"}
KIND_CLASSES = {"defn", "opaque", "ctor", "axiom"}


def unquote(field: str) -> str:
    # Environment-shard fields carry literal outer double quotes: the attributes
    # field is "extern;..." including the quote characters. Strip exactly one
    # outer pair; the inner a/s\"...\" name escapes are data and stay.
    if len(field) >= 2 and field.startswith('"') and field.endswith('"'):
        return field[1:-1]
    return field


def level_count(level_field: str) -> int:
    # "a/s\"u\"/s\"v\"" -> 2 ; "-" -> 0
    if level_field in ("-", ""):
        return 0
    return level_field.count('/s')


def parse_telescope(raw: str):
    if raw in ("-", ""):
        return []
    binders = []
    for cell in raw.split(";"):
        parts = cell.rsplit(":", 3)
        # cell shape: "quoted-name":info:mix256:h1:h2:h3:h4
        # the hash carries three colons, so split from the right is wrong there;
        # the shape is name:info:mix256:... — split into at most 3 parts instead.
        parts = cell.split(":", 2)
        if len(parts) != 3:
            raise GenerationFault(f"malformed telescope cell {cell!r}")
        name, info, type_hash = parts
        if not name or not info or not type_hash.startswith("mix256:"):
            raise GenerationFault(f"malformed telescope cell {cell!r}")
        binders.append((name, info, type_hash))
    return binders


def canonical_telescope(binders) -> str:
    if not binders:
        return "-"
    return ";".join(f"{name}:{info}:{type_hash}" for name, info, type_hash in binders)


def build_rows(census, env, partition, abi):
    rows = []
    seen_ids = set()
    for name, kind, module, arity_text, levels_text, entries in census:
        if kind not in KIND_CLASSES:
            raise GenerationFault(f"{name}: unknown kind {kind!r}")
        if name in seen_ids:
            raise GenerationFault(f"duplicate extern name {name!r}")
        seen_ids.add(name)

        observed = env.get(name)
        if observed is None:
            raise GenerationFault(f"{name}: absent from the builtin environment shard")
        (
            _record,
            quoted_key,
            _display,
            env_kind,
            env_module,
            level_field,
            env_arity,
            telescope_raw,
            type_hash,
            value_hash,
            _head,
            safety,
            attributes,
            env_entries,
            _spare,
            effect,
        ) = observed
        attributes = unquote(attributes)
        env_entries = unquote(env_entries)
        telescope_raw = unquote(telescope_raw)
        if env_kind != kind:
            raise GenerationFault(f"{name}: kind disagrees: census {kind}, env {env_kind}")
        if env_arity != arity_text:
            raise GenerationFault(
                f"{name}: arity disagrees: census {arity_text}, env {env_arity}"
            )
        levels = level_count(level_field)
        if str(levels) != levels_text:
            raise GenerationFault(
                f"{name}: level count disagrees: census {levels_text}, env {level_field!r}"
            )
        if safety not in SAFETY_CLASSES:
            raise GenerationFault(f"{name}: unknown safety class {safety!r}")
        if effect not in EFFECT_CLASSES:
            raise GenerationFault(f"{name}: unknown effect class {effect!r}")
        if "extern" not in attributes.split(";"):
            raise GenerationFault(f"{name}: attributes carry no extern marker")
        if env_entries != entries:
            raise GenerationFault(
                f"{name}: extern entries disagree: census {entries!r}, env {env_entries!r}"
            )

        entry_parts = entries.split(":")
        if len(entry_parts) != 3 or entry_parts[0] != "standard":
            raise GenerationFault(f"{name}: malformed extern entry {entries!r}")
        entry_class, entry_scope, symbol = entry_parts
        if not (symbol.startswith("lean_") or symbol.startswith("llvm_") or symbol.isidentifier()):
            raise GenerationFault(f"{name}: symbol {symbol!r} is not a C identifier")

        partition_row = partition.get(quoted_key)
        if partition_row is None:
            raise GenerationFault(f"{name}: absent from the builtin partition shard")
        partition_class, _reason = partition_row
        if partition_class != "toolchain-api":
            raise GenerationFault(
                f"{name}: partition is {partition_class}, not toolchain-api — an extern "
                "row outside the native-implementation partition needs a decision, "
                "not a generator default"
            )

        if symbol in abi:
            ownership = f"abi({abi[symbol]})"
        elif symbol.startswith("llvm_"):
            ownership = "rule(llvm-c-api)"
        elif not symbol.startswith("lean_"):
            # libm-class bare symbols (acos ... pow): the called C function is the
            # platform-math symbol; arguments and result are IEEE scalars, never
            # heap objects, so there is no ownership discipline to record beyond
            # the class. fln-libm owns the deterministic twin (plan §6.8).
            ownership = "rule(scalar-args,scalar-result)"
        elif symbol.endswith("_borrowed"):
            ownership = "rule(borrowed-args,borrowed-result)"
        else:
            ownership = "rule(borrowed-args,owned-result)"

        mode = "frontier" if name.startswith("LLVM.") else "all"

        binders = parse_telescope(telescope_raw)
        row_fields = [
            f"extern:{name}",
            name,
            kind,
            module,
            str(levels),
            arity_text,
            canonical_telescope(binders),
            type_hash,
            value_hash,
            safety,
            attributes,
            entry_class,
            entry_scope,
            symbol,
            effect,
            partition_class,
            ownership,
            mode,
            "faithful,sound",
        ]
        row_root = framed_hash(ROW_ROOT_DOMAIN, row_fields)
        rows.append((row_fields, row_root))
    rows.sort(key=lambda item: item[0][0])
    return rows


# --- rendering -----------------------------------------------------------------

def render_contract(rows, reference, digests):
    repo, tag, commit, tree = reference
    lines = [
        f"schema {CONTRACT_SCHEMA}",
        f"contract {CONTRACT_NAME}",
        "hash fnv1a64-noncryptographic framing=u64le-length-prefixed",
        f"semantic-schema {SEMANTIC_SCHEMA}",
        f"telemetry-schema {TELEMETRY_SCHEMA}",
        f"reference repo={repo} tag={tag} commit={commit} tree={tree}",
        "observation-platform linux-x86_64",
        f"row-count {len(rows)}",
        f"symbol-count {len({row[0][13] for row in rows})}",
        render_fields(
            [
                ("input-root-extern-census", f"sha256:{digests['extern-census-sha256']}"),
                (
                    "input-root-builtin-environment",
                    f"sha256:{digests['builtin-environment-sha256']}",
                ),
                (
                    "input-root-builtin-partition",
                    f"sha256:{digests['builtin-partition-sha256']}",
                ),
                ("input-root-abi-contract", f"sha256:{digests['abi-contract-sha256']}"),
            ]
        ),
        "mode-exception family=LLVM.* mode=frontier reason=upstream-llvm-backend-not-on-sovereign-path",
        "rows-begin",
    ]
    keys = [
        "id",
        "name",
        "kind",
        "module",
        "levels",
        "arity",
        "telescope",
        "type-hash",
        "value-hash",
        "safety",
        "attributes",
        "entry-class",
        "entry-scope",
        "symbol",
        "effect",
        "partition",
        "ownership",
        "mode",
        "profile",
        "row-root",
    ]
    for row_fields, row_root in rows:
        fields = list(zip(keys, row_fields)) + [("row-root", row_root)]
        lines.append("row " + render_fields(fields))
    lines.append("rows-end")
    lines.append(
        "projection kind=rust path=crates/fln-vm/src/extern_table_generated.rs "
        f"template-root={ROOT_PLACEHOLDER}"
    )
    contract_root = framed_hash(CONTRACT_ROOT_DOMAIN, lines)
    lines[-1] = lines[-1].replace(ROOT_PLACEHOLDER, contract_root)
    lines.append(f"contract-root {contract_root}")
    return "\n".join(lines) + "\n", contract_root


def render_rust(rows, contract_root):
    def rust(value):
        return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'

    out = [
        "//! @generated by scripts/extract/gen_extern_rows.py.",
        "//! Editing this file without changing canonical census input is drift.",
        "#![allow(clippy::too_many_lines)]",
        "",
        "//! The canonical W5 extern row table (bead franken_lean-pw6t): one row per",
        "//! `@[extern]` declaration at the pin, content-addressed per row and bound",
        "//! to `contracts/EXTERN_ROW_CONTRACT.txt` by `EXTERN_ROW_CONTRACT_ROOT`.",
        "",
        "/// The terminal `contract-root` of the canonical contract this table projects.",
        f"pub const EXTERN_ROW_CONTRACT_ROOT: &str = {rust(contract_root)};",
        "/// The declared anti-vacuity population of the pin's extern census.",
        f"pub const EXTERN_ROW_COUNT: usize = {len(rows)};",
        "",
        "/// One canonical extern row, `&'static` projection form. Field order is the",
        "/// canonical order of `ExternRow::root_fields` — wire, hash and table agree,",
        "/// so no projection can disagree about what the bytes mean.",
        "#derive_placeholder",
        "pub struct GeneratedExternRow {",
        '    pub id: &\'static str,',
        '    pub name: &\'static str,',
        '    pub kind: &\'static str,',
        '    pub module: &\'static str,',
        '    pub levels: u32,',
        '    pub arity: u32,',
        '    pub telescope: &\'static str,',
        '    pub type_hash: &\'static str,',
        '    pub value_hash: &\'static str,',
        '    pub safety: &\'static str,',
        '    pub attributes: &\'static str,',
        '    pub entry_class: &\'static str,',
        '    pub entry_scope: &\'static str,',
        '    pub symbol: &\'static str,',
        '    pub effect: &\'static str,',
        '    pub partition: &\'static str,',
        '    pub ownership: &\'static str,',
        '    pub mode: &\'static str,',
        '    pub profile: &\'static str,',
        '    pub row_root: &\'static str,',
        "}",
        "",
        "/// Every extern row at the pin, sorted by `id`, content-addressed per row.",
        "pub static EXTERN_ROWS: &[GeneratedExternRow] = &[",
    ]
    for row_fields, row_root in rows:
        (
            row_id,
            name,
            kind,
            module,
            levels,
            arity,
            telescope,
            type_hash,
            value_hash,
            safety,
            attributes,
            entry_class,
            entry_scope,
            symbol,
            effect,
            partition,
            ownership,
            mode,
            profile,
        ) = row_fields

        out.append("    GeneratedExternRow {")
        out.append(f"        id: {rust(row_id)},")
        out.append(f"        name: {rust(name)},")
        out.append(f"        kind: {rust(kind)},")
        out.append(f"        module: {rust(module)},")
        out.append(f"        levels: {levels},")
        out.append(f"        arity: {arity},")
        out.append(f"        telescope: {rust(telescope)},")
        out.append(f"        type_hash: {rust(type_hash)},")
        out.append(f"        value_hash: {rust(value_hash)},")
        out.append(f"        safety: {rust(safety)},")
        out.append(f"        attributes: {rust(attributes)},")
        out.append(f"        entry_class: {rust(entry_class)},")
        out.append(f"        entry_scope: {rust(entry_scope)},")
        out.append(f"        symbol: {rust(symbol)},")
        out.append(f"        effect: {rust(effect)},")
        out.append(f"        partition: {rust(partition)},")
        out.append(f"        ownership: {rust(ownership)},")
        out.append(f"        mode: {rust(mode)},")
        out.append(f"        profile: {rust(profile)},")
        out.append(f"        row_root: {rust(row_root)},")
        out.append("    },")
    out.append("];")
    out.append("")
    return "\n".join(out) + "\n"


# --- publication -----------------------------------------------------------------

def write_candidate(path, content):
    candidate = path.with_name(path.name + CANDIDATE_SUFFIX)
    try:
        with open(candidate, "xb") as handle:
            handle.write(content.encode("utf-8"))
            handle.flush()
            os.fsync(handle.fileno())
    except FileExistsError:
        raise GenerationFault(
            f"{relative(candidate)} already exists — an interrupted publication is "
            "sitting on the table; run --recover or remove the candidate deliberately"
        )
    return candidate


def publish(artifacts):
    candidates = []
    for path, content in artifacts:
        candidates.append((write_candidate(path, content), path))
    # projections first, canonical last; each rename fsynced, then the directories
    for candidate, path in candidates:
        os.replace(candidate, path)
    for directory in {path.parent for _, path in candidates}:
        fd = os.open(directory, os.O_RDONLY)
        try:
            os.fsync(fd)
        finally:
            os.close(fd)


def recover():
    recovered = []
    for path in (RUST_PATH, CONTRACT_PATH):
        candidate = path.with_name(path.name + CANDIDATE_SUFFIX)
        if candidate.is_file():
            os.replace(candidate, path)
            recovered.append(relative(path))
    if not recovered:
        raise GenerationFault("no candidate files to recover")
    return recovered


def validate_committed():
    """Structural + root validation of the committed artifacts. Needs no shard:
    the contract is self-certifying, and the Rust projection is bound to it by
    the template-root constant."""
    if not CONTRACT_PATH.is_file():
        raise GenerationFault(f"{relative(CONTRACT_PATH)} is missing")
    lines = read_text(CONTRACT_PATH).splitlines()
    if len(lines) < 12:
        raise GenerationFault("contract is implausibly short")
    if lines[0] != f"schema {CONTRACT_SCHEMA}":
        raise GenerationFault(f"contract schema row is {lines[0]!r}")
    if lines[1] != f"contract {CONTRACT_NAME}":
        raise GenerationFault(f"contract name row is {lines[1]!r}")
    root_lines = [line for line in lines if line.startswith("contract-root ")]
    if len(root_lines) != 1 or lines[-1] != root_lines[0]:
        raise GenerationFault("contract-root must appear exactly once, as the final line")
    declared_root = root_lines[0].split(" ", 1)[1]
    # The root was computed over the placeholder form of its own projections, so
    # validation substitutes the declared root back before recomputing — the same
    # two-pass law the generator publishes under.
    body = [
        line.replace(declared_root, ROOT_PLACEHOLDER) if line.startswith("projection ") else line
        for line in lines[:-1]
    ]
    recomputed = framed_hash(CONTRACT_ROOT_DOMAIN, body)
    if declared_root != recomputed:
        raise GenerationFault(
            f"contract-root {declared_root} does not recompute: {recomputed}"
        )
    row_lines = [line for line in lines if line.startswith("row ")]
    count_lines = [line for line in lines if line.startswith("row-count ")]
    if not count_lines or int(count_lines[0].split(" ")[1]) != len(row_lines):
        raise GenerationFault("row-count disagrees with the row population")
    if len(row_lines) == 0:
        raise GenerationFault("refusing a vacuous contract: zero rows")
    if not RUST_PATH.is_file():
        raise GenerationFault(f"{relative(RUST_PATH)} is missing")
    rust = read_text(RUST_PATH)
    if rust.count(declared_root) < 1:
        raise GenerationFault("the Rust projection does not carry the contract root")
    return declared_root, len(row_lines)


# --- entry ---------------------------------------------------------------------

def main(argv):
    if not (sys.flags.isolated and sys.flags.ignore_environment and sys.flags.no_site):
        print(
            "gen_extern_rows: refusing to run outside isolated mode "
            "(python3 -I -S); ambient interpreter configuration is not an input",
            file=sys.stderr,
        )
        return 2
    mode = argv[1] if len(argv) > 1 else "generate"
    try:
        if mode == "--recover":
            recovered = recover()
            print("recovered: " + ", ".join(recovered))
            return 0
        if mode == "--validate":
            root, count = validate_committed()
            print(f"valid: contract-root {root} over {count} rows")
            return 0
        if mode == "--print-root":
            root, _count = validate_committed()
            print(root)
            return 0
        if mode not in ("generate", "--check"):
            return die(f"unknown mode {mode!r}", 2)

        reference = reference_identity()
        try:
            digests = verify_shards()
        except ShardsAbsent as absent:
            print(f"inconclusive: {absent}", file=sys.stderr)
            return 3
        digests["abi-contract-sha256"] = sha256_file(ABI_CONTRACT)

        census = parse_extern_census()
        env = parse_environment()
        partition = parse_partition()
        abi = parse_abi_signatures()
        rows = build_rows(census, env, partition, abi)
        if len(rows) != EXPECTED_ROW_COUNT:
            raise GenerationFault(
                f"row population moved: {len(rows)} != declared {EXPECTED_ROW_COUNT} "
                "(a moved census is a schema revision, not an edit)"
            )

        contract_text, contract_root = render_contract(rows, reference, digests)
        rust_text = render_rust(rows, contract_root).replace(
            "#derive_placeholder", "#[derive(Clone, Copy, Debug)]"
        )

        if mode == "--check":
            drift = []
            if not CONTRACT_PATH.is_file() or read_text(CONTRACT_PATH) != contract_text:
                drift.append(relative(CONTRACT_PATH))
            if not RUST_PATH.is_file() or read_text(RUST_PATH) != rust_text:
                drift.append(relative(RUST_PATH))
            for path in (CONTRACT_PATH, RUST_PATH):
                if path.with_name(path.name + CANDIDATE_SUFFIX).exists():
                    drift.append(f"{relative(path)} has a leftover candidate")
            if drift:
                print("drift: " + ", ".join(drift), file=sys.stderr)
                return 1
            print("no drift")
            return 0

        publish([(RUST_PATH, rust_text), (CONTRACT_PATH, contract_text)])
        root, count = validate_committed()
        print(f"published: contract-root {root} over {count} rows")
        return 0
    except GenerationFault as fault:
        return die(str(fault), 1)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
