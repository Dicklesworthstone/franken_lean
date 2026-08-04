#!/usr/bin/env -S python3 -I -S
"""Extract the pinned Lean LSP and ``$/lean`` wire contract.

The Reference is data here, never a runtime component (D8).  The extractor reads
the complete protocol overview shipped by the pinned Lean tree, follows the wire
types named by that overview into their source declarations, extracts the
advertised capability record and semantic-token legend, and binds a representative
matrix of the Reference's own server-interactive transcript goldens.

Raw facts and reviewed policy are deliberately separate:

* ``contracts/LSP_WIRE_INVENTORY.txt`` is generated only from pinned source,
  ``SUITE.lock``, fixture bytes, and the reviewed policy root.
* ``ci/LSP_WIRE_POLICY.txt`` is hand-reviewed and must be an exact bijection over
  the mechanically discovered method keys.

Usage:

  scripts/extract/gen_lsp_wire_census.py --print-policy-template
  scripts/extract/gen_lsp_wire_census.py
  scripts/extract/gen_lsp_wire_census.py --check

Extraction is fail-closed.  A missing anchor, duplicate method, unresolved
top-level wire type, policy mismatch, or interrupted publication candidate is a
hard error.  The output has no timestamps or host paths.
"""

import json
import os
import re
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
EXTRACTOR_SOURCE = Path(__file__).resolve()
EVIDENCE_TOOL = ROOT / "scripts/evidence.py"
SUITE_LOCK = ROOT / "SUITE.lock"
OVERVIEW = ROOT / "vendor/lean4-src/src/Lean/Server/ProtocolOverview.lean"
LANGUAGE_FEATURES = ROOT / "vendor/lean4-src/src/Lean/Data/Lsp/LanguageFeatures.lean"
CAPABILITIES = ROOT / "vendor/lean4-src/src/Lean/Data/Lsp/Capabilities.lean"
INIT_SHUTDOWN = ROOT / "vendor/lean4-src/src/Lean/Data/Lsp/InitShutdown.lean"
EXTRA = ROOT / "vendor/lean4-src/src/Lean/Data/Lsp/Extra.lean"
WATCHDOG = ROOT / "vendor/lean4-src/src/Lean/Server/Watchdog.lean"
WORKER_UTILS = ROOT / "vendor/lean4-src/src/Lean/Server/FileWorker/Utils.lean"
RPC_BASIC = ROOT / "vendor/lean4-src/src/Lean/Server/Rpc/Basic.lean"
RPC_DERIVING = ROOT / "vendor/lean4-src/src/Lean/Server/Rpc/Deriving.lean"
RPC_REQUEST_HANDLING = (
    ROOT / "vendor/lean4-src/src/Lean/Server/Rpc/RequestHandling.lean"
)
REQUESTS = ROOT / "vendor/lean4-src/src/Lean/Server/Requests.lean"
INLAY_HINTS = ROOT / "vendor/lean4-src/src/Lean/Server/FileWorker/InlayHints.lean"
SEMANTIC_HIGHLIGHTING = (
    ROOT / "vendor/lean4-src/src/Lean/Server/FileWorker/SemanticHighlighting.lean"
)
RUNNER = ROOT / "vendor/lean4-src/src/Lean/Server/Test/Runner.lean"
FIXTURE_ROOT = ROOT / "vendor/lean4-src/tests/server_interactive"
TEST_UTIL = ROOT / "vendor/lean4-src/tests/util.sh"
NO_MOCK_E2E = ROOT / "crates/fln-conformance/tests/lsp_census_no_mock_e2e.rs"
POLICY = ROOT / "ci/LSP_WIRE_POLICY.txt"
OUTPUT = ROOT / "contracts/LSP_WIRE_INVENTORY.txt"

SCHEMA = "fln-lsp-wire-inventory/1"
POLICY_SCHEMA = "fln-lsp-wire-policy/1"
EXTRACTOR = "lean-protocol-overview-source-walk"
EXTRACTOR_VERSION = "1"
HASH_ALGORITHM = "fnv1a64-noncryptographic"

FIXTURES = (
    "cancellation.lean",
    "inlayHints.lean",
    "interactiveDiagnostics.lean",
    "moduleHierarchyImports.lean",
    "plainGoal.lean",
    "plainTermGoal.lean",
    "semanticTokens.lean",
    "userWidget.lean",
)

CONTAINERS_AND_PRIMITIVES = {
    "Array",
    "Bool",
    "ByteArray",
    "Char",
    "Dynamic",
    "Empty",
    "Environment",
    "Except",
    "Expr",
    "Float",
    "FVarId",
    "HashMap",
    "IO",
    "Int",
    "Json",
    "List",
    "MVarId",
    "Name",
    "Nat",
    "Option",
    "PersistentHashMap",
    "Prop",
    "RBMap",
    "RequestID",
    "StateM",
    "String",
    "Syntax",
    "Task",
    "TreeMap",
    "TreeSet",
    "Type",
    "UInt32",
    "UInt64",
    "Unit",
    "USize",
    "WithRpcRef",
}

DECLARATION_START = re.compile(
    r"^(?:(?:public|private|protected|noncomputable|partial|opaque)\s+)*"
    r"(structure|inductive|abbrev|class)\s+([A-Za-z_][A-Za-z0-9_.']*)\b"
)
TOP_LEVEL_COMMAND = re.compile(
    r"^(?:@\[[^\n]*\]\s*)?"
    r"(?:(?:public|private|protected|noncomputable|partial|opaque)\s+)*"
    r"(?:structure|inductive|abbrev|class|def|theorem|lemma|example|instance|"
    r"namespace|section|end|open|variable|initialize|builtin_initialize|"
    r"macro|syntax|elab_rules|set_option)\b"
)
IDENTIFIER = re.compile(r"\b(?:[A-Z][A-Za-z0-9_']*)(?:\.[A-Za-z_][A-Za-z0-9_']*)*\b")


def die(message: str) -> "NoReturn":  # noqa: F821 - documentation-only type
    print(f"gen_lsp_wire_census: FATAL: {message}", file=sys.stderr)
    raise SystemExit(1)


def relative(path: Path) -> str:
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        die(f"path escapes repository root: {path}")


def read_text(path: Path) -> str:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        die(f"cannot read {relative(path)}: {error}")
    if "\r" in text:
        die(f"{relative(path)} contains non-canonical carriage returns")
    return text


def read_pin() -> dict[str, str]:
    for line in read_text(SUITE_LOCK).splitlines():
        if not line.startswith("reference leanprover/lean4 "):
            continue
        fields = {
            key: value
            for token in line.split()[2:]
            if "=" in token
            for key, value in [token.split("=", 1)]
        }
        required = {"tag", "commit", "tree"}
        if set(fields) < required:
            die(f"SUITE.lock Reference row lacks {sorted(required - set(fields))}: {line!r}")
        if not re.fullmatch(r"[0-9a-f]{40}", fields["commit"]):
            die(f"SUITE.lock Reference commit is not a full lowercase hash: {fields['commit']!r}")
        if not re.fullmatch(r"[0-9a-f]{40}", fields["tree"]):
            die(f"SUITE.lock Reference tree is not a full lowercase hash: {fields['tree']!r}")
        return {
            "repo": "leanprover/lean4",
            "tag": fields["tag"],
            "commit": fields["commit"],
            "tree": fields["tree"],
        }
    die("SUITE.lock has no canonical leanprover/lean4 reference row")


VENDOR_BINDING_ENVIRONMENT_REFUSALS = (
    "requires an explicit repository .git directory",
    "requires a real repository .git directory",
)


def report_vendor_tree_binding() -> None:
    """Establish the producer's vendor identity when this checkout can run Git.

    Linked/archive/RCH trees have no real ``.git`` directory.  That is typed
    Inconclusive and never changes artifact bytes; an actual binding failure is
    fatal.  ``scripts/verify_vendor_tree.sh`` repeats the same predicate in the
    authoritative main-checkout gate.
    """

    try:
        completed = subprocess.run(
            [
                sys.executable,
                "-I",
                "-S",
                str(EVIDENCE_TOOL),
                "vendor-binding",
                "--root",
                str(ROOT),
                "--vendor-path",
                "vendor/lean4-src",
            ],
            capture_output=True,
            text=True,
            check=False,
            timeout=60,
        )
    except subprocess.TimeoutExpired:
        die("vendor-binding exceeded its 60-second producer deadline")
    if completed.returncode == 0:
        try:
            binding = json.loads(completed.stdout)
        except ValueError:
            die("vendor-binding exited 0 with non-JSON output")
        detail = f"commit={binding.get('commit', '?')} tree={binding.get('tree', '?')}"
        print(f"gen_lsp_wire_census: vendor-tree-binding established: {detail}", file=sys.stderr)
        return
    message = (completed.stderr or completed.stdout).strip()
    tail = message.splitlines()[-1] if message else "no diagnostic"
    if any(needle in message for needle in VENDOR_BINDING_ENVIRONMENT_REFUSALS):
        print(
            f"gen_lsp_wire_census: vendor-tree-binding inconclusive: {tail}",
            file=sys.stderr,
        )
        return
    die(f"vendor tree binding failed: {tail}")


def fnv1a64_bytes(data: bytes) -> int:
    value = 0xCBF29CE484222325
    for byte in data:
        value ^= byte
        value = (value * 0x100000001B3) & 0xFFFFFFFFFFFFFFFF
    return value


def framed_hash(domain: str, lines: list[str]) -> str:
    framed = bytearray()
    domain_bytes = domain.encode("utf-8")
    framed.extend(len(domain_bytes).to_bytes(8, "little"))
    framed.extend(domain_bytes)
    for line in lines:
        payload = line.encode("utf-8")
        framed.extend(len(payload).to_bytes(8, "little"))
        framed.extend(payload)
    return f"fnv1a64:{fnv1a64_bytes(bytes(framed)):016x}"


def file_hash(path: Path) -> str:
    return f"fnv1a64:{fnv1a64_bytes(path.read_bytes()):016x}"


def encode(value: str) -> str:
    safe = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-._~/:$"
    return "".join(
        chr(byte) if byte in safe else f"%{byte:02X}" for byte in value.encode("utf-8")
    )


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def lexical_mask(text: str) -> str:
    """Replace comments and string contents with spaces, retaining newlines."""

    output = list(text)
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(text):
        if block_depth:
            if text.startswith("/-", index):
                output[index : index + 2] = "  "
                block_depth += 1
                index += 2
            elif text.startswith("-/", index):
                output[index : index + 2] = "  "
                block_depth -= 1
                index += 2
            else:
                if text[index] != "\n":
                    output[index] = " "
                index += 1
            continue
        if in_string:
            if text[index] != "\n":
                output[index] = " "
            if escaped:
                escaped = False
            elif text[index] == "\\":
                escaped = True
            elif text[index] == '"':
                in_string = False
            index += 1
            continue
        if text.startswith("/-", index):
            output[index : index + 2] = "  "
            block_depth = 1
            index += 2
        elif text.startswith("--", index):
            end = text.find("\n", index)
            end = len(text) if end < 0 else end
            output[index:end] = " " * (end - index)
            index = end
        elif text[index] == '"':
            output[index] = " "
            in_string = True
            index += 1
        else:
            index += 1
    if block_depth or in_string:
        die("unterminated comment or string in pinned Lean source")
    return "".join(output)


def matching_delimiter(text: str, start: int, opening: str, closing: str) -> int:
    if start >= len(text) or text[start] != opening:
        die(f"delimiter scan did not start at {opening!r}")
    mask = lexical_mask(text)
    depth = 0
    for index in range(start, len(text)):
        char = mask[index]
        if char == opening:
            depth += 1
        elif char == closing:
            depth -= 1
            if depth == 0:
                return index
    die(f"unterminated {opening}{closing} region")


def split_top_level(text: str) -> list[str]:
    mask = lexical_mask(text)
    depths = {"(": 0, "[": 0, "{": 0}
    matching = {")": "(", "]": "[", "}": "{"}
    parts: list[str] = []
    start = 0
    for index, char in enumerate(mask):
        if char in depths:
            depths[char] += 1
        elif char in matching:
            opening = matching[char]
            depths[opening] -= 1
            if depths[opening] < 0:
                die("unbalanced delimiter while splitting protocol overview")
        elif char == "," and all(depth == 0 for depth in depths.values()):
            part = text[start:index].strip()
            if part:
                parts.append(part)
            start = index + 1
    part = text[start:].strip()
    if part:
        parts.append(part)
    if any(depth != 0 for depth in depths.values()):
        die("unbalanced nested delimiter while splitting protocol overview")
    return parts


def canonical_expression(text: str) -> str:
    """Collapse source whitespace outside strings without changing string bytes."""

    result: list[str] = []
    pending_space = False
    in_string = False
    escaped = False
    for char in text.strip():
        if in_string:
            result.append(char)
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            continue
        if char == '"':
            if pending_space and result:
                result.append(" ")
            pending_space = False
            result.append(char)
            in_string = True
        elif char.isspace():
            pending_space = True
        else:
            if pending_space and result:
                result.append(" ")
            pending_space = False
            result.append(char)
    if in_string:
        die("unterminated string while canonicalizing expression")
    return "".join(result)


def assignment_fields(entry: str, indentation: int) -> dict[str, str]:
    prefix = " " * indentation
    pattern = re.compile(
        rf"(?m)^{re.escape(prefix)}([A-Za-z][A-Za-z0-9?]*)\s*:=\s*"
    )
    matches = list(pattern.finditer(entry))
    fields: dict[str, str] = {}
    for position, match in enumerate(matches):
        end = matches[position + 1].start() if position + 1 < len(matches) else len(entry)
        value = entry[match.end() : end].strip()
        if value.endswith(","):
            value = value[:-1].rstrip()
        name = match.group(1)
        if name in fields:
            die(f"duplicate assignment field {name!r}")
        fields[name] = canonical_expression(value)
    return fields


def decode_lean_string(expression: str) -> str:
    try:
        value = json.loads(expression)
    except (TypeError, ValueError) as error:
        die(f"unsupported Lean string literal {expression!r}: {error}")
    if not isinstance(value, str):
        die(f"Lean method/description expression is not a string: {expression!r}")
    return value


def extract_methods() -> list[dict[str, object]]:
    text = read_text(OVERVIEW)
    anchor = text.find("def protocolOverview : Array MessageOverview := #[")
    if anchor < 0:
        die("ProtocolOverview.lean lacks the canonical protocolOverview declaration")
    array_start = text.find("[", anchor)
    array_end = matching_delimiter(text, array_start, "[", "]")
    entries = split_top_level(text[array_start + 1 : array_end])
    methods: list[dict[str, object]] = []
    seen: set[str] = set()
    search_offset = array_start + 1
    for ordinal, entry in enumerate(entries):
        family_match = re.match(r"\.(request|notification|rpcRequest)\s*\{", entry)
        if family_match is None:
            die(f"protocol entry {ordinal} has unsupported shape: {entry[:80]!r}")
        family = family_match.group(1)
        entry_open = entry.find("{", family_match.start())
        entry_close = matching_delimiter(entry, entry_open, "{", "}")
        if entry[entry_close + 1 :].strip():
            die(f"protocol entry {ordinal} has trailing syntax after its record")
        fields = assignment_fields(entry[entry_open + 1 : entry_close], 4)
        required = {"method", "parameterType", "description"}
        if family != "rpcRequest":
            required |= {"direction", "kinds"}
        if family == "request" or family == "rpcRequest":
            required.add("responseType")
        missing = required - set(fields)
        if missing:
            die(f"protocol entry {ordinal} lacks fields {sorted(missing)}")
        unexpected = set(fields) - {
            "method",
            "direction",
            "kinds",
            "parameterType",
            "responseType",
            "description",
        }
        if unexpected:
            die(f"protocol entry {ordinal} has unknown fields {sorted(unexpected)}")
        if family == "rpcRequest":
            method = fields["method"].removeprefix("`")
            direction = "client_to_server"
            kinds = "rpc_method"
            wire_carrier = "$/lean/rpc/call"
            family_name = "rpc_request"
        else:
            method = decode_lean_string(fields["method"])
            direction_expression = fields["direction"]
            directions = {
                ".clientToServer": "client_to_server",
                ".serverToClient": "server_to_client",
            }
            if direction_expression not in directions:
                die(f"protocol entry {method!r} has unknown direction {direction_expression!r}")
            direction = directions[direction_expression]
            kinds = fields["kinds"]
            wire_carrier = method
            family_name = family
        key = f"{family_name}:{method}"
        if key in seen:
            die(f"duplicate protocol key {key!r}")
        seen.add(key)
        local = text.find(entry, search_offset)
        if local < 0:
            die(f"could not recover source position for protocol entry {key!r}")
        search_offset = local + len(entry)
        methods.append(
            {
                "key": key,
                "ordinal": ordinal,
                "family": family_name,
                "method": method,
                "direction": direction,
                "kinds": kinds,
                "parameter": fields["parameterType"],
                "response": fields.get("responseType", "notification"),
                "description": decode_lean_string(fields["description"]),
                "wire_carrier": wire_carrier,
                "line": line_number(text, local),
                "entry_hash": file_hash_bytes(entry.encode("utf-8")),
            }
        )
    counts = {
        family: sum(method["family"] == family for method in methods)
        for family in ("request", "notification", "rpc_request")
    }
    if len(methods) != 59 or counts != {
        "request": 37,
        "notification": 12,
        "rpc_request": 10,
    }:
        die(f"protocol census cardinality drifted: total={len(methods)} families={counts}")
    return methods


def file_hash_bytes(payload: bytes) -> str:
    return f"fnv1a64:{fnv1a64_bytes(payload):016x}"


def schema_source_paths() -> list[Path]:
    roots = (
        ROOT / "vendor/lean4-src/src/Lean/Data/Lsp",
        ROOT / "vendor/lean4-src/src/Lean/Server",
        ROOT / "vendor/lean4-src/src/Lean/Widget",
    )
    paths = sorted(
        {
            path
            for source_root in roots
            for path in source_root.rglob("*.lean")
            if path.is_file()
        },
        key=relative,
    )
    if len(paths) < 50:
        die(f"schema source search collapsed to {len(paths)} files")
    return paths


def declaration_index() -> tuple[dict[str, list[dict[str, object]]], list[dict[str, object]]]:
    by_base: dict[str, list[dict[str, object]]] = {}
    all_declarations: list[dict[str, object]] = []
    for path in schema_source_paths():
        text = read_text(path)
        lines = text.splitlines(keepends=True)
        offsets: list[int] = []
        cursor = 0
        for line in lines:
            offsets.append(cursor)
            cursor += len(line)
        namespace_stack: list[str] = []
        starts: list[tuple[int, re.Match[str], tuple[str, ...]]] = []
        for index, line in enumerate(lines):
            stripped = line.rstrip("\n")
            namespace_match = re.match(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.']*)\s*$", stripped)
            if namespace_match:
                namespace_stack.extend(namespace_match.group(1).split("."))
                continue
            if re.match(r"^end(?:\s+[A-Za-z_][A-Za-z0-9_.']*)?\s*$", stripped):
                if namespace_stack:
                    namespace_stack.pop()
                continue
            declaration = DECLARATION_START.match(stripped)
            if declaration:
                starts.append((index, declaration, tuple(namespace_stack)))
        for position, (index, match, namespaces) in enumerate(starts):
            next_declaration_index = starts[position + 1][0] if position + 1 < len(starts) else len(lines)
            end_index = next_declaration_index
            for probe in range(index + 1, next_declaration_index):
                candidate = lines[probe].rstrip("\n")
                if candidate and not candidate[0].isspace() and TOP_LEVEL_COMMAND.match(candidate):
                    end_index = probe
                    break
            body = "".join(lines[index:end_index]).rstrip() + "\n"
            declared_name = match.group(2)
            full_name = (
                declared_name
                if "." in declared_name or not namespaces
                else ".".join((*namespaces, declared_name))
            )
            record: dict[str, object] = {
                "kind": match.group(1),
                "declared_name": declared_name,
                "full_name": full_name,
                "base": declared_name.rsplit(".", 1)[-1],
                "path": path,
                "line_start": index + 1,
                "line_end": end_index,
                "body": body,
                "hash": file_hash_bytes(body.encode("utf-8")),
            }
            all_declarations.append(record)
            by_base.setdefault(record["base"], []).append(record)
    if len(all_declarations) < 300:
        die(f"wire declaration source scan collapsed to {len(all_declarations)} declarations")
    return by_base, all_declarations


def type_identifiers(expression: str) -> set[str]:
    return {
        token
        for token in IDENTIFIER.findall(lexical_mask(expression))
        if token.rsplit(".", 1)[-1] not in CONTAINERS_AND_PRIMITIVES
    }


def resolve_declaration(
    token: str, by_base: dict[str, list[dict[str, object]]]
) -> dict[str, object] | None:
    base = token.rsplit(".", 1)[-1]
    candidates = by_base.get(base, [])
    if not candidates:
        return None
    if "." in token:
        exact = [
            candidate
            for candidate in candidates
            if candidate["full_name"] == token
            or str(candidate["full_name"]).endswith("." + token)
            or candidate["declared_name"] == token
        ]
        if len(exact) == 1:
            return exact[0]
        if len(exact) > 1:
            candidates = exact
    production = [
        candidate
        for candidate in candidates
        if "/Lean/Server/Test/" not in str(candidate["path"])
    ]
    if len(production) == 1:
        return production[0]
    if production:
        candidates = production
    for namespace in ("Lean.Lsp", "Lean.Widget", "Lean.Server"):
        canonical = [
            candidate
            for candidate in candidates
            if candidate["full_name"] == f"{namespace}.{base}"
        ]
        if len(canonical) == 1:
            return canonical[0]
    preferred = [
        candidate
        for candidate in candidates
        if "/Lean/Data/Lsp/" in str(candidate["path"])
        or "/Lean/Server/" in str(candidate["path"])
        or "/Lean/Widget/" in str(candidate["path"])
    ]
    if len(preferred) == 1:
        return preferred[0]
    if len(candidates) == 1:
        return candidates[0]
    descriptions = ", ".join(
        f"{relative(candidate['path'])}:{candidate['line_start']}:{candidate['full_name']}"
        for candidate in candidates[:8]
    )
    die(f"wire type {token!r} resolves ambiguously: {descriptions}")


def declaration_fields(declaration: dict[str, object]) -> list[dict[str, object]]:
    body = str(declaration["body"])
    mask = lexical_mask(body)
    fields: list[dict[str, object]] = []
    if declaration["kind"] in {"structure", "class"}:
        pattern = re.compile(
            r"(?m)^\s{2,}([A-Za-z_«][A-Za-z0-9_?'«»]*)\s*:\s*([^\n]+?)(?:\s*:=\s*[^\n]+)?$"
        )
        for match in pattern.finditer(mask):
            name = body[match.start(1) : match.end(1)]
            type_expression = canonical_expression(body[match.start(2) : match.end(2)])
            if not type_expression:
                continue
            field_syntax = mask[match.start() : match.end()]
            defaulted = ":=" in field_syntax
            wire_name = name
            if wire_name.startswith("«") and wire_name.endswith("»"):
                wire_name = wire_name[1:-1]
            if wire_name.endswith("?"):
                wire_name = wire_name[:-1]
            fields.append(
                {
                    "name": name,
                    "wire_name": wire_name,
                    "type": type_expression,
                    "optional": (
                        name.endswith("?")
                        or type_expression.startswith("Option ")
                        or defaulted
                    ),
                    "defaulted": defaulted,
                    "line": int(declaration["line_start"])
                    + body.count("\n", 0, match.start()),
                }
            )
    elif declaration["kind"] == "inductive":
        pattern = re.compile(r"(?m)^\s*\|\s*([A-Za-z_«][A-Za-z0-9_'«»]*)\b([^\n]*)$")
        for match in pattern.finditer(mask):
            fields.append(
                {
                    "name": match.group(1),
                    "wire_name": match.group(1),
                    "type": canonical_expression(body[match.start(2) : match.end(2)]) or "unit",
                    "optional": False,
                    "defaulted": False,
                    "line": int(declaration["line_start"])
                    + body.count("\n", 0, match.start()),
                }
            )
    return fields


def extract_schemas(methods: list[dict[str, object]]) -> list[dict[str, object]]:
    by_base, _ = declaration_index()
    direct_tokens = {
        token
        for method in methods
        for expression in (str(method["parameter"]), str(method["response"]))
        for token in type_identifiers(expression)
    }
    pending = sorted(direct_tokens)
    resolved_by_identity: dict[tuple[str, int, str], dict[str, object]] = {}
    unresolved_direct: set[str] = set()
    visited_tokens: set[str] = set()
    while pending:
        token = pending.pop(0)
        if token in visited_tokens:
            continue
        visited_tokens.add(token)
        declaration = resolve_declaration(token, by_base)
        if declaration is None:
            unresolved_direct.add(token)
            continue
        identity = (
            relative(declaration["path"]),
            int(declaration["line_start"]),
            str(declaration["full_name"]),
        )
        if identity in resolved_by_identity:
            continue
        resolved_by_identity[identity] = declaration
        for nested in sorted(type_identifiers(str(declaration["body"]))):
            if nested not in visited_tokens:
                pending.append(nested)
        pending.sort()
        if len(resolved_by_identity) > 2048:
            die("transitive wire-schema closure exceeds 2048 declarations")
    allowed_opaque = {
        "Elab.InfoWithCtx",
        "FVarId",
        "JsonRpc.RequestID",
        "LazyTraceChildren",
        "Lsp.RpcRef",
        "MVarId",
        "NestedType",
        "RpcRef",
    }
    unexpected_unresolved = {
        token
        for token in unresolved_direct
        if token in direct_tokens
        if token not in allowed_opaque
        and token.rsplit(".", 1)[-1] not in CONTAINERS_AND_PRIMITIVES
    }
    if unexpected_unresolved:
        die(f"unresolved wire-schema types: {sorted(unexpected_unresolved)}")
    schemas = sorted(
        resolved_by_identity.values(),
        key=lambda row: (
            str(row["full_name"]),
            relative(row["path"]),
            int(row["line_start"]),
        ),
    )
    if len(schemas) < 70:
        die(f"wire-schema closure collapsed to only {len(schemas)} declarations")
    return schemas


def extract_string_array(text: str, declaration_name: str) -> list[str]:
    match = re.search(
        rf"def\s+{re.escape(declaration_name)}\s*:\s*Array String\s*:=\s*#\[",
        text,
    )
    if match is None:
        die(f"missing {declaration_name} string-array declaration")
    start = text.find("[", match.start())
    end = matching_delimiter(text, start, "[", "]")
    body = text[start + 1 : end]
    values = [
        decode_lean_string(literal)
        for literal in re.findall(r'"(?:\\.|[^"\\])*"', body)
    ]
    if not values:
        die(f"{declaration_name} string array is empty")
    return values


def extract_capabilities() -> list[dict[str, object]]:
    text = read_text(WATCHDOG)
    match = re.search(r"def mkLeanServerCapabilities\s*:\s*ServerCapabilities\s*:=\s*\{", text)
    if match is None:
        die("Watchdog.lean lacks mkLeanServerCapabilities")
    start = text.find("{", match.start())
    end = matching_delimiter(text, start, "{", "}")
    body = text[start + 1 : end]
    fields = assignment_fields(body, 2)
    if len(fields) < 15:
        die(f"server capability extraction collapsed to {len(fields)} fields")
    rows = []
    for name, value in sorted(fields.items()):
        local = text.find(name, start, end)
        rows.append(
            {
                "name": name,
                "value": value,
                "path": WATCHDOG,
                "line": line_number(text, local),
                "hash": file_hash_bytes(value.encode("utf-8")),
            }
        )
    return rows


def unique_anchor(
    key: str, path: Path, pattern: str, value: str, flags: int = 0
) -> dict[str, object]:
    text = read_text(path)
    matches = list(re.finditer(pattern, text, flags))
    if len(matches) != 1:
        die(
            f"lifecycle anchor {key!r} expected once in {relative(path)}, "
            f"found {len(matches)}"
        )
    match = matches[0]
    snippet = match.group(0)
    return {
        "key": key,
        "value": value,
        "path": path,
        "line": line_number(text, match.start()),
        "hash": file_hash_bytes(snippet.encode("utf-8")),
    }


def extract_lifecycle_facts() -> list[dict[str, object]]:
    facts = [
        unique_anchor(
            "closed-document-request",
            WATCHDOG,
            r"code\s*:=\s*ErrorCode\.contentModified\s*\n\s*message\s*:=\s*s!\"Cannot process request to closed file",
            "content_modified_error",
        ),
        unique_anchor(
            "post-shutdown-request",
            WATCHDOG,
            r"code\s*:=\s*\.invalidRequest,\s*\n\s*message\s*:=\s*\"Request received after 'shutdown' request\.\"",
            "invalid_request_error",
        ),
        unique_anchor(
            "document-sync",
            WATCHDOG,
            r"change\s*:=\s*TextDocumentSyncKind\.incremental",
            "incremental",
        ),
        unique_anchor(
            "rpc-session-expiry-ms",
            WORKER_UTILS,
            r"def keepAliveTimeMs\s*:\s*Nat\s*:=\s*\n\s*30000",
            "30000",
        ),
        unique_anchor(
            "rpc-invalid-session",
            EXTRA,
            r"If an incorrect session ID is present, the server errors with `RpcNeedsReconnect`\.",
            "rpc_needs_reconnect",
        ),
        unique_anchor(
            "rpc-client-default-wire",
            CAPABILITIES,
            r"let some lean := c\.lean\?\s*\n\s*\| return \.v0",
            "v0",
        ),
        unique_anchor(
            "rpc-server-advertised-wire",
            WATCHDOG,
            r"rpcWireFormat\?\s*:=\s*some \.v1",
            "v1",
        ),
        unique_anchor(
            "position-encoding",
            ROOT / "vendor/lean4-src/src/Lean/Data/Lsp/Utf16.lean",
            r"0-indexed line numbering and converting the character offset within the line to a UTF-16 indexed",
            "utf16_code_units",
        ),
        unique_anchor(
            "initialize-nullability",
            INIT_SHUTDOWN,
            r"missing params, wrong json types and null all map to none",
            "optional_missing_wrong_type_or_null_is_none",
        ),
        unique_anchor(
            "cancel-routing",
            WATCHDOG,
            r"def handleCancelRequest \(p : CancelParams\).*?tryWriteMessage uri \(Notification\.mk \"\$/cancelRequest\" p\)",
            "request_id_to_document_then_forward",
            re.S,
        ),
        unique_anchor(
            "unknown-notification",
            WATCHDOG,
            r"\| \"\$/lean/rpc/keepAlive\"\s*=>.*?\n\s*\| _ =>\s*\n\s*pure \(\)",
            "ignored",
            re.S,
        ),
        unique_anchor(
            "request-method-not-found",
            REQUESTS,
            r"def methodNotFound \(method : String\) : RequestError :=\s*\n"
            r"\s*\{ code := ErrorCode\.methodNotFound",
            "method_not_found_error",
        ),
        unique_anchor(
            "request-invalid-params",
            REQUESTS,
            r"def invalidParams \(message : String\) : RequestError :=\s*\n"
            r"\s*\{ code := ErrorCode\.invalidParams, message \}",
            "invalid_params_error",
        ),
        unique_anchor(
            "request-cancelled",
            REQUESTS,
            r"def requestCancelled : RequestError :=\s*\n"
            r"\s*\{ code := ErrorCode\.requestCancelled, message := \"\" \}",
            "request_cancelled_error",
        ),
        unique_anchor(
            "rpc-method-not-found",
            RPC_REQUEST_HANDLING,
            r"\{ code := \.methodNotFound\s*\n"
            r"\s*message := s!\"No RPC method '\{p\.method\}' found\"",
            "method_not_found_error",
        ),
        unique_anchor(
            "rpc-invalid-params",
            RPC_REQUEST_HANDLING,
            r"code := JsonRpc\.ErrorCode\.invalidParams\s*\n"
            r"\s*message := s!\"Cannot decode params in RPC call",
            "invalid_params_error",
        ),
        unique_anchor(
            "partial-inlay-refresh-ms",
            INLAY_HINTS,
            r"\"workspace/inlayHint/refresh\"\s*\n\s*500",
            "500",
        ),
        unique_anchor(
            "partial-semantic-refresh-ms",
            SEMANTIC_HIGHLIGHTING,
            r"\"workspace/semanticTokens/refresh\"\s*\n\s*2000",
            "2000",
        ),
        unique_anchor(
            "rpc-reference-release",
            EXTRA,
            r"Not doing so is safe but will leak memory\.",
            "explicit_reference_counted_release",
        ),
        unique_anchor(
            "rpc-reserved-field",
            RPC_BASIC,
            r"The following are currently reserved:\s*\n- `__rpcref`",
            "__rpcref",
        ),
        unique_anchor(
            "rpc-optional-field-encoding",
            RPC_DERIVING,
            r"if isOptField fieldName then\s*\n\s*fieldTys := fieldTys\.push \(← `\(Option Json\)\)",
            "question_mark_field_is_optional_json",
        ),
    ]
    return sorted(facts, key=lambda fact: str(fact["key"]))


def extract_fixtures() -> list[dict[str, object]]:
    rows = []
    directive_pattern = re.compile(r"--(?:\^|v|⬑)\s+([^\s:]+)")
    for name in FIXTURES:
        source = FIXTURE_ROOT / name
        expected = FIXTURE_ROOT / f"{name}.out.expected"
        if not source.is_file() or not expected.is_file():
            die(f"server-interactive fixture pair is incomplete: {name}")
        source_text = read_text(source)
        directives = sorted(set(directive_pattern.findall(source_text)))
        if not directives:
            die(f"server-interactive fixture {name} has no runner directives")
        rows.append(
            {
                "name": name,
                "source": source,
                "expected": expected,
                "source_hash": file_hash(source),
                "expected_hash": file_hash(expected),
                "directives": ",".join(directives),
            }
        )
    return rows


def method_lifecycle(method: dict[str, object]) -> str:
    name = str(method["method"])
    family = str(method["family"])
    if name in {"initialize", "initialized", "shutdown", "exit"}:
        return "process"
    if name == "$/cancelRequest":
        return "request"
    if family == "rpc_request" or name.startswith("$/lean/rpc/"):
        return "rpc_session"
    if name.startswith("textDocument/") or name.startswith("$/lean/plain"):
        return "document"
    if name.startswith("callHierarchy/"):
        return "document"
    if name.startswith("$/lean/moduleHierarchy") or name.startswith("$/lean/prepareModule"):
        return "workspace"
    if name.startswith("workspace/"):
        return "workspace"
    if name == "$/lean/fileProgress":
        return "document"
    if name == "completionItem/resolve" or name == "codeAction/resolve":
        return "request"
    if name == "client/registerCapability":
        return "process"
    return "request"


def method_client(method: dict[str, object]) -> str:
    if method["direction"] == "server_to_client":
        return "server_initiated"
    if str(method["method"]) in {"initialize", "initialized", "shutdown", "exit"}:
        return "mandatory_client"
    return "capability_gated_client"


def policy_template(methods: list[dict[str, object]]) -> str:
    lines = [f"schema {POLICY_SCHEMA}"]
    for method in sorted(methods, key=lambda row: str(row["key"])):
        lifecycle = method_lifecycle(method)
        comparison = "normalized" if lifecycle == "rpc_session" else "exact"
        lines.append(
            "row "
            f"{encode(str(method['key']))} "
            f"support=required comparison={comparison} "
            f"lifecycle={lifecycle} "
            f"client={method_client(method)} platform=all"
        )
    return "\n".join(lines) + "\n"


def read_policy(methods: list[dict[str, object]]) -> tuple[str, dict[str, dict[str, str]]]:
    text = read_text(POLICY)
    lines = text.splitlines()
    if not lines or lines[0] != f"schema {POLICY_SCHEMA}":
        die(f"{relative(POLICY)} has wrong or absent schema")
    rows: dict[str, dict[str, str]] = {}
    previous = ""
    for number, line in enumerate(lines[1:], start=2):
        if not line or line.startswith("#"):
            continue
        tokens = line.split()
        if len(tokens) != 7 or tokens[0] != "row":
            die(f"{relative(POLICY)}:{number}: noncanonical policy row")
        key = tokens[1]
        if key <= previous:
            die(f"{relative(POLICY)}:{number}: policy keys are not strictly sorted")
        previous = key
        fields: dict[str, str] = {}
        for token in tokens[2:]:
            if "=" not in token:
                die(f"{relative(POLICY)}:{number}: malformed field {token!r}")
            field, value = token.split("=", 1)
            if field in fields or not value:
                die(f"{relative(POLICY)}:{number}: duplicate/empty field {field!r}")
            fields[field] = value
        if set(fields) != {"support", "comparison", "lifecycle", "client", "platform"}:
            die(f"{relative(POLICY)}:{number}: wrong policy field set {sorted(fields)}")
        if fields["support"] not in {"required", "optional"}:
            die(f"{relative(POLICY)}:{number}: unsupported support class")
        if fields["comparison"] not in {"exact", "normalized"}:
            die(f"{relative(POLICY)}:{number}: unsupported comparison class")
        rows[key] = fields
    raw_keys = {encode(str(method["key"])) for method in methods}
    policy_keys = set(rows)
    if raw_keys != policy_keys:
        die(
            "method/policy bijection failed: "
            f"missing={sorted(raw_keys - policy_keys)} "
            f"stale={sorted(policy_keys - raw_keys)}"
        )
    return text, rows


def source_rows(
    schemas: list[dict[str, object]],
    capabilities: list[dict[str, object]],
    lifecycle: list[dict[str, object]],
    fixtures: list[dict[str, object]],
) -> list[Path]:
    paths = {
        EXTRACTOR_SOURCE,
        EVIDENCE_TOOL,
        SUITE_LOCK,
        OVERVIEW,
        LANGUAGE_FEATURES,
        CAPABILITIES,
        INIT_SHUTDOWN,
        EXTRA,
        WATCHDOG,
        WORKER_UTILS,
        RPC_BASIC,
        RPC_DERIVING,
        RPC_REQUEST_HANDLING,
        REQUESTS,
        INLAY_HINTS,
        SEMANTIC_HIGHLIGHTING,
        RUNNER,
        FIXTURE_ROOT / "run_test.lean",
        TEST_UTIL,
        NO_MOCK_E2E,
    }
    paths.update(row["path"] for row in schemas)
    paths.update(row["path"] for row in capabilities)
    paths.update(row["path"] for row in lifecycle)
    for fixture in fixtures:
        paths.add(fixture["source"])
        paths.add(fixture["expected"])
    return sorted(paths, key=relative)


def render() -> tuple[str, dict[str, int]]:
    pin = read_pin()
    methods = extract_methods()
    schemas = extract_schemas(methods)
    capabilities = extract_capabilities()
    lifecycle = extract_lifecycle_facts()
    fixtures = extract_fixtures()
    policy_text, _policy_rows = read_policy(methods)
    language_text = read_text(LANGUAGE_FEATURES)
    token_types = extract_string_array(language_text, "SemanticTokenType.names")
    token_modifiers = extract_string_array(language_text, "SemanticTokenModifier.names")
    if len(token_types) != 24 or len(token_modifiers) != 10:
        die(
            "semantic legend cardinality drifted: "
            f"types={len(token_types)} modifiers={len(token_modifiers)}"
        )

    raw: list[str] = []
    raw.append(
        "reference "
        f"repo={pin['repo']} tag={pin['tag']} commit={pin['commit']} tree={pin['tree']}"
    )
    for path in source_rows(schemas, capabilities, lifecycle, fixtures):
        raw.append(f"source path={encode(relative(path))} hash={file_hash(path)}")
    for method in sorted(methods, key=lambda row: str(row["key"])):
        if method["family"] == "rpc_request":
            probe = "real-rpc-dispatch"
        elif method["direction"] == "server_to_client":
            probe = "real-server-emission"
        elif method["family"] == "request":
            probe = "real-request-dispatch"
        else:
            probe = "real-notification-dispatch"
        raw.append(
            "method "
            f"key={encode(str(method['key']))} ordinal={method['ordinal']} "
            f"family={method['family']} direction={method['direction']} "
            f"wire={encode(str(method['wire_carrier']))} "
            f"method={encode(str(method['method']))} "
            f"parameter={encode(str(method['parameter']))} "
            f"response={encode(str(method['response']))} "
            f"kinds={encode(str(method['kinds']))} "
            f"description={encode(str(method['description']))} "
            f"probe={probe} fixture=lsp-census-no-mock-e2e "
            f"source={encode(relative(OVERVIEW))}:{method['line']} "
            f"evidence={method['entry_hash']}"
        )
    field_count = 0
    for schema in schemas:
        schema_id = (
            f"{schema['full_name']}@{relative(schema['path'])}:{schema['line_start']}"
        )
        fields = declaration_fields(schema)
        raw.append(
            "schema-decl "
            f"id={encode(schema_id)} name={encode(str(schema['full_name']))} "
            f"kind={schema['kind']} source={encode(relative(schema['path']))}:"
            f"{schema['line_start']}-{schema['line_end']} "
            f"declaration={schema['hash']} field-count={len(fields)}"
        )
        for field in fields:
            field_count += 1
            raw.append(
                "schema-field "
                f"schema={encode(schema_id)} name={encode(str(field['name']))} "
                f"wire-name={encode(str(field['wire_name']))} "
                f"type={encode(str(field['type']))} "
                f"optional={'yes' if field['optional'] else 'no'} "
                f"defaulted={'yes' if field['defaulted'] else 'no'} "
                f"source={encode(relative(schema['path']))}:{field['line']}"
            )
    for capability in capabilities:
        raw.append(
            "capability "
            f"name={encode(str(capability['name']))} "
            f"value={encode(str(capability['value']))} "
            f"source={encode(relative(capability['path']))}:{capability['line']} "
            f"evidence={capability['hash']}"
        )
    for index, name in enumerate(token_types):
        raw.append(f"legend-type index={index} name={encode(name)}")
    for index, name in enumerate(token_modifiers):
        raw.append(f"legend-modifier index={index} name={encode(name)}")
    for fact in lifecycle:
        raw.append(
            "lifecycle "
            f"key={encode(str(fact['key']))} value={encode(str(fact['value']))} "
            f"source={encode(relative(fact['path']))}:{fact['line']} "
            f"evidence={fact['hash']}"
        )
    for fixture in fixtures:
        raw.append(
            "fixture "
            f"name={encode(str(fixture['name']))} "
            f"source={encode(relative(fixture['source']))} "
            f"source-hash={fixture['source_hash']} "
            f"expected={encode(relative(fixture['expected']))} "
            f"expected-hash={fixture['expected_hash']} "
            "normalizer=lean-test-suite-normalized-v1 "
            f"directives={encode(str(fixture['directives']))}"
        )

    lines = [
        f"schema {SCHEMA}",
        f"extractor {EXTRACTOR} version={EXTRACTOR_VERSION}",
        f"hash {HASH_ALGORITHM} framing=u64le-length-prefixed",
        "policy-join exact-method-bijection",
        f"method-count {len(methods)}",
        f"request-count {sum(row['family'] == 'request' for row in methods)}",
        f"notification-count {sum(row['family'] == 'notification' for row in methods)}",
        f"rpc-request-count {sum(row['family'] == 'rpc_request' for row in methods)}",
        f"schema-count {len(schemas)}",
        f"schema-field-count {field_count}",
        f"capability-count {len(capabilities)}",
        f"legend-type-count {len(token_types)}",
        f"legend-modifier-count {len(token_modifiers)}",
        f"lifecycle-count {len(lifecycle)}",
        f"fixture-count {len(fixtures)}",
        "position-units utf16-code-units",
        "unknown-object-fields ignored-by-derived-decoders",
        "malformed-known-fields typed-invalid-params",
        "raw-begin",
        *raw,
        "raw-end",
    ]
    raw_root = framed_hash("fln-lsp-wire-raw/1", raw)
    policy_root = framed_hash("fln-lsp-wire-policy/1", policy_text.splitlines())
    lines.extend(
        [
            f"raw-root {raw_root}",
            f"policy-root {policy_root}",
        ]
    )
    inventory_root = framed_hash("fln-lsp-wire-inventory/1", lines)
    lines.append(f"inventory-root {inventory_root}")
    counts = {
        "methods": len(methods),
        "schemas": len(schemas),
        "fields": field_count,
        "capabilities": len(capabilities),
        "fixtures": len(fixtures),
    }
    return "\n".join(lines) + "\n", counts


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
        die(f"interrupted publication candidate exists: {relative(candidate)}")
    except OSError as error:
        die(f"cannot write publication candidate {relative(candidate)}: {error}")
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
            f"atomic publication failed for {relative(path)}; "
            f"candidate is retained when available: {error}"
        )
    return "published"


def check_output(want: str) -> int:
    candidate = OUTPUT.with_name(OUTPUT.name + ".candidate")
    if candidate.exists():
        print(
            f"gen_lsp_wire_census: DRIFT: interrupted candidate {relative(candidate)} exists",
            file=sys.stderr,
        )
        return 1
    if not OUTPUT.exists():
        print(f"gen_lsp_wire_census: DRIFT: {relative(OUTPUT)} missing", file=sys.stderr)
        return 1
    have = read_text(OUTPUT)
    if have == want:
        return 0
    have_lines = have.splitlines()
    want_lines = want.splitlines()
    for number, (actual, expected) in enumerate(zip(have_lines, want_lines), start=1):
        if actual != expected:
            print(
                f"gen_lsp_wire_census: DRIFT: {relative(OUTPUT)}:{number}\n"
                f"  checked-in: {actual!r}\n"
                f"  regenerated: {expected!r}",
                file=sys.stderr,
            )
            return 1
    print(
        f"gen_lsp_wire_census: DRIFT: {relative(OUTPUT)} line count differs "
        f"({len(have_lines)} vs {len(want_lines)})",
        file=sys.stderr,
    )
    return 1


def main() -> int:
    arguments = sys.argv[1:]
    allowed = {"--check", "--print-policy-template"}
    unknown = [argument for argument in arguments if argument not in allowed]
    if unknown or len(arguments) > 1:
        die(
            "usage is gen_lsp_wire_census.py [--check|--print-policy-template]; "
            f"unsupported arguments: {unknown or arguments}"
        )
    report_vendor_tree_binding()
    methods = extract_methods()
    if arguments == ["--print-policy-template"]:
        sys.stdout.write(policy_template(methods))
        return 0
    text, counts = render()
    if arguments == ["--check"]:
        result = check_output(text)
        if result == 0:
            print(
                "gen_lsp_wire_census: check OK "
                f"({counts['methods']} methods, {counts['schemas']} schemas, "
                f"{counts['fields']} fields, {counts['capabilities']} capabilities, "
                f"{counts['fixtures']} real transcript fixtures)"
            )
        return result
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    action = atomic_publish(OUTPUT, text)
    print(
        f"gen_lsp_wire_census: {action} {relative(OUTPUT)} ({len(text)} bytes; "
        f"{counts['methods']} methods, {counts['schemas']} schemas, "
        f"{counts['fields']} fields, {counts['capabilities']} capabilities, "
        f"{counts['fixtures']} real transcript fixtures)"
    )
    return 0


if __name__ == "__main__":
    hostile_python = sorted(name for name in os.environ if name.startswith("PYTHON"))
    if not all((sys.flags.isolated, sys.flags.ignore_environment, sys.flags.no_site)):
        die("must run under python3 -I -S")
    if hostile_python:
        print(
            "gen_lsp_wire_census: isolated mode ignores ambient "
            f"{', '.join(hostile_python)}",
            file=sys.stderr,
        )
    raise SystemExit(main())
