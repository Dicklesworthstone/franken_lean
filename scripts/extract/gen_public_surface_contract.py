#!/usr/bin/env -S python3 -I -S
"""Generate PublicSurfaceContractV1 from the three closed census products.

The join is deliberately a consumer of authority, never a new oracle.  It binds:

* the option registry and its real-binary receipt;
* the lean/leanc/lake inventory, reviewed policy, and transcript matrix; and
* the LSP plus $/lean inventory, reviewed policy, and real fixture manifest

to the one Reference identity in SUITE.lock and the matching immutable epoch
manifest.  Candidate Rust and Markdown projections are validated first; the
canonical contract is replaced last, so an interrupted multi-file publication
cannot present a mixed generation as authoritative.
"""

from __future__ import annotations

import difflib
import json
import os
from pathlib import Path
import sys
from urllib.parse import quote, unquote_to_bytes


ROOT = Path(__file__).resolve().parents[2]
CONTRACT = ROOT / "contracts/PUBLIC_SURFACE_CONTRACT.txt"
DOCUMENT = ROOT / "contracts/PUBLIC_SURFACE_CONTRACT.md"
RUST = ROOT / "crates/fln-conformance/src/public_surface_generated.rs"

OPTION_CENSUS = ROOT / "contracts/option_census.ndjson"
OPTION_PROBE = (
    ROOT
    / "crates/fln-conformance/evidence/option_census/probe_v4.32.0.jsonl"
)
CLI_INVENTORY = ROOT / "contracts/CLI_LAKE_INVENTORY.txt"
CLI_POLICY = ROOT / "ci/CLI_LAKE_POLICY.txt"
LSP_INVENTORY = ROOT / "contracts/LSP_WIRE_INVENTORY.txt"
LSP_POLICY = ROOT / "ci/LSP_WIRE_POLICY.txt"

CONTRACT_SCHEMA = "fln-public-surface-contract/1"
SEMANTIC_SCHEMA = "fln.public-surface.semantic/1"
TELEMETRY_SCHEMA = "fln.public-surface.telemetry/1"
ROOT_PLACEHOLDER = "fnv1a64:PUBLIC_SURFACE_CONTRACT_ROOT"

OPTION_ROLE_RULES = (
    ("trace.", "diagnostic"),
    ("diagnostics", "diagnostic"),
    ("profiler", "diagnostic"),
    ("debug.", "diagnostic"),
    ("pp.", "presentation"),
    ("format.", "presentation"),
    ("printMessageEndPos", "presentation"),
    ("linter.", "diagnostic"),
    ("weak.", "infrastructure"),
    ("maxHeartbeats", "resource-budget"),
    ("maxRecDepth", "resource-budget"),
    ("synthInstance.maxHeartbeats", "resource-budget"),
    ("synthInstance.maxSize", "resource-budget"),
    ("exponentiation.threshold", "resource-budget"),
    ("Elab.async", "infrastructure"),
    ("Elab.inServer", "infrastructure"),
    ("internal.", "infrastructure"),
    ("stderrAsMessages", "infrastructure"),
    ("server.", "infrastructure"),
    ("interpreter.", "infrastructure"),
    ("", "semantic"),
)


def die(message: str) -> "NoReturn":
    raise SystemExit(f"gen_public_surface_contract: REFUSE: {message}")


def relative(path: Path) -> str:
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        return str(path)


def read_text(path: Path) -> str:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        die(f"cannot read {relative(path)}: {error}")
    if not text.endswith("\n"):
        die(f"{relative(path)} lacks its canonical final newline")
    return text


def fnv1a64_bytes(payload: bytes) -> str:
    value = 0xCBF29CE484222325
    for byte in payload:
        value ^= byte
        value = (value * 0x100000001B3) & 0xFFFFFFFFFFFFFFFF
    return f"fnv1a64:{value:016x}"


def framed_hash(domain: str, fields: list[str] | tuple[str, ...]) -> str:
    payload = bytearray()
    for field in (domain, *fields):
        encoded = field.encode("utf-8")
        payload.extend(len(encoded).to_bytes(8, "little"))
        payload.extend(encoded)
    return fnv1a64_bytes(bytes(payload))


def encoded(value: str) -> str:
    return quote(value, safe="-._~/:$")


def parse_fields(text: str, context: str) -> dict[str, str]:
    values: dict[str, str] = {}
    for token in text.split():
        if "=" not in token:
            die(f"{context}: field {token!r} is not key=value")
        key, value = token.split("=", 1)
        if not key or not value or key in values:
            die(f"{context}: duplicate or empty field {key!r}")
        try:
            decoded = unquote_to_bytes(value).decode("utf-8")  # ubs:ignore — contract data never selects a path or command
        except UnicodeDecodeError as error:
            die(f"{context}: field {key!r} is not percent-decoded UTF-8: {error}")
        if encoded(decoded) != value:
            die(f"{context}: field {key!r} is not canonically percent-encoded")
        values[key] = decoded
    return values


def required(values: dict[str, str], key: str, context: str) -> str:
    value = values.get(key)
    if value is None or value == "":
        die(f"{context}: missing {key}")
    return value


def one_prefixed(lines: list[str], prefix: str, context: str) -> str:
    values = [line.removeprefix(prefix) for line in lines if line.startswith(prefix)]
    if len(values) != 1 or not values[0] or " " in values[0]:
        die(f"{context}: expected exactly one scalar row {prefix!r}")
    return values[0]


def section(lines: list[str], begin: str, end: str, context: str) -> list[str]:
    if lines.count(begin) != 1 or lines.count(end) != 1:
        die(f"{context}: section markers {begin!r}/{end!r} are not unique")
    first = lines.index(begin)
    last = lines.index(end)
    if first + 1 >= last:
        die(f"{context}: section {begin!r} is empty or reversed")
    return lines[first + 1 : last]


def parse_reference_row(line: str, context: str) -> dict[str, str]:
    if not line.startswith("reference "):
        die(f"{context}: not a Reference row")
    fields = parse_fields(line.removeprefix("reference "), context)
    expected = {"repo", "tag", "commit", "tree"}
    if set(fields) != expected:
        die(f"{context}: Reference fields {sorted(fields)} != {sorted(expected)}")
    return fields


def reference_identity() -> dict[str, str]:
    suite_lines = read_text(ROOT / "SUITE.lock").splitlines()
    rows = [line for line in suite_lines if line.startswith("reference ")]
    if len(rows) != 1:
        die("SUITE.lock must contain exactly one Reference row")
    words = rows[0].split()
    if len(words) != 5 or words[0] != "reference":
        die("SUITE.lock has a malformed Reference row")
    reference = {"repo": words[1]}
    reference.update(
        parse_fields(" ".join(words[2:]), "SUITE.lock Reference fields")
    )
    if set(reference) != {"repo", "tag", "commit", "tree"}:
        die("SUITE.lock Reference row lacks tag, commit, or tree")

    manifest = ROOT / "tribunal/epochs" / reference["tag"] / "MANIFEST.txt"
    manifest_rows = [
        line
        for line in read_text(manifest).splitlines()
        if line.startswith("reference ")
    ]
    if len(manifest_rows) != 1:
        die(f"{relative(manifest)} must contain exactly one Reference row")
    words = manifest_rows[0].split()
    if len(words) != 4 or words[0] != "reference":
        die(f"{relative(manifest)} has a malformed Reference row")
    repo = words[1]
    fields = parse_fields(" ".join(words[2:]), f"{relative(manifest)} Reference")
    if (
        repo != reference["repo"]
        or fields.get("tag") != reference["tag"]
        or fields.get("commit") != reference["commit"]
    ):
        die("SUITE.lock and the immutable epoch manifest disagree")
    return reference


def parse_policy(path: Path, schema: str) -> tuple[dict[str, dict[str, str]], str]:
    text = read_text(path)
    lines = text.splitlines()
    if not lines or lines[0] != f"schema {schema}":
        die(f"{relative(path)} schema mismatch")
    policies: dict[str, dict[str, str]] = {}
    previous = ""
    for number, line in enumerate(lines[1:], start=2):
        if not line.startswith("row "):
            die(f"{relative(path)}:{number}: expected a policy row")
        key, separator, rest = line.removeprefix("row ").partition(" ")
        if not separator:
            die(f"{relative(path)}:{number}: policy row lacks fields")
        if key <= previous:
            die(f"{relative(path)}:{number}: policy keys are not strictly sorted")
        previous = key
        if key in policies:
            die(f"{relative(path)}:{number}: duplicate policy key {key}")
        policies[key] = parse_fields(rest, f"{relative(path)}:{number}")
    return policies, framed_hash(schema, lines)


def inventory_roots(
    path: Path,
    schema: str,
    raw_domain: str,
    policy_path: Path,
    policy_schema: str,
) -> tuple[list[str], list[str], dict[str, dict[str, str]], dict[str, str]]:
    text = read_text(path)
    lines = text.splitlines()
    if not lines or lines[0] != f"schema {schema}":
        die(f"{relative(path)} schema mismatch")
    raw = section(lines, "raw-begin", "raw-end", relative(path))
    raw_root = one_prefixed(lines, "raw-root ", relative(path))
    computed_raw = framed_hash(raw_domain, raw)
    if raw_root != computed_raw:
        die(f"{relative(path)} raw root {raw_root} != {computed_raw}")
    policies, policy_root = parse_policy(policy_path, policy_schema)
    recorded_policy = one_prefixed(lines, "policy-root ", relative(path))
    if recorded_policy != policy_root:
        die(f"{relative(path)} policy root {recorded_policy} != {policy_root}")
    inventory_root = one_prefixed(lines, "inventory-root ", relative(path))
    root_index = next(
        (index for index, line in enumerate(lines) if line.startswith("inventory-root ")),
        -1,
    )
    if root_index != len(lines) - 1:
        die(f"{relative(path)} inventory root is not the final row")
    computed_inventory = framed_hash(schema, lines[:root_index])
    if inventory_root != computed_inventory:
        die(f"{relative(path)} inventory root {inventory_root} != {computed_inventory}")
    return lines, raw, policies, {
        "raw": raw_root,
        "policy": policy_root,
        "inventory": inventory_root,
    }


def row_root(domain: str, raw_line: str, policy_line: str) -> str:
    return framed_hash(f"fln-public-surface-row/{domain}/1", [raw_line, policy_line])


def cli_domain(reference: dict[str, str]) -> tuple[dict, list[dict], list[dict]]:
    lines, raw, policies, roots = inventory_roots(
        CLI_INVENTORY,
        "fln-cli-lake-inventory/1",
        "fln-cli-lake-raw/1",
        CLI_POLICY,
        "fln-cli-lake-policy/1",
    )
    references = [
        parse_reference_row(line, "CLI/Lake inventory Reference")
        for line in raw
        if line.startswith("reference ")
    ]
    if references != [reference]:
        die("CLI/Lake inventory is not bound to the suite Reference identity")
    platform = one_prefixed(lines, "platform ", relative(CLI_INVENTORY))
    expected_count = int(one_prefixed(lines, "surface-count ", relative(CLI_INVENTORY)))
    surfaces: list[dict] = []
    raw_keys: list[str] = []
    for line in raw:
        if not line.startswith("surface "):
            continue
        values = parse_fields(line.removeprefix("surface "), "CLI/Lake surface")
        key = required(values, "key", "CLI/Lake surface")
        raw_keys.append(key)
        policy = policies.get(key)
        if policy is None:
            die(f"CLI/Lake surface {key} has no reviewed policy")
        expected_policy = {
            "authority",
            "channel",
            "comparison",
            "platform",
            "precedence",
            "support",
        }
        if set(policy) != expected_policy:
            die(f"CLI/Lake policy {key} has fields {sorted(policy)}")
        policy_line = " ".join(f"{name}={policy[name]}" for name in sorted(policy))
        surfaces.append(
            {
                "domain": "cli-lake",
                "key": key,
                "kind": required(values, "kind", f"CLI/Lake surface {key}"),
                "epoch": f"{reference['tag']}@{reference['commit']}",
                "platform": policy["platform"],
                "client": values.get("personality", "command-line"),
                "profile": "faithful,sound",
                "mode": "all",
                "fixture": "cli-lake-census-no-mock-e2e",
                "comparison": policy["comparison"],
                "authority": policy["authority"],
                "support": policy["support"],
                "effect": (
                    f"channel:{policy['channel']};precedence:{policy['precedence']}"
                ),
                "source": required(values, "source", f"CLI/Lake surface {key}"),
                "row_root": row_root("cli-lake", line, policy_line),
            }
        )
    if raw_keys != sorted(raw_keys) or len(set(raw_keys)) != len(raw_keys):
        die("CLI/Lake surface keys are not unique and sorted")
    if len(surfaces) != expected_count or set(raw_keys) != set(policies):
        die("CLI/Lake fact-policy bijection or declared count failed")

    fixtures: list[dict] = []
    for line in raw:
        if not line.startswith("transcript "):
            continue
        values = parse_fields(line.removeprefix("transcript "), "CLI/Lake transcript")
        key = required(values, "key", "CLI/Lake transcript")
        fixtures.append(
            {
                "domain": "cli-lake",
                "key": key,
                "kind": "real-process-transcript",
                "source": f"contracts/CLI_LAKE_TRANSCRIPTS.txt:{key}",
                "expected": (
                    f"exit={required(values, 'exit', key)};"
                    f"stdout={required(values, 'stdout', key)};"
                    f"stderr={required(values, 'stderr', key)}"
                ),
                "normalizer": required(values, "normalizer", key),
                "authority": "pinned-reference-binary",
                "fixture_root": row_root("cli-lake-fixture", line, roots["inventory"]),
            }
        )
    if len(fixtures) != int(
        one_prefixed(lines, "transcript-count ", relative(CLI_INVENTORY))
    ):
        die("CLI/Lake transcript count mismatch")
    fixture_root = framed_hash(
        "fln-public-surface-cli-fixtures/1",
        [fixture["fixture_root"] for fixture in fixtures],
    )
    domain = {
        "name": "cli-lake",
        "schema": "fln-cli-lake-inventory/1",
        "platform": platform,
        "row_count": len(surfaces),
        "input_root": roots["inventory"],
        "raw_root": roots["raw"],
        "policy_root": roots["policy"],
        "fixture_root": fixture_root,
    }
    return domain, surfaces, fixtures


def lsp_domain(reference: dict[str, str]) -> tuple[dict, list[dict], list[dict]]:
    lines, raw, policies, roots = inventory_roots(
        LSP_INVENTORY,
        "fln-lsp-wire-inventory/1",
        "fln-lsp-wire-raw/1",
        LSP_POLICY,
        "fln-lsp-wire-policy/1",
    )
    references = []
    for line in raw:
        if line.startswith("reference "):
            fields = parse_fields(line.removeprefix("reference "), "LSP Reference")
            references.append(
                {
                    "repo": required(fields, "repo", "LSP Reference"),
                    "tag": required(fields, "tag", "LSP Reference"),
                    "commit": required(fields, "commit", "LSP Reference"),
                    "tree": required(fields, "tree", "LSP Reference"),
                }
            )
    if references != [reference]:
        die("LSP inventory is not bound to the suite Reference identity")
    expected_count = int(one_prefixed(lines, "method-count ", relative(LSP_INVENTORY)))
    methods: list[dict] = []
    raw_keys: list[str] = []
    for line in raw:
        if not line.startswith("method "):
            continue
        values = parse_fields(line.removeprefix("method "), "LSP method")
        key = required(values, "key", "LSP method")
        raw_keys.append(key)
        policy = policies.get(key)
        if policy is None:
            die(f"LSP method {key} has no reviewed policy")
        expected_policy = {"client", "comparison", "lifecycle", "platform", "support"}
        if set(policy) != expected_policy:
            die(f"LSP policy {key} has fields {sorted(policy)}")
        policy_line = " ".join(f"{name}={policy[name]}" for name in sorted(policy))
        methods.append(
            {
                "domain": "lsp",
                "key": key,
                "kind": required(values, "family", f"LSP method {key}"),
                "epoch": f"{reference['tag']}@{reference['commit']}",
                "platform": policy["platform"],
                "client": policy["client"],
                "profile": "faithful,sound",
                "mode": "all",
                "fixture": required(values, "fixture", f"LSP method {key}"),
                "comparison": policy["comparison"],
                "authority": "pinned-source+real-server-transcript",
                "support": policy["support"],
                "effect": f"lifecycle:{policy['lifecycle']}",
                "source": required(values, "source", f"LSP method {key}"),
                "row_root": row_root("lsp", line, policy_line),
            }
        )
    if raw_keys != sorted(raw_keys) or len(set(raw_keys)) != len(raw_keys):
        die("LSP method keys are not unique and sorted")
    if len(methods) != expected_count or set(raw_keys) != set(policies):
        die("LSP fact-policy bijection or declared count failed")

    fixtures: list[dict] = []
    for line in raw:
        if not line.startswith("fixture "):
            continue
        values = parse_fields(line.removeprefix("fixture "), "LSP fixture")
        key = required(values, "name", "LSP fixture")
        fixtures.append(
            {
                "domain": "lsp",
                "key": key,
                "kind": "real-server-transcript",
                "source": required(values, "source", key),
                "expected": (
                    f"source={required(values, 'source-hash', key)};"
                    f"expected={required(values, 'expected-hash', key)}"
                ),
                "normalizer": required(values, "normalizer", key),
                "authority": "pinned-reference-server",
                "fixture_root": row_root("lsp-fixture", line, roots["inventory"]),
            }
        )
    expected_fixtures = int(
        one_prefixed(lines, "fixture-count ", relative(LSP_INVENTORY))
    )
    if len(fixtures) != expected_fixtures:
        die("LSP fixture count mismatch")
    fixture_root = framed_hash(
        "fln-public-surface-lsp-fixtures/1",
        [fixture["fixture_root"] for fixture in fixtures],
    )
    domain = {
        "name": "lsp",
        "schema": "fln-lsp-wire-inventory/1",
        "platform": "portable-schema+linux-x86_64-oracle",
        "row_count": len(methods),
        "input_root": roots["inventory"],
        "raw_root": roots["raw"],
        "policy_root": roots["policy"],
        "fixture_root": fixture_root,
    }
    return domain, methods, fixtures


def option_role(name: str) -> str:
    for prefix, role in OPTION_ROLE_RULES:
        if name.startswith(prefix):
            return role
    die(f"option role policy is not total for {name}")


def option_key(row: dict[str, object]) -> str:
    kind = str(row["kind"])
    name = str(row.get("name", "?"))
    if kind == "dynamic":
        return f"dynamic:{row['source']}"
    return f"{kind}:{name}"


def option_domain(reference: dict[str, str]) -> tuple[dict, list[dict], list[dict]]:
    text = read_text(OPTION_CENSUS)
    lines = text.splitlines()
    rows: list[dict[str, object]] = []
    previous: tuple[str, str] | None = None
    for number, line in enumerate(lines, start=1):
        try:
            value = json.loads(line)
        except json.JSONDecodeError as error:
            die(f"{relative(OPTION_CENSUS)}:{number}: invalid JSON: {error}")
        if not isinstance(value, dict) or value.get("schema") != "fln.option-census/1":
            die(f"{relative(OPTION_CENSUS)}:{number}: wrong schema or row shape")
        canonical = json.dumps(
            value, ensure_ascii=False, separators=(",", ":"), sort_keys=True
        )
        if canonical != line:
            die(f"{relative(OPTION_CENSUS)}:{number}: row is not canonical JSON")
        kind = str(value.get("kind", ""))
        if kind not in {"builtin_option", "option", "trace_class", "dynamic"}:
            die(f"{relative(OPTION_CENSUS)}:{number}: unsupported kind {kind!r}")
        ordering = (str(value.get("name", "?")), str(value.get("source", "")))
        if previous is not None and ordering < previous:
            die(f"{relative(OPTION_CENSUS)}:{number}: rows are not sorted")
        previous = ordering
        rows.append(value)
    if len(rows) != 660:
        die(f"option census row count is {len(rows)}, expected 660")
    keys = [option_key(row) for row in rows]
    if len(set(keys)) != len(keys):
        die("option census does not produce unique PublicSurface row ids")

    raw_root = framed_hash("fln-option-public-raw/1", lines)
    policy_lines: list[str] = []
    surfaces: list[dict] = []
    for line, row, key in zip(lines, rows, keys, strict=True):
        kind = str(row["kind"])
        name = str(row.get("name", "?"))
        dynamic = kind == "dynamic"
        role = "dynamic-unresolved" if dynamic else option_role(name)
        policy = {
            "authority": "pinned-source+real-binary-receipt",
            "comparison": "disclosed-unresolved" if dynamic else "exact",
            "platform": "all",
            "role": role,
            "support": "blocked-unresolved" if dynamic else "required",
        }
        policy_line = (
            f"row {encoded(key)} "
            + " ".join(f"{field}={encoded(policy[field])}" for field in sorted(policy))
        )
        policy_lines.append(policy_line)
        surfaces.append(
            {
                "domain": "option",
                "key": key,
                "kind": kind,
                "epoch": f"{reference['tag']}@{reference['commit']}",
                "platform": policy["platform"],
                "client": "all-consumers",
                "profile": "faithful,sound",
                "mode": "all",
                "fixture": "option-census-no-mock-e2e",
                "comparison": policy["comparison"],
                "authority": policy["authority"],
                "support": policy["support"],
                "effect": role,
                "source": str(row["source"]),
                "row_root": row_root("option", line, policy_line),
            }
        )
    ordered = sorted(surfaces, key=lambda row: row["key"])
    if [row["key"] for row in ordered] != sorted(keys):
        die("option PublicSurface keys are not deterministic")
    surfaces = ordered
    policy_lines.sort()
    policy_root = framed_hash("fln-option-public-policy/1", policy_lines)

    probe_text = read_text(OPTION_PROBE)
    probe_lines = probe_text.splitlines()
    fixtures: list[dict] = []
    summary_count = 0
    for number, line in enumerate(probe_lines, start=1):
        try:
            probe = json.loads(line)
        except json.JSONDecodeError as error:
            die(f"{relative(OPTION_PROBE)}:{number}: invalid JSON: {error}")
        if probe.get("schema") != "fln-x4-option-probe/1":
            die(f"{relative(OPTION_PROBE)}:{number}: schema mismatch")
        step = str(probe.get("step", ""))
        if not step:
            die(f"{relative(OPTION_PROBE)}:{number}: step missing")
        if step == "summary":
            summary_count += 1
            if (
                probe.get("pin") != reference["tag"]
                or probe.get("verdict") != "all-cells-hold"
            ):
                die("option probe summary is not bound to the suite tag and green verdict")
        fixtures.append(
            {
                "domain": "option",
                "key": step,
                "kind": "real-binary-probe",
                "source": f"{relative(OPTION_PROBE)}:{number}",
                "expected": fnv1a64_bytes(line.encode("utf-8")),
                "normalizer": "canonical-json-v1",
                "authority": "pinned-reference-binary",
                "fixture_root": row_root("option-fixture", line, reference["commit"]),
            }
        )
    if summary_count != 1 or len(fixtures) != 7:
        die("option probe receipt is incomplete")
    probe_root = framed_hash("fln-option-public-fixtures/1", probe_lines)
    input_root = framed_hash(
        "fln-option-public-domain/1",
        [raw_root, policy_root, probe_root, reference["commit"], reference["tree"]],
    )
    domain = {
        "name": "option",
        "schema": "fln.option-census/1",
        "platform": "portable-source+linux-x86_64-oracle",
        "row_count": len(surfaces),
        "input_root": input_root,
        "raw_root": raw_root,
        "policy_root": policy_root,
        "fixture_root": probe_root,
    }
    return domain, surfaces, fixtures


def contract_field_row(kind: str, values: dict[str, object]) -> str:
    return kind + " " + " ".join(
        f"{key}={encoded(str(values[key]))}" for key in values
    )


def rust_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=False)


def render_rust(
    reference: dict[str, str],
    domains: list[dict],
    surfaces: list[dict],
    fixtures: list[dict],
    root: str,
) -> str:
    lines = [
        "//! @generated by scripts/extract/gen_public_surface_contract.py.",
        "//! Editing this file without changing canonical census input is drift.",
        "",
        "#![allow(clippy::too_many_lines)]",
        "",
        f"pub const CONTRACT_ROOT: &str = {rust_string(root)};",
        f"pub const REFERENCE_TAG: &str = {rust_string(reference['tag'])};",
        f"pub const REFERENCE_COMMIT: &str = {rust_string(reference['commit'])};",
        f"pub const REFERENCE_TREE: &str = {rust_string(reference['tree'])};",
        f"pub const SURFACE_COUNT: usize = {len(surfaces)};",
        f"pub const FIXTURE_COUNT: usize = {len(fixtures)};",
        "",
        "#[derive(Clone, Copy, Debug, Eq, PartialEq)]",
        "pub struct GeneratedDomain {",
        "    pub name: &'static str,",
        "    pub schema: &'static str,",
        "    pub platform: &'static str,",
        "    pub row_count: usize,",
        "    pub input_root: &'static str,",
        "    pub raw_root: &'static str,",
        "    pub policy_root: &'static str,",
        "    pub fixture_root: &'static str,",
        "}",
        "",
        "pub const DOMAINS: &[GeneratedDomain] = &[",
    ]
    for domain in domains:
        lines.extend(
            [
                "    GeneratedDomain {",
                f"        name: {rust_string(domain['name'])},",
                f"        schema: {rust_string(domain['schema'])},",
                f"        platform: {rust_string(domain['platform'])},",
                f"        row_count: {domain['row_count']},",
                f"        input_root: {rust_string(domain['input_root'])},",
                f"        raw_root: {rust_string(domain['raw_root'])},",
                f"        policy_root: {rust_string(domain['policy_root'])},",
                f"        fixture_root: {rust_string(domain['fixture_root'])},",
                "    },",
            ]
        )
    lines.extend(
        [
            "];",
            "",
            "#[derive(Clone, Copy, Debug, Eq, PartialEq)]",
            "pub struct GeneratedSurface {",
            "    pub domain: &'static str,",
            "    pub key: &'static str,",
            "    pub kind: &'static str,",
            "    pub row_root: &'static str,",
            "}",
            "",
            "pub const SURFACES: &[GeneratedSurface] = &[",
        ]
    )
    for surface in surfaces:
        lines.append(
            "    GeneratedSurface { "
            f"domain: {rust_string(surface['domain'])}, "
            f"key: {rust_string(surface['key'])}, "
            f"kind: {rust_string(surface['kind'])}, "
            f"row_root: {rust_string(surface['row_root'])} "
            "},"
        )
    lines.extend(
        [
            "];",
            "",
            "#[derive(Clone, Copy, Debug, Eq, PartialEq)]",
            "pub struct GeneratedFixture {",
            "    pub domain: &'static str,",
            "    pub key: &'static str,",
            "    pub fixture_root: &'static str,",
            "}",
            "",
            "pub const FIXTURES: &[GeneratedFixture] = &[",
        ]
    )
    for fixture in fixtures:
        lines.append(
            "    GeneratedFixture { "
            f"domain: {rust_string(fixture['domain'])}, "
            f"key: {rust_string(fixture['key'])}, "
            f"fixture_root: {rust_string(fixture['fixture_root'])} "
            "},"
        )
    lines.extend(["];", ""])
    return "\n".join(lines)


def render_document(
    reference: dict[str, str],
    domains: list[dict],
    surfaces: list[dict],
    fixtures: list[dict],
    root: str,
) -> str:
    by_kind: dict[tuple[str, str], int] = {}
    for surface in surfaces:
        key = (str(surface["domain"]), str(surface["kind"]))
        by_kind[key] = by_kind.get(key, 0) + 1
    lines = [
        "# Public Surface Contract V1",
        "",
        "<!-- generated by scripts/extract/gen_public_surface_contract.py -->",
        "",
        f"- Contract root: `{root}`",
        f"- Reference: `{reference['repo']} {reference['tag']} {reference['commit']}`",
        f"- Reference tree: `{reference['tree']}`",
        f"- Canonical surface rows: **{len(surfaces)}**",
        f"- Real fixture bindings: **{len(fixtures)}**",
        "",
        "Raw observed facts and reviewed policy remain separately rooted. This join",
        "does not implement any option, CLI, Lake, or LSP behavior.",
        "",
        "## Domains",
        "",
        "| Domain | Schema | Platform scope | Rows | Input root | Policy root |",
        "|---|---|---|---:|---|---|",
    ]
    for domain in domains:
        lines.append(
            f"| `{domain['name']}` | `{domain['schema']}` | "
            f"`{domain['platform']}` | {domain['row_count']} | "
            f"`{domain['input_root']}` | `{domain['policy_root']}` |"
        )
    lines.extend(
        [
            "",
            "## Surface families",
            "",
            "| Domain | Kind | Rows |",
            "|---|---|---:|",
        ]
    )
    for (domain, kind), count in sorted(by_kind.items()):
        lines.append(f"| `{domain}` | `{kind}` | {count} |")
    lines.extend(
        [
            "",
            "## Evidence boundary",
            "",
            f"Authoritative evidence uses `{SEMANTIC_SCHEMA}`. Host, PID, timing,",
            f"worker, path, cache, and performance facts use `{TELEMETRY_SCHEMA}` and",
            "are excluded from semantic roots. The pin-bearing workflow executes the",
            "three domain rigs plus the exact public-surface join.",
            "",
        ]
    )
    return "\n".join(lines)


def render_all() -> tuple[dict[Path, str], str, dict[str, int]]:
    reference = reference_identity()
    domain_products = [
        cli_domain(reference),
        lsp_domain(reference),
        option_domain(reference),
    ]
    domains = sorted((product[0] for product in domain_products), key=lambda row: row["name"])
    surfaces = sorted(
        (row for product in domain_products for row in product[1]),
        key=lambda row: (row["domain"], row["key"]),
    )
    fixtures = sorted(
        (row for product in domain_products for row in product[2]),
        key=lambda row: (row["domain"], row["key"]),
    )
    if len(domains) != 3 or len(surfaces) != 1010 or len(fixtures) != 40:
        die(
            "joined population changed: "
            f"domains={len(domains)} surfaces={len(surfaces)} fixtures={len(fixtures)}"
        )
    pairs = [(row["domain"], row["key"]) for row in surfaces]
    if pairs != sorted(pairs) or len(set(pairs)) != len(pairs):
        die("joined surface ids are not unique and sorted")

    rust_template = render_rust(reference, domains, surfaces, fixtures, ROOT_PLACEHOLDER)
    doc_template = render_document(reference, domains, surfaces, fixtures, ROOT_PLACEHOLDER)
    rust_template_root = fnv1a64_bytes(rust_template.encode("utf-8"))
    doc_template_root = fnv1a64_bytes(doc_template.encode("utf-8"))

    lines = [
        f"schema {CONTRACT_SCHEMA}",
        "contract PublicSurfaceContractV1",
        "hash fnv1a64-noncryptographic framing=u64le-length-prefixed",
        f"semantic-schema {SEMANTIC_SCHEMA}",
        f"telemetry-schema {TELEMETRY_SCHEMA}",
        contract_field_row("reference", reference),
        "observation-platform linux-x86_64",
        f"domain-count {len(domains)}",
        f"surface-count {len(surfaces)}",
        f"fixture-count {len(fixtures)}",
        "raw-policy-separation required",
        "rows-begin",
    ]
    for domain in domains:
        lines.append(
            contract_field_row(
                "domain",
                {
                    "name": domain["name"],
                    "schema": domain["schema"],
                    "platform": domain["platform"],
                    "row-count": domain["row_count"],
                    "input-root": domain["input_root"],
                    "raw-root": domain["raw_root"],
                    "policy-root": domain["policy_root"],
                    "fixture-root": domain["fixture_root"],
                },
            )
        )
    for surface in surfaces:
        lines.append(
            contract_field_row(
                "surface",
                {
                    "domain": surface["domain"],
                    "key": surface["key"],
                    "kind": surface["kind"],
                    "epoch": surface["epoch"],
                    "platform": surface["platform"],
                    "client": surface["client"],
                    "profile": surface["profile"],
                    "mode": surface["mode"],
                    "fixture": surface["fixture"],
                    "comparison": surface["comparison"],
                    "authority": surface["authority"],
                    "support": surface["support"],
                    "effect": surface["effect"],
                    "source": surface["source"],
                    "row-root": surface["row_root"],
                },
            )
        )
    for fixture in fixtures:
        lines.append(
            contract_field_row(
                "fixture",
                {
                    "domain": fixture["domain"],
                    "key": fixture["key"],
                    "kind": fixture["kind"],
                    "source": fixture["source"],
                    "expected": fixture["expected"],
                    "normalizer": fixture["normalizer"],
                    "authority": fixture["authority"],
                    "fixture-root": fixture["fixture_root"],
                },
            )
        )
    lines.extend(
        [
            contract_field_row(
                "projection",
                {
                    "kind": "markdown",
                    "path": relative(DOCUMENT),
                    "template-root": doc_template_root,
                },
            ),
            contract_field_row(
                "projection",
                {
                    "kind": "rust",
                    "path": relative(RUST),
                    "template-root": rust_template_root,
                },
            ),
            "rows-end",
        ]
    )
    contract_root = framed_hash(CONTRACT_SCHEMA, lines)
    lines.append(f"contract-root {contract_root}")
    contract_text = "\n".join(lines) + "\n"
    rust_text = rust_template.replace(ROOT_PLACEHOLDER, contract_root)
    doc_text = doc_template.replace(ROOT_PLACEHOLDER, contract_root)
    if ROOT_PLACEHOLDER in rust_text or ROOT_PLACEHOLDER in doc_text:
        die("projection root substitution was incomplete")
    outputs = {CONTRACT: contract_text, DOCUMENT: doc_text, RUST: rust_text}
    validate_outputs(outputs)
    return outputs, contract_root, {
        "domains": len(domains),
        "surfaces": len(surfaces),
        "fixtures": len(fixtures),
    }


def validate_outputs(outputs: dict[Path, str]) -> None:
    contract = outputs[CONTRACT]
    document = outputs[DOCUMENT]
    rust = outputs[RUST]
    lines = contract.splitlines()
    if not lines or not lines[-1].startswith("contract-root "):
        die("rendered contract lacks its terminal root")
    root = lines[-1].removeprefix("contract-root ")
    computed = framed_hash(CONTRACT_SCHEMA, lines[:-1])
    if root != computed:
        die(f"rendered contract root {root} != {computed}")
    if document.count(root) != 1 or rust.count(root) != 1:
        die("each generated projection must bind the contract root exactly once")
    projection_rows = [
        parse_fields(line.removeprefix("projection "), "projection")
        for line in lines
        if line.startswith("projection ")
    ]
    by_kind = {required(row, "kind", "projection"): row for row in projection_rows}
    if set(by_kind) != {"markdown", "rust"}:
        die("contract projection set is not exactly markdown plus rust")
    doc_template = document.replace(root, ROOT_PLACEHOLDER)
    rust_template = rust.replace(root, ROOT_PLACEHOLDER)
    if fnv1a64_bytes(doc_template.encode("utf-8")) != required(
        by_kind["markdown"], "template-root", "markdown projection"
    ):
        die("Markdown projection template root mismatch")
    if fnv1a64_bytes(rust_template.encode("utf-8")) != required(
        by_kind["rust"], "template-root", "Rust projection"
    ):
        die("Rust projection template root mismatch")


def candidate(path: Path) -> Path:
    return path.with_name(path.name + ".candidate")


def compare_output(path: Path, wanted: str) -> list[str]:
    if not path.exists():
        return [f"{relative(path)} is missing"]
    try:
        actual = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        return [f"{relative(path)} cannot be read: {error}"]
    if actual == wanted:
        return []
    diff = list(
        difflib.unified_diff(
            actual.splitlines(),
            wanted.splitlines(),
            fromfile=f"checked-in/{relative(path)}",
            tofile=f"generated/{relative(path)}",
            n=2,
        )
    )
    return diff[:16] or [f"{relative(path)} differs"]


def check(outputs: dict[Path, str], root: str, counts: dict[str, int]) -> int:
    interrupted = [relative(candidate(path)) for path in outputs if candidate(path).exists()]
    if interrupted:
        print(
            "gen_public_surface_contract: DRIFT: interrupted candidates exist: "
            + ", ".join(interrupted),
            file=sys.stderr,
        )
        return 1
    findings: list[str] = []
    for path, wanted in outputs.items():
        findings.extend(compare_output(path, wanted))
    if findings:
        print("gen_public_surface_contract: DRIFT:", file=sys.stderr)
        for line in findings[:32]:
            print(f"  {line}", file=sys.stderr)
        return 1
    print(
        "gen_public_surface_contract: check OK "
        f"(root {root}; {counts['domains']} domains, "
        f"{counts['surfaces']} surfaces, {counts['fixtures']} fixtures)"
    )
    return 0


def write_candidate(path: Path, text: str) -> None:
    target = candidate(path)
    try:
        with target.open("xb") as output:
            output.write(text.encode("utf-8"))
            output.flush()
            os.fsync(output.fileno())
    except FileExistsError:
        die(f"interrupted candidate {relative(target)} already exists; run --recover")
    except OSError as error:
        die(f"cannot write candidate {relative(target)}: {error}")


def replace_candidate(path: Path) -> None:
    target = candidate(path)
    try:
        os.replace(target, path)
        flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
        descriptor = os.open(path.parent, flags)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
    except OSError as error:
        die(f"cannot publish {relative(path)}: {error}")


def publish(outputs: dict[Path, str], root: str, counts: dict[str, int]) -> int:
    interrupted = [path for path in outputs if candidate(path).exists()]
    if interrupted:
        die(
            "interrupted publication candidates exist: "
            + ", ".join(relative(candidate(path)) for path in interrupted)
            + "; run --recover"
        )
    if all(not compare_output(path, text) for path, text in outputs.items()):
        print(f"gen_public_surface_contract: unchanged root {root}")
        return 0
    for path, text in outputs.items():
        write_candidate(path, text)
    staged = {
        path: candidate(path).read_text(encoding="utf-8")
        for path in outputs
    }
    validate_outputs(staged)
    # Projections first, canonical authority last.
    for path in (RUST, DOCUMENT, CONTRACT):
        replace_candidate(path)
    validate_outputs(
        {path: path.read_text(encoding="utf-8") for path in outputs}
    )
    print(
        "gen_public_surface_contract: published "
        f"root {root}; {counts['surfaces']} surfaces and {counts['fixtures']} fixtures"
    )
    return 0


def recover(outputs: dict[Path, str], root: str, counts: dict[str, int]) -> int:
    any_candidate = False
    effective: dict[Path, str] = {}
    for path, wanted in outputs.items():
        staged = candidate(path)
        if staged.exists():
            any_candidate = True
            try:
                actual = staged.read_text(encoding="utf-8")
            except (OSError, UnicodeError) as error:
                die(f"cannot read recovery candidate {relative(staged)}: {error}")
            if actual != wanted:
                die(f"recovery candidate {relative(staged)} is stale or corrupted")
            effective[path] = actual
        else:
            if compare_output(path, wanted):
                die(
                    f"{relative(path)} is neither already published nor backed by "
                    "a valid recovery candidate"
                )
            effective[path] = wanted
    validate_outputs(effective)
    if not any_candidate:
        print(f"gen_public_surface_contract: recovery unnecessary; root {root} complete")
        return 0
    for path in (RUST, DOCUMENT, CONTRACT):
        if candidate(path).exists():
            replace_candidate(path)
    final = {path: path.read_text(encoding="utf-8") for path in outputs}
    validate_outputs(final)
    print(
        "gen_public_surface_contract: recovered "
        f"root {root}; {counts['surfaces']} surfaces and {counts['fixtures']} fixtures"
    )
    return 0


def main() -> int:
    arguments = sys.argv[1:]
    allowed = {"--check", "--recover", "--print-root"}
    if len(arguments) > 1 or any(argument not in allowed for argument in arguments):
        die("usage: gen_public_surface_contract.py [--check|--recover|--print-root]")
    outputs, root, counts = render_all()
    if arguments == ["--check"]:
        return check(outputs, root, counts)
    if arguments == ["--recover"]:
        return recover(outputs, root, counts)
    if arguments == ["--print-root"]:
        print(root)
        return 0
    return publish(outputs, root, counts)


if __name__ == "__main__":
    hostile_python = sorted(name for name in os.environ if name.startswith("PYTHON"))
    if not all((sys.flags.isolated, sys.flags.ignore_environment, sys.flags.no_site)):
        die("must run under python3 -I -S")
    if hostile_python:
        print(
            "gen_public_surface_contract: isolated mode ignores ambient "
            + ", ".join(hostile_python),
            file=sys.stderr,
        )
    raise SystemExit(main())
