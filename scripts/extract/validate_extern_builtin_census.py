#!/usr/bin/env -S python3 -I -S
"""Validate the pin-derived extern/builtin census under explicit resource bounds.

The validator is intentionally independent of Lean. It checks the two sorted
projections are bijective, recomputes every partition from the observed facts
and the parsed reviewed precedence, reconciles the legacy extern projection,
binds the raw walk back to SUITE.lock, and binds all inputs through the
publication manifest.
"""

from __future__ import annotations

import argparse
import ast
import hashlib
import os
from pathlib import Path
import sys


MAX_FILE_BYTES = 95 * 1024 * 1024
MAX_TOTAL_INPUT_BYTES = 320 * 1024 * 1024
MAX_LINE_BYTES = 16384
EXPECTED_OBSERVED_SHARDS = 3
OBSERVED_COLUMNS = 16
PARTITION_COLUMNS = 4
PARTITION_CLASSES = {
    "toolchain-api",
    "library-code",
    "user-facing-data",
}


class CensusError(Exception):
    """A typed authoritative-publication rejection."""


def _fail(reason: str, detail: str) -> "None":
    raise CensusError(f"reason={reason}: {detail}")


def _bounded_bytes(path: Path) -> bytes:
    try:
        size = path.stat().st_size
    except OSError as error:
        _fail("input_unavailable", f"{path}: {error}")
    if size > MAX_FILE_BYTES:
        _fail(
            "resource_exhausted",
            f"{path}: {size} bytes exceeds {MAX_FILE_BYTES}",
        )
    try:
        data = path.read_bytes()
    except OSError as error:
        _fail("input_unavailable", f"{path}: {error}")
    if not data.endswith(b"\n"):
        _fail("noncanonical_text", f"{path}: missing terminal LF")
    if b"\r" in data:
        _fail("noncanonical_text", f"{path}: CR bytes are forbidden")
    for line_number, line in enumerate(data.splitlines(), 1):
        if len(line) > MAX_LINE_BYTES:
            _fail(
                "resource_exhausted",
                f"{path}:{line_number}: {len(line)} bytes exceeds {MAX_LINE_BYTES}",
            )
    return data


def _decode_lean_string(value: str, context: str) -> str:
    try:
        decoded = ast.literal_eval(value)
    except (SyntaxError, ValueError) as error:
        _fail("invalid_quoted_field", f"{context}: {error}")
    if not isinstance(decoded, str):
        _fail("invalid_quoted_field", f"{context}: expected a string")
    return decoded


def _validate_structural_root(value: str, context: str) -> None:
    fields = value.split(":")
    if (
        len(fields) != 5
        or fields[0] != "mix256"
        or any(not lane.isdecimal() for lane in fields[1:])
        or any(int(lane) > (1 << 64) - 1 for lane in fields[1:])
    ):
        _fail(
            "invalid_structural_root",
            f"{context}: expected mix256 with four UInt64 lanes",
        )


def _metadata_and_rows(
    data: bytes,
    path: Path,
    schema: str,
    row_kind: str,
    columns: int,
) -> tuple[dict[str, str], list[list[str]]]:
    metadata: dict[str, str] = {}
    rows: list[list[str]] = []
    saw_schema = False
    previous_key: str | None = None
    for line_number, raw in enumerate(data.decode("utf-8").splitlines(), 1):
        if not raw or raw.startswith("#"):
            continue
        if raw == f"schema {schema}":
            if saw_schema:
                _fail("duplicate_schema", f"{path}:{line_number}")
            saw_schema = True
            continue
        fields = raw.split("\t")
        if fields[0] == row_kind:
            if len(fields) != columns:
                _fail(
                    "row_arity",
                    f"{path}:{line_number}: expected {columns}, got {len(fields)}",
                )
            key = _decode_lean_string(fields[1], f"{path}:{line_number} structural key")
            if previous_key is not None and key <= previous_key:
                reason = "duplicate_name" if key == previous_key else "row_order"
                _fail(reason, f"{path}:{line_number}: key {key!r}")
            previous_key = key
            rows.append(fields)
            continue
        if fields[0] == "columns":
            continue
        if len(fields) != 2:
            _fail("unknown_row", f"{path}:{line_number}: {raw!r}")
        if fields[0] in metadata:
            _fail("duplicate_metadata", f"{path}:{line_number}: {fields[0]}")
        metadata[fields[0]] = fields[1]
    if not saw_schema:
        _fail("missing_schema", f"{path}: expected schema {schema}")
    return metadata, rows


def _required_int(metadata: dict[str, str], key: str, path: Path) -> int:
    value = metadata.get(key)
    if value is None:
        _fail("missing_metadata", f"{path}: {key}")
    try:
        parsed = int(value)
    except ValueError:
        _fail("invalid_metadata", f"{path}: {key}={value!r}")
    if parsed < 0:
        _fail("invalid_metadata", f"{path}: {key} must be nonnegative")
    return parsed


def _parse_policy(data: bytes, path: Path) -> list[tuple[str, str, str, str]]:
    rules: list[tuple[str, str, str, str]] = []
    saw_schema = False
    saw_classes = False
    saw_precedence = False
    saw_totality = False
    known_conditions = {
        "effect",
        "extern",
        "implemented-by",
        "kind",
        "meta",
        "module-root",
        "safety",
    }
    for line_number, raw in enumerate(data.decode("utf-8").splitlines(), 1):
        if not raw or raw.startswith("#"):
            continue
        fields = raw.split()
        if raw == "schema fln-builtin-partition-policy/1":
            if saw_schema:
                _fail("duplicate_schema", f"{path}:{line_number}")
            saw_schema = True
        elif fields[0] == "classes":
            if (
                saw_classes
                or len(fields) != 2
                or set(fields[1].split(",")) != PARTITION_CLASSES
            ):
                _fail("policy_classes", f"{path}:{line_number}: {raw!r}")
            saw_classes = True
        elif raw == "precedence first-match":
            if saw_precedence:
                _fail("policy_precedence", f"{path}:{line_number}: duplicate")
            saw_precedence = True
        elif fields[0] == "rule":
            if len(fields) != 5:
                _fail("policy_rule", f"{path}:{line_number}: {raw!r}")
            try:
                ordinal = int(fields[1])
            except ValueError:
                _fail("policy_rule", f"{path}:{line_number}: invalid ordinal")
            if ordinal != len(rules) + 1:
                _fail(
                    "policy_rule_order",
                    f"{path}:{line_number}: expected {len(rules) + 1:02d}",
                )
            condition = fields[2]
            if condition == "otherwise":
                condition_key, condition_value = "otherwise", ""
            elif condition.count("=") == 1:
                condition_key, condition_value = condition.split("=", 1)
                if condition_key not in known_conditions or not condition_value:
                    _fail("policy_rule", f"{path}:{line_number}: {condition!r}")
            else:
                _fail("policy_rule", f"{path}:{line_number}: {condition!r}")
            assignments: dict[str, str] = {}
            for assignment in fields[3:]:
                if assignment.count("=") != 1:
                    _fail("policy_rule", f"{path}:{line_number}: {assignment!r}")
                key, value = assignment.split("=", 1)
                if key in assignments or not value:
                    _fail("policy_rule", f"{path}:{line_number}: {assignment!r}")
                assignments[key] = value
            if set(assignments) != {"partition", "reason"}:
                _fail("policy_rule", f"{path}:{line_number}: assignments")
            if assignments["partition"] not in PARTITION_CLASSES:
                _fail(
                    "policy_rule",
                    f"{path}:{line_number}: partition={assignments['partition']}",
                )
            rules.append(
                (
                    condition_key,
                    condition_value,
                    assignments["partition"],
                    assignments["reason"],
                )
            )
        elif raw == "totality exactly-one-first-match":
            if saw_totality:
                _fail("policy_totality", f"{path}:{line_number}: duplicate")
            saw_totality = True
        else:
            _fail("policy_unknown_row", f"{path}:{line_number}: {raw!r}")
    if not all((saw_schema, saw_classes, saw_precedence, saw_totality)):
        _fail("policy_incomplete", str(path))
    otherwise = [index for index, rule in enumerate(rules) if rule[0] == "otherwise"]
    if otherwise != [len(rules) - 1]:
        _fail("policy_totality", f"{path}: final rule must be the sole otherwise")
    return rules


def _condition_matches(
    condition_key: str,
    condition_value: str,
    *,
    kind: str,
    module: str,
    safety: str,
    attribute_set: set[str],
    extern_entries: str,
    implemented_by: str,
    effect: str,
) -> bool:
    if condition_key == "otherwise":
        return True
    if condition_key == "extern":
        return condition_value == "present" and extern_entries != "-"
    if condition_key == "implemented-by":
        return condition_value == "present" and implemented_by != "-"
    if condition_key == "kind":
        return kind in condition_value.split(",")
    if condition_key == "meta":
        return condition_value == "true" and "meta" in attribute_set
    if condition_key == "safety":
        return safety in condition_value.split(",")
    if condition_key == "effect":
        if condition_value == "non-pure":
            return effect != "pure"
        return effect in condition_value.split(",")
    if condition_key == "module-root":
        if condition_value != "Lean":
            _fail("policy_rule", f"unsupported module root {condition_value!r}")
        return module == 'a/s"Lean"' or module.startswith('a/s"Lean"/')
    _fail("policy_rule", f"unsupported condition {condition_key!r}")


def _expected_partition(
    observed: list[str], rules: list[tuple[str, str, str, str]]
) -> tuple[str, str]:
    kind = observed[3]
    module = _decode_lean_string(observed[4], f"{observed[1]} module")
    safety = observed[11]
    attributes = _decode_lean_string(observed[12], f"{observed[1]} attributes")
    extern_entries = _decode_lean_string(observed[13], f"{observed[1]} extern entries")
    implemented_by = _decode_lean_string(observed[14], f"{observed[1]} implemented-by")
    effect = observed[15]
    attribute_set = set(attributes.split(";"))
    for condition_key, condition_value, partition, reason in rules:
        if _condition_matches(
            condition_key,
            condition_value,
            kind=kind,
            module=module,
            safety=safety,
            attribute_set=attribute_set,
            extern_entries=extern_entries,
            implemented_by=implemented_by,
            effect=effect,
        ):
            if (extern_entries != "-" or implemented_by != "-") and (
                partition != "toolchain-api"
            ):
                _fail(
                    "native_marker_misclassified",
                    f"{observed[1]}: {partition}/{reason}",
                )
            return partition, reason
    _fail("policy_not_total", observed[1])


def _parse_extern(data: bytes, path: Path) -> tuple[int, dict[str, str]]:
    saw_schema = False
    declared_count: int | None = None
    rows: dict[str, str] = {}
    previous_name: str | None = None
    for line_number, raw in enumerate(data.decode("utf-8").splitlines(), 1):
        if not raw or raw.startswith("#"):
            continue
        if raw == "schema fln-extern-census/1":
            saw_schema = True
            continue
        fields = raw.split("\t")
        if fields[0] == "extern_count":
            declared_count = int(fields[1])
        elif fields[0] == "extern":
            if len(fields) != 7:
                _fail("row_arity", f"{path}:{line_number}: extern")
            name = fields[1]
            if previous_name is not None and name <= previous_name:
                _fail("extern_order", f"{path}:{line_number}: {name}")
            previous_name = name
            rows[name] = fields[6]
        elif fields[0] in {
            "constant_count",
            "columns",
            "columns_summary",
            "summary",
        }:
            continue
        else:
            _fail("unknown_row", f"{path}:{line_number}: {raw!r}")
    if not saw_schema:
        _fail("missing_schema", f"{path}: fln-extern-census/1")
    if declared_count != len(rows):
        _fail(
            "extern_count_mismatch",
            f"{path}: declared={declared_count} rows={len(rows)}",
        )
    return len(rows), rows


def _parse_manifest(data: bytes, path: Path) -> dict[str, str]:
    marker = b"manifest-root\tsha256:"
    marker_index = data.rfind(marker)
    if marker_index < 0:
        _fail("missing_manifest_root", str(path))
    prefix = data[:marker_index]
    root_line = data[marker_index:].decode("utf-8").strip()
    declared_root = root_line.removeprefix("manifest-root\tsha256:")
    actual_root = hashlib.sha256(prefix).hexdigest()
    if declared_root != actual_root:
        _fail(
            "manifest_root_mismatch",
            f"{path}: declared={declared_root} actual={actual_root}",
        )
    metadata: dict[str, str] = {}
    saw_schema = False
    for line_number, raw in enumerate(prefix.decode("utf-8").splitlines(), 1):
        if not raw or raw.startswith("#"):
            continue
        if raw == "schema fln-extern-builtin-environment/1":
            saw_schema = True
            continue
        fields = raw.split("\t")
        if len(fields) != 2 or fields[0] in metadata:
            _fail("manifest_invalid", f"{path}:{line_number}: {raw!r}")
        metadata[fields[0]] = fields[1]
    if not saw_schema:
        _fail("missing_schema", f"{path}: manifest")
    return metadata


def _combine_observed_shards(
    data: list[bytes], paths: list[Path]
) -> tuple[dict[str, str], list[list[str]]]:
    if len(data) != EXPECTED_OBSERVED_SHARDS or len(paths) != EXPECTED_OBSERVED_SHARDS:
        _fail(
            "observed_shard_count",
            f"expected={EXPECTED_OBSERVED_SHARDS} actual={len(data)}",
        )
    combined_rows: list[list[str]] = []
    canonical_metadata: dict[str, str] | None = None
    previous_key: str | None = None
    for shard_data, path in zip(data, paths, strict=True):
        metadata, rows = _metadata_and_rows(
            shard_data,
            path,
            "fln-builtin-environment/1",
            "observed",
            OBSERVED_COLUMNS,
        )
        if canonical_metadata is None:
            canonical_metadata = metadata
        elif metadata != canonical_metadata:
            differing = sorted(
                key
                for key in set(metadata) | set(canonical_metadata)
                if metadata.get(key) != canonical_metadata.get(key)
            )
            _fail("observed_shard_metadata_drift", f"{path}: fields={differing}")
        if not rows:
            _fail("observed_shard_empty", str(path))
        first_key = _decode_lean_string(rows[0][1], f"{path}: first key")
        if previous_key is not None and first_key <= previous_key:
            _fail(
                "observed_shard_order",
                f"{path}: {first_key!r} follows {previous_key!r}",
            )
        previous_key = _decode_lean_string(rows[-1][1], f"{path}: last key")
        combined_rows.extend(rows)
    assert canonical_metadata is not None
    return canonical_metadata, combined_rows


def _validate_observed_registries(metadata: dict[str, str], path: Path) -> set[str]:
    module_count = _required_int(metadata, "module_count", path)
    expected_module_keys = {f"module_registry_{index}" for index in range(module_count)}
    actual_module_keys = {key for key in metadata if key.startswith("module_registry_")}
    if actual_module_keys != expected_module_keys:
        missing = sorted(expected_module_keys - actual_module_keys)[:3]
        extra = sorted(actual_module_keys - expected_module_keys)[:3]
        _fail("module_registry_incomplete", f"missing={missing} extra={extra}")
    modules = [
        _decode_lean_string(metadata[f"module_registry_{index}"], f"module {index}")
        for index in range(module_count)
    ]
    if modules != sorted(set(modules)):
        _fail("module_registry_noncanonical", str(path))

    attribute_count = _required_int(metadata, "attribute_count", path)
    registry = metadata.get("attribute_registry")
    if registry is None:
        _fail("attribute_registry_incomplete", f"{path}: missing registry")
    attributes = _decode_lean_string(registry, f"{path}: attribute registry").split(",")
    if len(attributes) != attribute_count or attributes != sorted(set(attributes)):
        _fail(
            "attribute_registry_incomplete",
            f"declared={attribute_count} entries={len(attributes)}",
        )

    base_keys = {
        "attribute_count",
        "attribute_registry",
        "constant_count",
        "extern_count",
        "module_count",
        "oracle_kind",
        "reference_commit",
        "reference_tree",
        "suite_lock_sha256",
    }
    expected_keys = base_keys | expected_module_keys
    if set(metadata) != expected_keys:
        missing = sorted(expected_keys - set(metadata))[:3]
        extra = sorted(set(metadata) - expected_keys)[:3]
        _fail("observed_metadata_drift", f"missing={missing} extra={extra}")
    return set(modules)


def _suite_reference(data: bytes, path: Path) -> tuple[str, str]:
    reference_rows = [
        raw for raw in data.decode("utf-8").splitlines() if raw.startswith("reference ")
    ]
    if len(reference_rows) != 1:
        _fail("suite_reference", f"{path}: rows={len(reference_rows)}")
    fields = reference_rows[0].split()[1:]
    if not fields or "=" in fields[0]:
        _fail("suite_reference", f"{path}: missing repository identity")
    values: dict[str, str] = {"repository": fields[0]}
    for field in fields[1:]:
        if field.count("=") != 1:
            _fail("suite_reference", f"{path}: {field!r}")
        key, value = field.split("=", 1)
        if key in values:
            _fail("suite_reference", f"{path}: duplicate {key}")
        values[key] = value
    commit = values.get("commit", "")
    tree = values.get("tree", "")
    if (
        len(commit) != 40
        or len(tree) != 40
        or any(character not in "0123456789abcdef" for character in commit + tree)
    ):
        _fail("suite_reference", f"{path}: invalid commit/tree")
    return commit, tree


def validate(args: argparse.Namespace) -> dict[str, int | str]:
    extern_data = _bounded_bytes(args.extern)
    observed_data = [_bounded_bytes(path) for path in args.observed]
    partition_data = _bounded_bytes(args.partition)
    manifest_data = _bounded_bytes(args.manifest)
    policy_data = _bounded_bytes(args.policy)
    suite_path = args.root / "SUITE.lock"
    suite_data = _bounded_bytes(suite_path)
    total_input_bytes = sum(
        len(data)
        for data in [
            extern_data,
            *observed_data,
            partition_data,
            manifest_data,
            policy_data,
            suite_data,
        ]
    )
    if total_input_bytes > MAX_TOTAL_INPUT_BYTES:
        _fail(
            "resource_exhausted",
            f"total input {total_input_bytes} bytes exceeds {MAX_TOTAL_INPUT_BYTES}",
        )

    rules = _parse_policy(policy_data, args.policy)

    observed_meta, observed_rows = _combine_observed_shards(
        observed_data,
        args.observed,
    )
    module_registry = _validate_observed_registries(observed_meta, args.observed[0])
    suite_commit, suite_tree = _suite_reference(suite_data, suite_path)
    expected_observed_bindings = {
        "oracle_kind": "reference-environment-walk",
        "reference_commit": suite_commit,
        "reference_tree": suite_tree,
        "suite_lock_sha256": hashlib.sha256(suite_data).hexdigest(),
    }
    for key, expected in expected_observed_bindings.items():
        if observed_meta.get(key) != expected:
            _fail(
                "observed_source_binding_drift",
                f"{key}: expected={expected!r} actual={observed_meta.get(key)!r}",
            )
    partition_meta, partition_rows = _metadata_and_rows(
        partition_data,
        args.partition,
        "fln-builtin-partition/1",
        "partition",
        PARTITION_COLUMNS,
    )
    expected_partition_metadata = {
        "constant_count",
        "library_code_count",
        "partition_policy_sha256",
        "toolchain_api_count",
        "unresolved_count",
        "user_facing_data_count",
    }
    if set(partition_meta) != expected_partition_metadata:
        missing = sorted(expected_partition_metadata - set(partition_meta))
        extra = sorted(set(partition_meta) - expected_partition_metadata)
        _fail("partition_metadata_drift", f"missing={missing} extra={extra}")
    policy_sha256 = hashlib.sha256(policy_data).hexdigest()
    if partition_meta.get("partition_policy_sha256") != policy_sha256:
        _fail(
            "partition_policy_binding_drift",
            "partition projection does not bind the reviewed policy",
        )
    observed_count = _required_int(observed_meta, "constant_count", args.observed[0])
    partition_count = _required_int(partition_meta, "constant_count", args.partition)
    if observed_count != len(observed_rows) or partition_count != len(partition_rows):
        _fail(
            "declaration_count_mismatch",
            "declared counts do not equal emitted row counts "
            f"(observed {observed_count}/{len(observed_rows)}, "
            f"partition {partition_count}/{len(partition_rows)})",
        )
    if observed_count != partition_count:
        _fail(
            "policy_bijection",
            f"observed={observed_count} partition={partition_count}",
        )

    class_counts = {partition_class: 0 for partition_class in PARTITION_CLASSES}
    observed_extern: dict[str, str] = {}
    for observed, policy in zip(observed_rows, partition_rows, strict=True):
        if observed[1] != policy[1]:
            _fail(
                "policy_bijection",
                f"observed key {observed[1]!r} != partition key {policy[1]!r}",
            )
        _validate_structural_root(observed[8], f"{observed[1]} signature")
        _validate_structural_root(observed[9], f"{observed[1]} result")
        module = _decode_lean_string(observed[4], f"{observed[1]} module")
        if module not in module_registry:
            _fail("module_registry_join", f"{observed[1]}: {module!r}")
        expected_class, expected_reason = _expected_partition(observed, rules)
        if policy[2:] != [expected_class, expected_reason]:
            _fail(
                "partition_drift",
                f"{observed[1]}: expected {expected_class}/{expected_reason}, "
                f"got {policy[2]}/{policy[3]}",
            )
        if policy[2] not in class_counts:
            _fail("unknown_partition", f"{observed[1]}: {policy[2]}")
        class_counts[policy[2]] += 1
        entries = _decode_lean_string(observed[13], f"{observed[1]} extern")
        if entries != "-":
            display_name = observed[2]
            if display_name in observed_extern:
                _fail("duplicate_extern_name", display_name)
            observed_extern[display_name] = entries

    unresolved = _required_int(partition_meta, "unresolved_count", args.partition)
    if unresolved != 0:
        _fail("unresolved_partition", f"rows={unresolved}")
    declared_classes = {
        "toolchain-api": _required_int(
            partition_meta, "toolchain_api_count", args.partition
        ),
        "library-code": _required_int(
            partition_meta, "library_code_count", args.partition
        ),
        "user-facing-data": _required_int(
            partition_meta, "user_facing_data_count", args.partition
        ),
    }
    if declared_classes != class_counts:
        _fail(
            "partition_count_mismatch",
            f"declared={declared_classes} actual={class_counts}",
        )

    extern_count, extern_rows = _parse_extern(extern_data, args.extern)
    observed_declared_extern = _required_int(
        observed_meta, "extern_count", args.observed[0]
    )
    if observed_declared_extern != len(observed_extern):
        _fail(
            "observed_extern_count_mismatch",
            f"declared={observed_declared_extern} rows={len(observed_extern)}",
        )
    if extern_rows != observed_extern:
        missing = sorted(set(extern_rows) - set(observed_extern))[:3]
        extra = sorted(set(observed_extern) - set(extern_rows))[:3]
        remapped = sorted(
            name
            for name in set(extern_rows) & set(observed_extern)
            if extern_rows[name] != observed_extern[name]
        )[:3]
        _fail(
            "extern_projection_drift",
            f"missing={missing} extra={extra} remapped={remapped}",
        )

    manifest = _parse_manifest(manifest_data, args.manifest)
    expected_manifest = {
        "extractor": "lean-reference-environment-walk-v2",
        "extern-census-sha256": hashlib.sha256(extern_data).hexdigest(),
        "builtin-environment-sha256": hashlib.sha256(
            b"".join(observed_data)
        ).hexdigest(),
        "builtin-partition-sha256": hashlib.sha256(partition_data).hexdigest(),
        "partition-policy-sha256": policy_sha256,
        "constant-count": str(observed_count),
        "extern-count": str(extern_count),
        "module-count": str(
            _required_int(observed_meta, "module_count", args.observed[0])
        ),
        "attribute-count": str(
            _required_int(observed_meta, "attribute_count", args.observed[0])
        ),
        "toolchain-api-count": str(class_counts["toolchain-api"]),
        "library-code-count": str(class_counts["library-code"]),
        "user-facing-data-count": str(class_counts["user-facing-data"]),
        "unresolved-count": "0",
    }
    if manifest != expected_manifest:
        differing = sorted(
            key
            for key in set(manifest) | set(expected_manifest)
            if manifest.get(key) != expected_manifest.get(key)
        )
        _fail("manifest_drift", f"fields={differing}")
    return {
        "constants": observed_count,
        "externs": extern_count,
        "toolchain_api": class_counts["toolchain-api"],
        "library_code": class_counts["library-code"],
        "user_facing_data": class_counts["user-facing-data"],
        "unresolved": 0,
        "manifest_root": hashlib.sha256(
            manifest_data[: manifest_data.rfind(b"manifest-root\tsha256:")]
        ).hexdigest(),
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--root", type=Path, default=Path(__file__).resolve().parents[2]
    )
    parser.add_argument("--extern", type=Path)
    parser.add_argument("--observed", type=Path, action="append")
    parser.add_argument("--partition", type=Path)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--policy", type=Path)
    args = parser.parse_args()
    args.extern = args.extern or args.root / "contracts/extern_census.tsv"
    args.observed = args.observed or [
        args.root / "contracts/builtin_environment.tsv",
        args.root / "contracts/builtin_environment.001.tsv",
        args.root / "contracts/builtin_environment.002.tsv",
    ]
    args.partition = args.partition or args.root / "contracts/builtin_partition.tsv"
    args.manifest = (
        args.manifest or args.root / "contracts/EXTERN_BUILTIN_ENVIRONMENT.txt"
    )
    args.policy = args.policy or args.root / "ci/BUILTIN_PARTITION_POLICY.txt"
    return args


def main() -> int:
    try:
        result = validate(parse_args())
    except CensusError as error:
        print(f"extern-builtin-census: reject {error}", file=sys.stderr)
        return 1
    except (OSError, UnicodeError, ValueError) as error:
        print(
            f"extern-builtin-census: inconclusive reason=validator_fault: {error}",
            file=sys.stderr,
        )
        return 2
    print(
        "extern-builtin-census: pass "
        + " ".join(f"{key}={value}" for key, value in result.items())
    )
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
        print(
            "extern-builtin-census: sealed_interpreter_unsealed_startup",
            file=sys.stderr,
        )
        raise SystemExit(2)
    if hostile_python:
        print(
            "extern-builtin-census: sealed_interpreter_hostile_environment names="
            + ",".join(hostile_python),
            file=sys.stderr,
        )
        raise SystemExit(2)
    raise SystemExit(main())
