#!/usr/bin/env -S python3 -I -S
"""Independently validate the ref-vs-ref semantic artifacts and final E2E log.

The writer invokes this validator twice:

* ``preterminal`` checks the closed semantic-step roster and retained plant
  artifacts before the validation step itself is admitted.
* ``final`` re-reads the completed ``fln.e2e/2`` log after its sole terminal
  record exists.  The shared evidence validator and bundle validator then add
  their own independent checks before publication.

The two phases make the ordering explicit: a validator cannot truthfully claim
to have read a final log when ``run_end`` has not been written yet.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import sys
from pathlib import Path
from typing import Any, Callable

SCHEMA = "fln.e2e/2"
BEAD = "fln-euo"
SCENARIO = "reference_reference_no_mock_e2e"
VALIDATION_SCHEMA = "fln.reference-reference-validation/2"
MAX_LOG_BYTES = 2 * 1024 * 1024
MAX_ARTIFACT_BYTES = 16 * 1024 * 1024

DOMAIN_STEPS = (
    "oracle_binding",
    "reference_run_a",
    "reference_run_b",
    "determinism",
    "baseline",
    "seeded_divergence_artifact",
    "seeded_divergence_line",
    "seeded_divergence_subline",
    "seeded_divergence_diagnostic",
    "seeded_divergence_exit",
    "non_authoritative_outcome",
    "recovery",
)
FINAL_STEPS = (*DOMAIN_STEPS, "bundle_validation")
IDENTITY_KEYS = {
    "bead",
    "event",
    "monotonic_ns",
    "run_id",
    "scenario",
    "schema",
    "sequence",
    "wall_time_utc",
}
START_KEYS = IDENTITY_KEYS | {
    "argv",
    "budgets",
    "cache_state",
    "claim_ids",
    "cwd",
    "epoch",
    "gate_ids",
    "host_facts",
    "input_root",
    "invariant_ids",
    "mode",
    "parity_ledger_row",
    "platform",
    "producer_binding",
    "profile",
    "seed",
    "thread_count",
    "vendor_binding",
}
STEP_KEYS = IDENTITY_KEYS | {
    "actual",
    "assertion",
    "expected",
    "expected_child_exit",
    "expected_supervisor_classification",
    "expected_wrapper_exit",
    "final_state",
    "input_root",
    "step_id",
    "subject_final_state",
    "subject_root",
    "supervisor",
    "validation_artifact",
}
TERMINAL_KEYS = IDENTITY_KEYS | {
    "active_step",
    "bundle_commit",
    "cleanup_status",
    "duration_ns",
    "evidence_manifest",
    "evidence_state",
    "final_state",
    "first_divergence",
    "logical_root",
    "process_exit",
    "reason_code",
    "receipt_root",
    "verdict",
}
PLANT_MARKERS = {
    "seeded.diff": b"PLANTED-DIVERGENCE",
    "plant-line.diff": b"PLANT-LINE",
    "plant-subline.diff": b"PLANT-SUBLINE",
    "plant-diagnostic.diff": b"PLANT-DIAGNOSTIC",
    "plant-exit.diff": b"PLANT-EXIT",
}


class ValidationError(Exception):
    """A semantic or evidence-shape refusal."""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValidationError(message)


def regular_file(path: Path, *, max_bytes: int) -> bytes:
    require(not path.is_symlink(), f"{path}: symlink artifacts are refused")
    require(path.is_file(), f"{path}: expected a regular file")
    size = path.stat().st_size
    require(size <= max_bytes, f"{path}: {size} bytes exceeds budget {max_bytes}")
    return path.read_bytes()


def within_artifact_root(raw: Path, artifact_root: Path, *, label: str) -> Path:
    candidate = raw if raw.is_absolute() else artifact_root / raw
    parent = candidate.parent.resolve(strict=True)
    require(
        parent == artifact_root,
        f"{label} escapes the artifact root: {candidate}",
    )
    return parent / candidate.name


def load_log(path: Path) -> tuple[list[dict[str, Any]], str]:
    raw = regular_file(path, max_bytes=MAX_LOG_BYTES)
    require(raw.endswith(b"\n"), f"{path}: NDJSON is not newline terminated")
    records: list[dict[str, Any]] = []
    for number, line in enumerate(raw.splitlines(), 1):
        require(bool(line), f"{path}:{number}: blank NDJSON row")
        try:
            record = json.loads(line)
        except (UnicodeDecodeError, json.JSONDecodeError) as error:
            raise ValidationError(
                f"{path}:{number}: unparseable row: {error}"
            ) from error
        require(isinstance(record, dict), f"{path}:{number}: row is not an object")
        records.append(record)
    require(bool(records), f"{path}: empty run log")
    return records, hashlib.sha256(raw).hexdigest()


def validate_log(
    records: list[dict[str, Any]], *, run_id: str, phase: str
) -> tuple[list[str], str]:
    expected_steps = DOMAIN_STEPS if phase == "preterminal" else FINAL_STEPS
    expected_events = ["run_start", *(["step"] * len(expected_steps))]
    if phase == "final":
        expected_events.append("run_end")

    actual_events = [record.get("event") for record in records]
    require(
        actual_events == expected_events,
        f"{phase}: event roster differs: {actual_events!r}",
    )

    for index, record in enumerate(records):
        prefix = f"record {index + 1}"
        require(record.get("schema") == SCHEMA, f"{prefix}: wrong schema")
        require(record.get("run_id") == run_id, f"{prefix}: mixed run identity")
        require(record.get("bead") == BEAD, f"{prefix}: wrong bead")
        require(record.get("scenario") == SCENARIO, f"{prefix}: wrong scenario")
        require(record.get("sequence") == index, f"{prefix}: non-contiguous sequence")

    start = records[0]
    require(
        set(start) == START_KEYS,
        "run_start shape differs: "
        f"missing={sorted(START_KEYS - set(start))!r} "
        f"extra={sorted(set(start) - START_KEYS)!r}",
    )
    input_root = start.get("input_root")
    require(
        isinstance(input_root, str)
        and input_root.startswith("sha256:")
        and len(input_root) == 71,
        "run_start lacks a canonical input root",
    )

    step_records = records[1 : 1 + len(expected_steps)]
    actual_steps = [record.get("step_id") for record in step_records]
    require(
        actual_steps == list(expected_steps),
        f"{phase}: step roster differs: {actual_steps!r}",
    )
    for record in step_records:
        step = record["step_id"]
        require(
            set(record) == STEP_KEYS,
            f"{step}: step shape differs: "
            f"missing={sorted(STEP_KEYS - set(record))!r} "
            f"extra={sorted(set(record) - STEP_KEYS)!r}",
        )
        require(record.get("assertion") == "pass", f"{step}: assertion is not pass")
        require(
            record.get("expected_supervisor_classification") == "pass"
            and record.get("expected_wrapper_exit") == 0
            and record.get("expected_child_exit") == 0,
            f"{step}: expected supervisor outcome is not the clean control",
        )
        supervisor = record.get("supervisor")
        require(isinstance(supervisor, dict), f"{step}: supervisor is absent")
        require(
            supervisor.get("classification") == "pass"
            and supervisor.get("wrapper_exit") == 0
            and supervisor.get("child_exit") == 0,
            f"{step}: supervisor did not complete cleanly",
        )
        require(
            record.get("input_root") == input_root
            and record.get("final_state") == input_root,
            f"{step}: governed root changed",
        )
        require(
            record.get("subject_root") == record.get("subject_final_state"),
            f"{step}: subject root changed",
        )

    if phase == "final":
        terminal = records[-1]
        require(
            set(terminal) == TERMINAL_KEYS,
            "run_end shape differs: "
            f"missing={sorted(TERMINAL_KEYS - set(terminal))!r} "
            f"extra={sorted(set(terminal) - TERMINAL_KEYS)!r}",
        )
        require(terminal.get("verdict") == "pass", "final verdict is not pass")
        require(terminal.get("process_exit") == 0, "final process exit is not zero")
        require(
            terminal.get("final_state") == input_root
            and terminal.get("logical_root") == input_root,
            "terminal root differs from the run input root",
        )
        require(
            terminal.get("first_divergence") == "none",
            "passing terminal claims a divergence",
        )

    return actual_steps, input_root


def validate_semantic_artifact_names(names: list[str]) -> None:
    expected_suffixes = {".exit", ".stderr", ".stdout"}
    grouped: dict[str, set[str]] = {}
    for name in names:
        require("/" not in name, f"nested semantic artifact is refused: {name}")
        suffix = next(
            (candidate for candidate in expected_suffixes if name.endswith(candidate)),
            None,
        )
        require(suffix is not None, f"telemetry or unknown semantic artifact: {name}")
        stem = name[: -len(suffix)]
        require(bool(stem), f"semantic artifact has no fixture identity: {name}")
        grouped.setdefault(stem, set()).add(suffix)
    require(bool(grouped), "semantic artifact roster is empty")
    for stem, suffixes in grouped.items():
        require(
            suffixes == expected_suffixes,
            f"{stem}: semantic artifact triplet differs: {sorted(suffixes)!r}",
        )


def tree_digest(directory: Path) -> tuple[str, int, list[str]]:
    require(not directory.is_symlink(), f"{directory}: tree root is a symlink")
    require(directory.is_dir(), f"{directory}: tree root is absent")
    digest = hashlib.sha256()
    count = 0
    names: list[str] = []
    for path in sorted(directory.rglob("*"), key=lambda item: item.as_posix()):
        require(not path.is_symlink(), f"{path}: symlink inside semantic tree")
        if path.is_dir():
            continue
        raw = regular_file(path, max_bytes=MAX_ARTIFACT_BYTES)
        relative_text = path.relative_to(directory).as_posix()
        relative = relative_text.encode("utf-8")
        digest.update(len(relative).to_bytes(8, "big"))
        digest.update(relative)
        digest.update(len(raw).to_bytes(8, "big"))
        digest.update(raw)
        count += 1
        names.append(relative_text)
    require(count > 0, f"{directory}: empty semantic tree")
    validate_semantic_artifact_names(names)
    return digest.hexdigest(), count, names


def negative_controls(
    records: list[dict[str, Any]],
    *,
    run_id: str,
    phase: str,
    semantic_names: list[str],
) -> list[str]:
    killed: list[str] = []

    def reject_record_case(
        name: str, edit: Callable[[list[dict[str, Any]]], None]
    ) -> None:
        candidate = copy.deepcopy(records)
        edit(candidate)
        try:
            validate_log(candidate, run_id=run_id, phase=phase)
        except ValidationError:
            killed.append(name)
        else:
            raise ValidationError(f"negative control survived: {name}")

    reject_record_case(
        "extra_field",
        lambda rows: rows[1].update(unreviewed_field="surplus"),
    )

    def remove_actual(rows: list[dict[str, Any]]) -> None:
        rows[1].pop("actual")

    reject_record_case("missing_field", remove_actual)

    def reorder_steps(rows: list[dict[str, Any]]) -> None:
        rows[1], rows[2] = rows[2], rows[1]
        for index, row in enumerate(rows):
            row["sequence"] = index

    reject_record_case("broken_step_order", reorder_steps)
    reject_record_case("silent_truncation", lambda rows: rows.pop())
    reject_record_case(
        "foreign_run_linkage",
        lambda rows: rows[1].update(run_id="foreign-run"),
    )

    def mismatch_final_state(rows: list[dict[str, Any]]) -> None:
        target = rows[-1] if phase == "final" else rows[1]
        target["final_state"] = f"sha256:{'0' * 64}"

    reject_record_case("final_state_mismatch", mismatch_final_state)

    def duplicate_step(rows: list[dict[str, Any]]) -> None:
        rows.insert(2, copy.deepcopy(rows[1]))
        for index, row in enumerate(rows):
            row["sequence"] = index

    reject_record_case("duplicate_step", duplicate_step)

    try:
        validate_semantic_artifact_names([*semantic_names, "timing.telemetry.ndjson"])
    except ValidationError:
        killed.append("semantic_telemetry_mixing")
    else:
        raise ValidationError("negative control survived: semantic_telemetry_mixing")

    return killed


def validate_plants(artifact_root: Path) -> dict[str, str]:
    ledger_path = artifact_root / "plant-digests.txt"
    ledger = regular_file(ledger_path, max_bytes=16_384)
    require(ledger.endswith(b"\n"), f"{ledger_path}: digest ledger is truncated")
    observed: dict[str, str] = {}
    for number, raw in enumerate(ledger.decode("ascii").splitlines(), 1):
        fields = raw.split()
        require(len(fields) == 2, f"{ledger_path}:{number}: malformed digest row")
        digest, name = fields
        require(
            len(digest) == 64 and all(char in "0123456789abcdef" for char in digest),
            f"{ledger_path}:{number}: malformed SHA-256",
        )
        require(
            name not in observed, f"{ledger_path}:{number}: duplicate artifact {name}"
        )
        require(
            name in PLANT_MARKERS, f"{ledger_path}:{number}: unknown artifact {name}"
        )
        path = within_artifact_root(Path(name), artifact_root, label="plant artifact")
        payload = regular_file(path, max_bytes=MAX_ARTIFACT_BYTES)
        require(
            # ubs:ignore — public artifact digest.
            hashlib.sha256(payload).hexdigest()
            == digest,  # ubs:ignore — public artifact digest.
            f"{name}: retained bytes differ from the digest ledger",
        )
        require(
            PLANT_MARKERS[name] in payload,
            f"{name}: planted body is not surfaced in the retained diff",
        )
        observed[name] = digest
    require(
        set(observed) == set(PLANT_MARKERS),
        f"plant digest roster differs: {sorted(observed)!r}",
    )
    return observed


def write_report(path: Path, artifact_root: Path, report: dict[str, Any]) -> None:
    output = within_artifact_root(path, artifact_root, label="validation output")
    require(not output.exists(), f"{output}: validation output already exists")
    payload = (
        json.dumps(report, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
        + "\n"
    ).encode("ascii")
    with output.open("xb") as handle:
        handle.write(payload)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--phase", choices=("preterminal", "final"), required=True)
    parser.add_argument("--log", required=True)
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--art-dir", required=True)
    parser.add_argument("--output", required=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        artifact_root = Path(args.art_dir).resolve(strict=True)
        require(
            artifact_root.is_dir() and not Path(args.art_dir).is_symlink(),
            "artifact root must be a real directory",
        )
        log_path = within_artifact_root(Path(args.log), artifact_root, label="run log")
        records, log_sha256 = load_log(log_path)
        steps, input_root = validate_log(records, run_id=args.run_id, phase=args.phase)
        plant_digests = validate_plants(artifact_root)
        run_a_root, run_a_files, run_a_names = tree_digest(artifact_root / "run-a")
        run_b_root, run_b_files, run_b_names = tree_digest(artifact_root / "run-b")
        require(
            run_a_root == run_b_root  # ubs:ignore — public semantic tree root.
            and run_a_files == run_b_files  # ubs:ignore — public file count.
            and run_a_names == run_b_names,  # ubs:ignore — public artifact names.
            "Reference semantic trees are not byte-identical",
        )
        controls = negative_controls(
            records,
            run_id=args.run_id,
            phase=args.phase,
            semantic_names=run_a_names,
        )
        report = {
            "artifact_digests": plant_digests,
            "input_root": input_root,
            "phase": args.phase,
            "negative_controls_killed": controls,
            "records": len(records),
            "run_id": args.run_id,
            "run_log_sha256": log_sha256,
            "schema": VALIDATION_SCHEMA,
            "semantic_files": run_a_files,
            "semantic_root": f"sha256:{run_a_root}",
            "steps": steps,
            "verdict": "pass",
        }
        write_report(Path(args.output), artifact_root, report)
    except (OSError, UnicodeError, ValidationError, ValueError) as error:
        print(f"ref-vs-ref validation refused: {error}", file=sys.stderr)
        return 1
    print(
        f"ref-vs-ref {args.phase} validation passed: "
        f"{len(records)} records, {run_a_files} semantic artifacts",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
