from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path, PurePosixPath
from typing import Any

SCHEMA = "fln.agent-handoff/2"
VERIFY_SCHEMA = "fln.agent-handoff-verification/2"
CAPSULE_SCHEMA = "fln.agent-frontier/1"
MAX_ISSUES_BYTES = 64 * 1024 * 1024
MAX_OVERLAY_BYTES = 4 * 1024 * 1024
MAX_SELECTOR_BYTES = 2 * 1024 * 1024
MAX_CAPSULE_COMMENT_BYTES = 2 * 1024 * 1024
MAX_CAPSULES = 4096
MAX_TRACKED_BLOBS = 256
MAX_SEMANTIC_SEAMS = 256
MAX_ACTIVE_PATH_CLAIMS = 16_384
MAX_ACTIVE_SEAM_CLAIMS = 16_384
MAX_NEGATIVE_EVIDENCE = 128
MAX_RECENT_COMMITS = 64
MAX_READY_CANDIDATES = 100
MAX_EVIDENCE_FILES = 512
MAX_OUTPUT_BYTES = 4 * 1024 * 1024
MAX_VERIFY_BYTES = MAX_OUTPUT_BYTES
HEX40 = re.compile(r"^[0-9a-f]{40}$")
BEAD_TRAILER = re.compile(r"^Beads?:\s*(.+?)\s*$", re.IGNORECASE)
CONTROL_PATHS = (
    ".beads/issues.jsonl",
    "AGENTS.md",
    "README.md",
    "COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md",
    "SUITE.lock",
    "AGENT_FRONTIER_PROTOCOL.md",
    "IMPLEMENTATION_STATUS.md",
    "CHANGELOG.md",
    "scripts/frontier_select.py",
    "scripts/agent_handoff.py",
    "scripts/agent_handoff_lib/__init__.py",
    "scripts/agent_handoff_lib/common.py",
    "scripts/agent_handoff_lib/git_state.py",
    "scripts/agent_handoff_lib/capsules.py",
    "scripts/agent_handoff_lib/snapshot.py",
    "scripts/agent_handoff_lib/cli.py",
    "scripts/test_agent_handoff.py",
    "scripts/check_agent_handoff.sh",
    "docs/AGENT_HANDOFF.md",
)


class HandoffError(Exception):
    pass


def reject_duplicate_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise HandoffError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


DECODER = json.JSONDecoder(object_pairs_hook=reject_duplicate_pairs)


def canonical_json(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        + "\n"
    ).encode("utf-8")


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def die(reason: str, code: int = 2, *, schema: str = SCHEMA) -> int:
    sys.stderr.buffer.write(
        canonical_json({"schema": schema, "outcome": "refused", "reason": reason})
    )
    return code


def bounded_read(path: Path, limit: int, label: str) -> bytes:
    try:
        with path.open("rb") as handle:
            data = handle.read(limit + 1)
    except OSError as exc:
        raise HandoffError(f"cannot read {label} {path}: {exc}") from exc
    if len(data) > limit:
        raise HandoffError(f"{label} exceeds the {limit}-byte ceiling: {path}")
    return data


def load_json_bytes(data: bytes, label: str) -> Any:
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise HandoffError(f"{label} is not valid UTF-8: {exc}") from exc
    try:
        value, end = DECODER.raw_decode(text)
    except (json.JSONDecodeError, HandoffError) as exc:
        raise HandoffError(
            f"{label} is not valid duplicate-free JSON: {exc}"
        ) from exc
    if text[end:].strip():
        raise HandoffError(f"{label} has trailing non-whitespace content")
    return value


def safe_relative_path(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise HandoffError(f"{label} must be a non-empty path string")
    if any(character in value for character in ("\x00", "\n", "\r", "\t", "\\")):
        raise HandoffError(f"{label} contains a forbidden path character")
    path = PurePosixPath(value)
    if path.is_absolute() or any(part in {"", ".", ".."} for part in path.parts):
        raise HandoffError(
            f"{label} must be a normalized repository-relative path"
        )
    return path.as_posix()


def require_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise HandoffError(f"{label} must be a non-empty string")
    if "\x00" in value:
        raise HandoffError(f"{label} must not contain NUL")
    return value


def require_bool(value: Any, label: str) -> bool:
    if not isinstance(value, bool):
        raise HandoffError(f"{label} must be boolean")
    return value


def require_int(value: Any, label: str, minimum: int, maximum: int) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or not minimum <= value <= maximum:
        raise HandoffError(f"{label} must be an integer in [{minimum}, {maximum}]")
    return value


def require_optional_string(value: Any, label: str) -> str | None:
    if value is None:
        return None
    return require_string(value, label)


def require_string_list(
    value: Any,
    label: str,
    *,
    maximum: int,
    allow_empty: bool = True,
) -> list[str]:
    if not isinstance(value, list):
        raise HandoffError(f"{label} must be an array")
    if len(value) > maximum:
        raise HandoffError(f"{label} exceeds the {maximum}-item ceiling")
    if not allow_empty and not value:
        raise HandoffError(f"{label} must not be empty")
    result: list[str] = []
    for index, item in enumerate(value):
        result.append(require_string(item, f"{label}[{index}]"))
    if len(set(result)) != len(result):
        raise HandoffError(f"{label} must not contain duplicates")
    return result


def git(
    repo: Path, *arguments: str, check: bool = True
) -> subprocess.CompletedProcess[str]:
    environment = os.environ.copy()
    environment.update({"LC_ALL": "C", "LANG": "C"})
    try:
        process = subprocess.run(
            ["git", *arguments],
            cwd=repo,
            env=environment,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=20,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise HandoffError(
            f"git {' '.join(arguments)} failed to execute: {exc}"
        ) from exc
    if check and process.returncode != 0:
        detail = process.stderr.strip() or process.stdout.strip() or "unknown git failure"
        raise HandoffError(f"git {' '.join(arguments)} failed: {detail}")
    return process


def repository_root(candidate: Path) -> Path:
    candidate = candidate.resolve()
    root = Path(git(candidate, "rev-parse", "--show-toplevel").stdout.strip()).resolve()
    if not root.is_dir():
        raise HandoffError(f"git reported a non-directory repository root: {root}")
    return root


def issue_rows_bytes(raw: bytes, label: str = "Beads issue store") -> tuple[list[dict[str, Any]], str]:
    rows: list[dict[str, Any]] = []
    for line_number, raw_line in enumerate(raw.splitlines(), 1):
        if not raw_line.strip():
            continue
        value = load_json_bytes(raw_line, f"{label} line {line_number}")
        if not isinstance(value, dict):
            raise HandoffError(f"{label} line {line_number} must be an object")
        rows.append(value)
    if not rows:
        raise HandoffError(f"{label} contains no issue rows")
    return rows, sha256_hex(raw)


def issue_rows(path: Path) -> tuple[list[dict[str, Any]], str]:
    raw = bounded_read(path, MAX_ISSUES_BYTES, "Beads issue store")
    return issue_rows_bytes(raw)


def environment_facts() -> dict[str, Any]:
    facts: dict[str, Any] = {"python": sys.version.split()[0]}
    for name in ("git", "cargo", "rustc", "br", "bd", "gh"):
        executable = shutil.which(name)
        facts[name] = {"available": executable is not None}
        if executable is None:
            continue
        try:
            process = subprocess.run(
                [executable, "--version"],
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                timeout=3,
                check=False,
            )
        except (OSError, subprocess.TimeoutExpired):
            continue
        lines = process.stdout.splitlines()
        if lines:
            facts[name]["version"] = lines[0][:200]
    return facts


def write_no_clobber(path: Path, payload: bytes) -> None:
    parent = path.parent
    if not parent.is_dir():
        raise HandoffError(f"output parent directory does not exist: {parent}")
    temporary: Path | None = None
    try:
        descriptor, temporary_name = tempfile.mkstemp(
            prefix=f".{path.name}.handoff-", dir=parent
        )
        temporary = Path(temporary_name)
        os.fchmod(descriptor, 0o644)
        with os.fdopen(descriptor, "wb", closefd=True) as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        try:
            os.link(temporary, path)
        except OSError as exc:
            raise HandoffError(f"refusing to replace output path {path}: {exc}") from exc
        try:
            directory_descriptor = os.open(parent, os.O_RDONLY)
        except OSError:
            directory_descriptor = None
        if directory_descriptor is not None:
            try:
                try:
                    os.fsync(directory_descriptor)
                except OSError:
                    pass
            finally:
                os.close(directory_descriptor)
    except HandoffError:
        raise
    except OSError as exc:
        raise HandoffError(f"cannot publish output path {path}: {exc}") from exc
    finally:
        if temporary is not None:
            try:
                temporary.unlink()
            except FileNotFoundError:
                pass
            except OSError:
                pass
