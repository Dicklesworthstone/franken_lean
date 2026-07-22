#!/usr/bin/env python3
"""Fail-closed evidence utilities for FrankenLean's shell quality gates.

This is test/CI apparatus, not a FrankenLean runtime component.  It centralizes the
parts that shell is particularly bad at: JSON encoding and validation, bounded
subprocess capture that continues draining after truncation, process-tree cancellation,
canonical input hashing, and write-once artifact manifests.

Published files are claimed with no-follow ``O_EXCL`` opens and never overwritten.
An interrupted write deliberately remains invalid at its final path: validation fails
closed, the evidence is retained, and no cleanup/deletion is attempted.
"""

from __future__ import annotations

import argparse
import ctypes
import datetime as dt
import fcntl
import hashlib
import hmac
import json
import os
import platform
import re
import resource
import signal
import stat
import subprocess
import sys
import threading
import time
from pathlib import Path
from typing import Any, Iterable, Sequence


PASS = 0
FAIL = 1
SETUP_FAILURE = 2
INCONCLUSIVE = 3
CANCELLED = 4

RUN_SCHEMAS = {"fln.check/2", "fln.e2e/2"}
CHECK_STAGE_ORDER = [
    "evidence-self-test",
    "shellcheck",
    "fmt",
    "check",
    "clippy",
    "test",
    "structure-guard",
    "vendor-tree",
    "ubs",
]
CHECK_SELF_TEST_ORDER = [*CHECK_STAGE_ORDER, "cancel-term"]
E2E_STEP_ORDERS = {
    "closure_audit": [
        "build_guard",
        "freeze_guard",
        "real_closure",
        "copy_seeded_fixture",
        "seeded_registry_package",
        "copy_recovery_fixture",
        "closure_recovery",
        "final_real_recheck",
    ],
    "structure_gate": [
        "build_guard",
        "verify_built_guard",
        "freeze_guard",
        "verify_frozen_guard",
        "real_workspace",
        "robot_setup_failure",
        "copy_unacknowledged",
        "seeded_unacknowledged",
        "copy_acknowledged",
        "seeded_acknowledged",
        "copy_dependency_recovery",
        "dependency_recovery",
        "copy_unledgered",
        "seeded_unledgered",
        "copy_ledgered_recovery",
        "ledger_recovery",
        "copy_exported",
        "seeded_export",
        "copy_export_recovery",
        "export_recovery",
        "resource_exhaustion",
        "resource_recovery",
        "cancellation",
        "cancellation_recovery",
        "final_real_recheck",
    ],
}
SHA256_HEX = re.compile(r"[0-9a-f]{64}")

MAX_RECORD_BYTES = 1_048_576
MAX_LOG_BYTES = 67_108_864
SECRET_KEY = re.compile(
    r"(?i)(authorization|bearer|password|passwd|secret|token|api[_-]?key|private[_-]?key)"
)


class EvidenceError(RuntimeError):
    """A fail-closed evidence production or validation error."""


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat(timespec="milliseconds")


def canonical_json(value: Any) -> bytes:
    return (
        json.dumps(
            value,
            allow_nan=False,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )
        + "\n"
    ).encode("utf-8")


def reject_json_constant(value: str) -> None:
    raise EvidenceError(f"non-finite JSON number is forbidden: {value}")


def unique_json_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    value: dict[str, Any] = {}
    for key, item in pairs:
        if key in value:
            raise EvidenceError(f"duplicate JSON key: {key}")
        value[key] = item
    return value


def parse_json(data: bytes | str, *, subject: str) -> Any:
    try:
        return json.loads(
            data,
            object_pairs_hook=unique_json_object,
            parse_constant=reject_json_constant,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise EvidenceError(f"malformed JSON in {subject}: {error}") from error


def lexical_absolute(path: Path) -> Path:
    """Return an absolute lexical path without following a symlink component."""
    return Path(os.path.abspath(os.fspath(path)))


def require_within(path: Path, root: Path, *, label: str) -> Path:
    absolute = lexical_absolute(path)
    root_absolute = lexical_absolute(root)
    try:
        absolute.relative_to(root_absolute)
    except ValueError as error:
        raise EvidenceError(f"{label} escapes artifact root: {absolute}") from error
    return absolute


def open_directory_nofollow(path: Path, *, create: bool) -> tuple[Path, int]:
    """Open a directory through no-follow dirfds, optionally creating components."""
    absolute = lexical_absolute(path)
    if os.name != "posix" or not hasattr(os, "O_NOFOLLOW"):
        raise EvidenceError("evidence publication requires POSIX O_NOFOLLOW support")
    flags = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC
    descriptor = os.open(absolute.anchor, flags)
    try:
        for component in absolute.parts[1:]:
            try:
                child = os.open(component, flags, dir_fd=descriptor)
            except FileNotFoundError:
                if not create:
                    raise
                try:
                    os.mkdir(component, 0o755, dir_fd=descriptor)
                except FileExistsError:
                    # A racing creator is accepted only if the no-follow open below
                    # proves that it created a real directory, not a symlink.
                    pass
                child = os.open(component, flags, dir_fd=descriptor)
            os.close(descriptor)
            descriptor = child
        return absolute, descriptor
    except BaseException:
        os.close(descriptor)
        raise


def open_regular_nofollow(path: Path) -> tuple[Path, int]:
    absolute = lexical_absolute(path)
    _parent, parent_fd = open_directory_nofollow(absolute.parent, create=False)
    try:
        descriptor = os.open(
            absolute.name,
            os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC,
            dir_fd=parent_fd,
        )
    finally:
        os.close(parent_fd)
    facts = os.fstat(descriptor)
    if not stat.S_ISREG(facts.st_mode):
        os.close(descriptor)
        raise EvidenceError(f"evidence path is not a regular file: {absolute}")
    return absolute, descriptor


def stable_file_facts(
    path: Path, *, max_bytes: int | None = None
) -> tuple[bytes, int, str]:
    """Read one immutable snapshot and reject concurrent mutation."""
    absolute, descriptor = open_regular_nofollow(path)
    try:
        before = os.fstat(descriptor)
        if max_bytes is not None and before.st_size > max_bytes:
            raise EvidenceError(f"file exceeds {max_bytes} bytes: {absolute}")
        chunks: list[bytes] = []
        digest = hashlib.sha256()
        total = 0
        while True:
            block = os.read(descriptor, 1_048_576)
            if not block:
                break
            total += len(block)
            if max_bytes is not None and total > max_bytes:
                raise EvidenceError(f"file exceeds {max_bytes} bytes: {absolute}")
            digest.update(block)
            chunks.append(block)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    stable_fields = ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_ctime_ns")
    if any(getattr(before, field) != getattr(after, field) for field in stable_fields):
        raise EvidenceError(f"file changed while being read: {absolute}")
    if total != before.st_size:
        raise EvidenceError(f"file size changed while being read: {absolute}")
    return b"".join(chunks), total, digest.hexdigest()


def stable_symlink_facts(path: Path) -> tuple[bytes, int, str]:
    absolute = lexical_absolute(path)
    before = absolute.lstat()
    if not stat.S_ISLNK(before.st_mode):
        raise EvidenceError(f"canonical link changed type: {absolute}")
    target = os.fsencode(os.readlink(absolute))
    after = absolute.lstat()
    stable_fields = ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_ctime_ns")
    if any(getattr(before, field) != getattr(after, field) for field in stable_fields):
        raise EvidenceError(f"symlink changed while being read: {absolute}")
    return target, len(target), hashlib.sha256(target).hexdigest()


def write_new(path: Path, data: bytes, mode: int = 0o644) -> None:
    """Claim an absent path with O_EXCL and durably write it exactly once.

    A failed write deliberately leaves an invalid/incomplete final path.  It is never
    renamed over another producer's file and is rejected by bundle validation.
    """
    absolute = lexical_absolute(path)
    _parent, parent_fd = open_directory_nofollow(absolute.parent, create=True)
    try:
        descriptor = os.open(
            absolute.name,
            os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_CLOEXEC,
            mode,
            dir_fd=parent_fd,
        )
    except BaseException:
        os.close(parent_fd)
        raise
    try:
        view = memoryview(data)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                raise EvidenceError(f"short write while publishing {absolute}")
            view = view[written:]
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
        os.fsync(parent_fd)
        os.close(parent_fd)


def append_record(
    path: Path, record: dict[str, Any], *, must_be_new: bool = False
) -> None:
    """Append and fsync one canonically encoded NDJSON record."""
    data = canonical_json(record)
    if len(data) > MAX_RECORD_BYTES:
        raise EvidenceError(f"record exceeds {MAX_RECORD_BYTES} bytes")
    absolute = lexical_absolute(path)
    _parent, parent_fd = open_directory_nofollow(absolute.parent, create=True)
    flags = os.O_WRONLY | os.O_APPEND | os.O_CREAT | os.O_NOFOLLOW | os.O_CLOEXEC
    if must_be_new:
        flags |= os.O_EXCL
    try:
        descriptor = os.open(absolute.name, flags, 0o644, dir_fd=parent_fd)
    except BaseException:
        os.close(parent_fd)
        raise
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise EvidenceError(f"NDJSON path is not a regular file: {absolute}")
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        written = os.write(descriptor, data)
        if written != len(data):
            raise EvidenceError(f"short append while writing {absolute}")
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
        os.fsync(parent_fd)
        os.close(parent_fd)


def redact_arg(arg: str) -> tuple[str, bool]:
    if "=" in arg:
        key, _value = arg.split("=", 1)
        if SECRET_KEY.search(key):
            return f"{key}=<redacted>", True
    if SECRET_KEY.search(arg) and (":" in arg or " " in arg or len(arg) > 80):
        return "<redacted>", True
    return arg, False


def redacted_argv(argv: Sequence[str]) -> tuple[list[str], bool]:
    result: list[str] = []
    redacted = False
    redact_next = False
    for arg in argv:
        if redact_next:
            result.append("<redacted>")
            redacted = True
            redact_next = False
            continue
        rendered, changed = redact_arg(arg)
        result.append(rendered)
        redacted = redacted or changed
        if arg.startswith("-") and SECRET_KEY.search(arg) and "=" not in arg:
            redact_next = True
    return result, redacted


class BoundedCapture:
    def __init__(self, limit: int) -> None:
        if limit < 256:
            raise EvidenceError("capture limit must be at least 256 bytes")
        self.limit = limit
        self.total = 0
        self.digest = hashlib.sha256()
        self._small: bytearray | None = bytearray()
        self._head = bytearray()
        self._tail = bytearray()
        self._head_limit = limit // 2
        self._tail_limit = limit - self._head_limit
        self._lock = threading.Lock()

    def feed(self, data: bytes) -> None:
        with self._lock:
            self.total += len(data)
            self.digest.update(data)
            if self._small is not None:
                if len(self._small) + len(data) <= self.limit:
                    self._small.extend(data)
                    return
                combined = bytes(self._small) + data
                self._head.extend(combined[: self._head_limit])
                self._tail.extend(combined[-self._tail_limit :])
                self._small = None
                return
            if len(self._head) < self._head_limit:
                need = self._head_limit - len(self._head)
                self._head.extend(data[:need])
                data = data[need:]
            if data:
                combined_tail = bytes(self._tail) + data
                self._tail = bytearray(combined_tail[-self._tail_limit :])

    @property
    def truncated(self) -> bool:
        return self._small is None

    def render(self) -> tuple[bytes, int, int]:
        with self._lock:
            if self._small is not None:
                data = bytes(self._small)
                return data, len(data), 0
            omitted = max(0, self.total - len(self._head) - len(self._tail))
            marker = f"\n...[{omitted} bytes omitted; {self.total} total]...\n".encode()
            available = max(0, self.limit - len(marker))
            head_len = min(len(self._head), available // 2)
            tail_len = min(len(self._tail), available - head_len)
            data = bytes(self._head[:head_len]) + marker + bytes(self._tail[-tail_len:])
            if len(data) > self.limit:
                raise EvidenceError("internal capture bound violation")
            return data, head_len, tail_len

    def facts(
        self, artifact: str, retained: int, head: int, tail: int
    ) -> dict[str, Any]:
        return {
            "artifact": artifact,
            "sha256": self.digest.hexdigest(),
            "retained_sha256": None,
            "total_bytes": self.total,
            "retained_bytes": retained,
            "head_bytes": head,
            "tail_bytes": tail,
            "truncated": self.truncated,
        }


def drain(pipe: Any, capture: BoundedCapture, errors: list[str], label: str) -> None:
    try:
        while True:
            block = pipe.read(65_536)
            if not block:
                break
            capture.feed(block)
    except BaseException as error:  # thread failure must become typed harness failure
        errors.append(f"{label} drain failed: {error}")
    finally:
        try:
            pipe.close()
        except OSError as error:
            errors.append(f"{label} close failed: {error}")


def process_alive(pid: int) -> bool:
    facts = proc_stat_facts(pid)
    return facts is not None and facts[0] != "Z"


def proc_stat_facts(pid: int) -> tuple[str, int, int] | None:
    """Return Linux process state, process group, and start ticks."""
    try:
        data = Path(f"/proc/{pid}/stat").read_text(encoding="ascii")
    except FileNotFoundError:
        return None
    except (OSError, UnicodeError) as error:
        raise EvidenceError(f"cannot inspect process {pid}: {error}") from error
    close = data.rfind(")")
    if close < 0:
        raise EvidenceError(f"malformed Linux stat record for process {pid}")
    fields = data[close + 2 :].split()
    if len(fields) < 20:
        raise EvidenceError(f"short Linux stat record for process {pid}")
    try:
        return fields[0], int(fields[2]), int(fields[19])
    except ValueError as error:
        raise EvidenceError(f"malformed Linux stat facts for process {pid}") from error


def enable_child_subreaper() -> None:
    """Make orphaned grandchildren observable and reapable by this supervisor."""
    if sys.platform != "linux":
        raise EvidenceError("process-tree supervision currently requires Linux")
    libc = ctypes.CDLL(None, use_errno=True)
    # Linux prctl(PR_SET_CHILD_SUBREAPER, 1). This affects only this short-lived
    # supervisor process and lets it contain double-fork/setsid descendants.
    if libc.prctl(36, 1, 0, 0, 0) != 0:
        error_number = ctypes.get_errno()
        raise EvidenceError(f"cannot enable child subreaper: errno {error_number}")


def proc_children(pid: int) -> set[int]:
    path = Path(f"/proc/{pid}/task/{pid}/children")
    try:
        raw = path.read_text(encoding="ascii").strip()
    except FileNotFoundError:
        return set()
    except (OSError, UnicodeError) as error:
        raise EvidenceError(f"cannot inspect descendants of {pid}: {error}") from error
    if not raw:
        return set()
    try:
        return {int(value) for value in raw.split()}
    except ValueError as error:
        raise EvidenceError(f"malformed Linux children list for {pid}") from error


def descendant_closure(roots: Iterable[int]) -> set[int]:
    pending = list(roots)
    found: set[int] = set()
    while pending:
        parent = pending.pop()
        for child in proc_children(parent):
            if child not in found:
                found.add(child)
                pending.append(child)
    return found


def live_process_group_members(pgid: int) -> set[int]:
    members: set[int] = set()
    for entry in Path("/proc").iterdir():
        if not entry.name.isdecimal():
            continue
        pid = int(entry.name)
        facts = proc_stat_facts(pid)
        if facts is not None and facts[0] != "Z" and facts[1] == pgid:
            members.add(pid)
    return members


ProcessHandles = dict[int, tuple[int, int]]


def open_process_handle(pid: int) -> tuple[int, int] | None:
    """Bind a Linux PID to its lifetime before it can be signalled."""
    if not hasattr(os, "pidfd_open") or not hasattr(signal, "pidfd_send_signal"):
        raise EvidenceError("process supervision requires Linux pidfd support")
    facts = proc_stat_facts(pid)
    if facts is None or facts[0] == "Z":
        return None
    try:
        descriptor = os.pidfd_open(pid, 0)
    except ProcessLookupError:
        return None
    repeated = proc_stat_facts(pid)
    if repeated != facts or repeated is None or repeated[0] == "Z":
        os.close(descriptor)
        return None
    return facts[2], descriptor


def close_process_handles(handles: ProcessHandles) -> None:
    for _start_ticks, descriptor in handles.values():
        os.close(descriptor)
    handles.clear()


def process_handle_alive(pid: int, handle: tuple[int, int]) -> bool:
    facts = proc_stat_facts(pid)
    return facts is not None and facts[0] != "Z" and facts[2] == handle[0]


def remember_process(pid: int, handles: ProcessHandles) -> bool:
    current = handles.get(pid)
    if current is not None:
        if process_handle_alive(pid, current):
            return True
        os.close(current[1])
        del handles[pid]
    opened = open_process_handle(pid)
    if opened is None:
        return False
    handles[pid] = opened
    return True


def signal_process_handle(
    pid: int, handle: tuple[int, int], signum: int
) -> bool:
    if not process_handle_alive(pid, handle):
        return False
    try:
        signal.pidfd_send_signal(handle[1], signum, None, 0)
        return True
    except ProcessLookupError:
        return False


def live_tree_members(root_pid: int, known: ProcessHandles) -> set[int]:
    # While the leader lives, walk beneath it. Once an intermediate exits, Linux's
    # subreaper reparents its surviving descendants directly to this process.
    for pid, handle in list(known.items()):
        if not process_handle_alive(pid, handle):
            os.close(handle[1])
            del known[pid]
    roots: set[int] = set()
    if root_pid in known and process_handle_alive(root_pid, known[root_pid]):
        roots.add(root_pid)
    roots.update(proc_children(os.getpid()))
    pending = list(roots)
    visited: set[int] = set()
    while pending:
        pid = pending.pop()
        if pid == os.getpid() or pid in visited or not remember_process(pid, known):
            continue
        visited.add(pid)
        for child in proc_children(pid):
            if child not in visited:
                pending.append(child)
    return {
        pid
        for pid, handle in known.items()
        if pid != os.getpid() and process_handle_alive(pid, handle)
    }


def reap_adopted_children() -> None:
    while True:
        try:
            pid, _status = os.waitpid(-1, os.WNOHANG)
        except ChildProcessError:
            return
        if pid <= 0:
            return


def terminate_tree(
    proc: subprocess.Popen[bytes],
    first_signal: int,
    grace_s: float,
    known: ProcessHandles,
) -> tuple[bool, bool, list[int]]:
    term_sent = False
    kill_sent = False
    live = live_tree_members(proc.pid, known)
    for pid in live:
        term_sent = signal_process_handle(pid, known[pid], first_signal) or term_sent
    deadline = time.monotonic() + grace_s
    while time.monotonic() < deadline:
        proc.poll()
        reap_adopted_children()
        live = live_tree_members(proc.pid, known)
        if not live:
            break
        for pid in live:
            signal_process_handle(pid, known[pid], first_signal)
        time.sleep(0.02)
    live = live_tree_members(proc.pid, known)
    if live:
        # Freeze the bound tree before forced termination. Once every discovered
        # process is stopped, no member can fork across the final descendant scan.
        freeze_deadline = time.monotonic() + max(0.25, grace_s)
        while time.monotonic() < freeze_deadline:
            for pid in live:
                signal_process_handle(pid, known[pid], signal.SIGSTOP)
            time.sleep(0.01)
            repeated = live_tree_members(proc.pid, known)
            all_stopped = all(
                (facts := proc_stat_facts(pid)) is not None
                and facts[0] in {"T", "t"}
                and facts[2] == known[pid][0]
                for pid in repeated
            )
            if repeated == live and all_stopped:
                live = repeated
                break
            live = repeated
        for pid in live:
            kill_sent = (
                signal_process_handle(pid, known[pid], signal.SIGKILL) or kill_sent
            )
        kill_deadline = time.monotonic() + max(0.25, grace_s)
        while time.monotonic() < kill_deadline:
            proc.poll()
            reap_adopted_children()
            live = live_tree_members(proc.pid, known)
            if not live:
                break
            for pid in live:
                signal_process_handle(pid, known[pid], signal.SIGKILL)
            time.sleep(0.02)
    survivors = sorted(live_tree_members(proc.pid, known))
    return term_sent, kill_sent, survivors


def run_supervised(
    *,
    argv: Sequence[str],
    cwd: Path,
    metadata_path: Path,
    stdout_path: Path,
    stderr_path: Path,
    readiness_path: Path,
    artifact_root: Path,
    capture_bytes: int,
    output_budget_bytes: int,
    timeout_ms: int,
    grace_ms: int,
    stage_id: str,
    planted: bool,
    semantic_failure_exits: Sequence[int] = (),
    cancel_after_ms: int | None = None,
) -> int:
    if not argv:
        raise EvidenceError("supervisor requires a non-empty argv")
    for label, value in (
        ("capture-bytes", capture_bytes),
        ("output-budget-bytes", output_budget_bytes),
        ("timeout-ms", timeout_ms),
        ("grace-ms", grace_ms),
    ):
        if value <= 0:
            raise EvidenceError(f"{label} must be positive")
    if output_budget_bytes < capture_bytes:
        raise EvidenceError(
            "output budget must be at least the per-stream capture bound"
        )
    semantic_exits = sorted(set(semantic_failure_exits))
    if any(
        not isinstance(value, int)
        or isinstance(value, bool)
        or value <= 0
        or value > 255
        for value in semantic_exits
    ):
        raise EvidenceError(
            "semantic failure exits must be unique integers from 1 through 255"
        )
    artifact_root = lexical_absolute(artifact_root)
    for label, path in (
        ("metadata", metadata_path),
        ("stdout", stdout_path),
        ("stderr", stderr_path),
        ("readiness", readiness_path),
    ):
        require_within(path, artifact_root, label=label)

    started_ns = time.monotonic_ns()
    started_utc = utc_now()
    usage_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    stdout_capture = BoundedCapture(capture_bytes)
    stderr_capture = BoundedCapture(capture_bytes)
    errors: list[str] = []
    cancel_signal: int | None = None
    termination_reason: str | None = None
    term_sent = False
    kill_sent = False
    proc: subprocess.Popen[bytes] | None = None
    child_exit: int | None = None
    child_signal: str | None = None
    watched_signals = (signal.SIGHUP, signal.SIGINT, signal.SIGTERM)
    old_handlers: dict[int, Any] = {
        signum: signal.getsignal(signum) for signum in watched_signals
    }
    known_descendants: ProcessHandles = {}
    survivors: list[int] = []
    readiness_published = False

    def remember_signal(signum: int, _frame: Any) -> None:
        nonlocal cancel_signal
        if cancel_signal is None:
            cancel_signal = signum

    rendered_argv, had_redaction = redacted_argv(argv)
    try:
        enable_child_subreaper()
        for signum in watched_signals:
            signal.signal(signum, remember_signal)
        proc = subprocess.Popen(
            list(argv),
            cwd=cwd,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            start_new_session=True,
        )
        if not remember_process(proc.pid, known_descendants):
            raise EvidenceError("cannot bind child process lifetime")
        child_facts = proc_stat_facts(proc.pid)
        wrapper_facts = proc_stat_facts(os.getpid())
        if child_facts is None or wrapper_facts is None:
            raise EvidenceError("cannot capture process identity facts for readiness")
        write_new(
            readiness_path,
            canonical_json(
                {
                    "schema": "fln.supervisor-readiness/1",
                    "stage_id": stage_id,
                    "wrapper_pid": os.getpid(),
                    "wrapper_start_ticks": wrapper_facts[2],
                    "child_pid": proc.pid,
                    "child_pgid": os.getpgid(proc.pid),
                    "child_start_ticks": child_facts[2],
                    "monotonic_ns": time.monotonic_ns(),
                    "status": "ready",
                }
            ),
        )
        readiness_published = True
        assert proc.stdout is not None and proc.stderr is not None
        out_thread = threading.Thread(
            target=drain,
            args=(proc.stdout, stdout_capture, errors, "stdout"),
            daemon=True,
        )
        err_thread = threading.Thread(
            target=drain,
            args=(proc.stderr, stderr_capture, errors, "stderr"),
            daemon=True,
        )
        out_thread.start()
        err_thread.start()
        deadline_ns = started_ns + timeout_ms * 1_000_000
        synthetic_cancel_ns = (
            started_ns + cancel_after_ms * 1_000_000
            if cancel_after_ms is not None
            else None
        )
        while proc.poll() is None:
            live_tree_members(proc.pid, known_descendants)
            now_ns = time.monotonic_ns()
            if cancel_signal is not None:
                termination_reason = "signal"
            elif synthetic_cancel_ns is not None and now_ns >= synthetic_cancel_ns:
                cancel_signal = signal.SIGTERM
                termination_reason = "signal"
            elif stdout_capture.total + stderr_capture.total > output_budget_bytes:
                termination_reason = "output_budget_exhausted"
            elif now_ns >= deadline_ns:
                termination_reason = "timeout"
            if termination_reason is not None:
                first = cancel_signal if cancel_signal is not None else signal.SIGTERM
                term_sent, kill_sent, survivors = terminate_tree(
                    proc, first, grace_ms / 1000, known_descendants
                )
                break
            time.sleep(0.02)
        child_return = proc.wait()
        lingering = live_tree_members(proc.pid, known_descendants)
        if lingering:
            errors.append(f"descendants outlived group leader: {sorted(lingering)}")
            sent_term, sent_kill, survivors = terminate_tree(
                proc, signal.SIGTERM, grace_ms / 1000, known_descendants
            )
            term_sent = term_sent or sent_term
            kill_sent = kill_sent or sent_kill
        out_thread.join(max(1.0, grace_ms / 1000 + 1.0))
        err_thread.join(max(1.0, grace_ms / 1000 + 1.0))
        if out_thread.is_alive() or err_thread.is_alive():
            errors.append("capture drainer did not terminate after child exit")
            sent_term, sent_kill, survivors = terminate_tree(
                proc, signal.SIGKILL, grace_ms / 1000, known_descendants
            )
            term_sent = term_sent or sent_term
            kill_sent = kill_sent or sent_kill
        if survivors:
            errors.append(f"process-tree termination left survivors: {survivors}")
        if (
            termination_reason is None
            and stdout_capture.total + stderr_capture.total > output_budget_bytes
        ):
            # A very fast producer can exit between monitor polls. Its completed result
            # still exceeded the declared resource budget and therefore remains typed
            # inconclusive rather than being promoted to pass/fail.
            termination_reason = "output_budget_exhausted"
        if child_return < 0:
            child_signal = signal.Signals(-child_return).name
        else:
            child_exit = child_return
    except BaseException as error:
        errors.append(f"supervisor failure: {type(error).__name__}: {error}")
        if proc is not None:
            sent_term, sent_kill, survivors = terminate_tree(
                proc, signal.SIGTERM, grace_ms / 1000, known_descendants
            )
            term_sent = term_sent or sent_term
            kill_sent = kill_sent or sent_kill
            try:
                proc.wait(timeout=max(1.0, grace_ms / 1000 + 1.0))
            except subprocess.TimeoutExpired:
                errors.append("child remained live after supervisor failure")
    finally:
        reap_adopted_children()

    if not readiness_published:
        try:
            write_new(
                readiness_path,
                canonical_json(
                    {
                        "schema": "fln.supervisor-readiness/1",
                        "stage_id": stage_id,
                        "wrapper_pid": os.getpid(),
                        "wrapper_start_ticks": (
                            proc_stat_facts(os.getpid()) or ("", 0, 0)
                        )[2],
                        "child_pid": None,
                        "child_pgid": None,
                        "child_start_ticks": None,
                        "monotonic_ns": time.monotonic_ns(),
                        "status": "spawn_failed",
                    }
                ),
            )
            readiness_published = True
        except BaseException as error:
            errors.append(
                f"readiness publication failure: {type(error).__name__}: {error}"
            )

    # Block cancellation while terminal artifacts are selected and published. The
    # disposition change to SIG_IGN below is the single linearization point: signals
    # pending before it are reflected as cancellation; signals after it are post-commit.
    previous_signal_mask = signal.pthread_sigmask(signal.SIG_BLOCK, watched_signals)
    ended_ns = time.monotonic_ns()
    usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    if survivors and not any("termination left survivors" in error for error in errors):
        errors.append(f"process-tree termination left survivors: {survivors}")
    capture_publication_failed = False
    try:
        out_data, out_head, out_tail = stdout_capture.render()
        err_data, err_head, err_tail = stderr_capture.render()
        write_new(stdout_path, out_data)
        write_new(stderr_path, err_data)
    except BaseException as error:
        errors.append(f"capture publication failure: {type(error).__name__}: {error}")
        capture_publication_failed = True
        out_data, out_head, out_tail = b"", 0, 0
        err_data, err_head, err_tail = b"", 0, 0

    pending = signal.sigpending()
    if cancel_signal is None:
        cancel_signal = next(
            (signum for signum in watched_signals if signum in pending), None
        )

    def classify_terminal() -> tuple[str, str, int]:
        if capture_publication_failed:
            return "internal_fault", "artifact_publication_failure", SETUP_FAILURE
        if errors:
            return "internal_fault", "supervisor_or_capture_failure", SETUP_FAILURE
        if cancel_signal is not None:
            return (
                "cancelled",
                f"signal_{signal.Signals(cancel_signal).name}",
                CANCELLED,
            )
        if termination_reason in {"timeout", "output_budget_exhausted"}:
            return "inconclusive", termination_reason, INCONCLUSIVE
        if child_signal is not None:
            return "inconclusive", f"child_signal_{child_signal}", INCONCLUSIVE
        if child_exit in semantic_exits:
            return "fail", "child_exit_semantic_failure", FAIL
        if child_exit != 0:
            return "internal_fault", "unexpected_child_exit", SETUP_FAILURE
        return "pass", "exit_zero", PASS

    classification, reason_code, wrapper_exit = classify_terminal()

    metadata: dict[str, Any] = {
        "schema": "fln.supervisor/1",
        "stage_id": stage_id,
        "argv": rendered_argv,
        "argv_redacted": had_redaction,
        "cwd": str(cwd),
        "classification": classification,
        "reason_code": reason_code,
        "wrapper_exit": wrapper_exit,
        "child_exit": child_exit,
        "child_signal": child_signal,
        "cancel_signal": signal.Signals(cancel_signal).name if cancel_signal else None,
        "planted": planted,
        "semantic_failure_exits": semantic_exits,
        "started_utc": started_utc,
        "ended_utc": utc_now(),
        "monotonic_start_ns": started_ns,
        "monotonic_end_ns": ended_ns,
        "duration_ns": ended_ns - started_ns,
        "resource": {
            "capture_bytes_per_stream": capture_bytes,
            "output_budget_bytes": output_budget_bytes,
            "timeout_ms": timeout_ms,
            "kill_grace_ms": grace_ms,
            "total_output_bytes": stdout_capture.total + stderr_capture.total,
            "user_cpu_seconds": max(0.0, usage_after.ru_utime - usage_before.ru_utime),
            "system_cpu_seconds": max(
                0.0, usage_after.ru_stime - usage_before.ru_stime
            ),
            "max_rss_kib_observed": usage_after.ru_maxrss,
            "term_sent": term_sent,
            "kill_sent": kill_sent,
            "process_tree_scope": "linux_subreaper_plus_pidfd",
            "surviving_pids": survivors,
        },
        "stdout": stdout_capture.facts(
            stdout_path.name, len(out_data), out_head, out_tail
        ),
        "stderr": stderr_capture.facts(
            stderr_path.name, len(err_data), err_head, err_tail
        ),
        "errors": errors,
        "readiness": readiness_path.name,
        "host": {
            "platform": platform.platform(),
            "machine": platform.machine(),
            "python": platform.python_version(),
        },
    }
    metadata["stdout"]["retained_sha256"] = hashlib.sha256(out_data).hexdigest()
    metadata["stderr"]["retained_sha256"] = hashlib.sha256(err_data).hexdigest()
    metadata_data = canonical_json(metadata)
    # Account for a signal that became pending while the terminal object was built.
    pending = signal.sigpending()
    if cancel_signal is None:
        cancel_signal = next(
            (signum for signum in watched_signals if signum in pending), None
        )
        if cancel_signal is not None:
            classification, reason_code, wrapper_exit = classify_terminal()
            metadata["classification"] = classification
            metadata["reason_code"] = reason_code
            metadata["wrapper_exit"] = wrapper_exit
            metadata["cancel_signal"] = signal.Signals(cancel_signal).name
            metadata_data = canonical_json(metadata)
    for signum in watched_signals:
        signal.signal(signum, signal.SIG_IGN)
    try:
        write_new(metadata_path, metadata_data)
    except BaseException as error:
        fallback = {
            "schema": "fln.supervisor/1",
            "classification": "internal_fault",
            "reason_code": "metadata_publication_failure",
            "metadata_path": str(metadata_path),
            "error": f"{type(error).__name__}: {error}",
        }
        sys.stderr.buffer.write(canonical_json(fallback))
        for signum, handler in old_handlers.items():
            signal.signal(signum, handler)
        signal.pthread_sigmask(signal.SIG_SETMASK, previous_signal_mask)
        close_process_handles(known_descendants)
        return SETUP_FAILURE
    for signum, handler in old_handlers.items():
        signal.signal(signum, handler)
    signal.pthread_sigmask(signal.SIG_SETMASK, previous_signal_mask)
    close_process_handles(known_descendants)
    return wrapper_exit


def load_ndjson_snapshot(path: Path) -> tuple[list[dict[str, Any]], str]:
    data, _size, digest = stable_file_facts(path, max_bytes=MAX_LOG_BYTES)
    records: list[dict[str, Any]] = []
    for number, raw in enumerate(data.splitlines(keepends=True), 1):
        if len(raw) > MAX_RECORD_BYTES:
            raise EvidenceError(f"{path}:{number}: record too large")
        if not raw.endswith(b"\n"):
            raise EvidenceError(f"{path}:{number}: unterminated record")
        value = parse_json(raw, subject=f"{path}:{number}")
        if not isinstance(value, dict):
            raise EvidenceError(f"{path}:{number}: record is not an object")
        records.append(value)
    if not records:
        raise EvidenceError(f"NDJSON is empty: {path}")
    return records, digest


def load_ndjson(path: Path) -> list[dict[str, Any]]:
    records, _digest = load_ndjson_snapshot(path)
    return records


def validate_guard(
    path: Path,
    expected_exit: int,
    expected_verdict: str,
    expected_findings: Sequence[str],
    expected_root: str,
    observed_exit: int,
) -> dict[str, Any]:
    path = lexical_absolute(path)
    records, digest = load_ndjson_snapshot(path)
    for index, record in enumerate(records):
        if record.get("schema") != "structure-guard/2":
            raise EvidenceError(f"{path}:{index + 1}: wrong schema")
    if records[0].get("event") != "run_start":
        raise EvidenceError(f"{path}: first record is not run_start")
    if records[0].get("root") != expected_root:
        raise EvidenceError(f"{path}: guard root does not match the invoked fixture")
    if expected_verdict not in {"pass", "fail", "setup_error"}:
        raise EvidenceError(f"{path}: unsupported expected guard verdict")
    if observed_exit != expected_exit:
        raise EvidenceError(
            f"{path}: observed exit {observed_exit}, expected {expected_exit}"
        )
    terminals = [record for record in records if record.get("event") == "run_end"]
    if len(terminals) != 1 or records[-1] is not terminals[0]:
        raise EvidenceError(f"{path}: expected exactly one final run_end")
    terminal = terminals[0]
    if terminal.get("verdict") != expected_verdict:
        raise EvidenceError(
            f"{path}: verdict {terminal.get('verdict')!r}, expected {expected_verdict!r}"
        )
    if terminal.get("exit_code") != expected_exit:
        raise EvidenceError(
            f"{path}: terminal exit {terminal.get('exit_code')!r}, expected {expected_exit}"
        )
    if expected_verdict in {"pass", "fail"}:
        graph_digest = records[0].get("graph_digest")
        if not isinstance(graph_digest, str) or not graph_digest.startswith("fnv1a64:"):
            raise EvidenceError(f"{path}: guard graph digest is missing")
        if not isinstance(records[0].get("crates"), int) or not isinstance(
            records[0].get("edges"), int
        ):
            raise EvidenceError(f"{path}: guard graph counts are malformed")
    elif records[0].get("graph_digest") is not None:
        raise EvidenceError(f"{path}: setup failure claims a graph digest")
    actual_findings = []
    finding_records = records[1:-1]
    for index, record in enumerate(finding_records, 2):
        if record.get("event") != "finding":
            raise EvidenceError(f"{path}:{index}: non-finding inside guard run")
        if record.get("severity") != "error":
            raise EvidenceError(f"{path}:{index}: guard finding severity is not error")
        if not isinstance(record.get("code"), str) or not isinstance(
            record.get("path"), str
        ):
            raise EvidenceError(f"{path}:{index}: malformed guard finding identity")
        if not isinstance(record.get("detail"), str) or not record["detail"]:
            raise EvidenceError(f"{path}:{index}: guard finding lacks detail")
        raw_path = str(record.get("path"))
        # Current structure-guard findings carry a source line in the path string.
        # Scenario contracts intentionally match code + canonical file path; span
        # accuracy is a separate claim and must not make fixtures line-number brittle.
        canonical_path = re.sub(r":\d+(?::\d+)?$", "", raw_path)
        actual_findings.append(f"{record.get('code')}@{canonical_path}")
    canonical_order = sorted(
        finding_records,
        key=lambda record: (
            str(record.get("code")),
            str(record.get("path")),
            str(record.get("detail")),
        ),
    )
    if finding_records != canonical_order:
        raise EvidenceError(f"{path}: guard findings are not deterministically sorted")
    if actual_findings != list(expected_findings):
        raise EvidenceError(
            f"{path}: exact findings {actual_findings!r}, expected {list(expected_findings)!r}"
        )
    if terminal.get("findings") != len(actual_findings):
        raise EvidenceError(f"{path}: terminal finding count disagrees with records")
    if terminal.get("exit_code") != observed_exit:
        raise EvidenceError(f"{path}: reported and observed exits disagree")
    return {
        "schema": "fln.validation/1",
        "subject": path.name,
        "valid": True,
        "exit_code": expected_exit,
        "verdict": expected_verdict,
        "findings": actual_findings,
        "sha256": digest,
    }


def validate_run(
    path: Path,
    schema: str,
    expected_verdict: str,
    *,
    expected_active_stage: str | None = None,
    expected_planted_stage: str | None = None,
    live_context: bool = True,
) -> dict[str, Any]:
    if schema not in RUN_SCHEMAS:
        raise EvidenceError(f"unsupported run schema: {schema!r}")
    path = lexical_absolute(path)
    records, digest = load_ndjson_snapshot(path)
    if records[0].get("event") != "run_start":
        raise EvidenceError(f"{path}: first record is not run_start")
    terminals = [record for record in records if record.get("event") == "run_end"]
    if len(terminals) != 1 or records[-1] is not terminals[0]:
        raise EvidenceError(f"{path}: expected exactly one final run_end")
    run_id = records[0].get("run_id")
    bead = records[0].get("bead")
    if (
        not isinstance(run_id, str)
        or not run_id
        or not isinstance(bead, str)
        or not bead
    ):
        raise EvidenceError(f"{path}: invalid run identity")
    scenario = records[0].get("scenario")
    if not isinstance(scenario, str) or not scenario:
        raise EvidenceError(f"{path}: scenario identity is missing")
    prior_monotonic = -1
    for index, record in enumerate(records):
        if record.get("schema") != schema:
            raise EvidenceError(f"{path}:{index + 1}: wrong schema")
        if record.get("run_id") != run_id or record.get("bead") != bead:
            raise EvidenceError(f"{path}:{index + 1}: mixed run or bead identity")
        if record.get("scenario") != scenario:
            raise EvidenceError(f"{path}:{index + 1}: mixed scenario identity")
        if record.get("sequence") != index:
            raise EvidenceError(f"{path}:{index + 1}: non-contiguous sequence")
        if not isinstance(record.get("monotonic_ns"), int) or isinstance(
            record.get("monotonic_ns"), bool
        ):
            raise EvidenceError(f"{path}:{index + 1}: missing monotonic_ns")
        if record["monotonic_ns"] < prior_monotonic:
            raise EvidenceError(f"{path}:{index + 1}: monotonic time moved backwards")
        prior_monotonic = record["monotonic_ns"]
        if not isinstance(record.get("wall_time_utc"), str):
            raise EvidenceError(f"{path}:{index + 1}: missing wall_time_utc")
    terminal = terminals[0]
    if terminal.get("verdict") != expected_verdict:
        raise EvidenceError(
            f"{path}: verdict {terminal.get('verdict')!r}, expected {expected_verdict!r}"
        )
    start_required = {
        "argv",
        "cwd",
        "claim_ids",
        "invariant_ids",
        "gate_ids",
        "epoch",
        "mode",
        "profile",
        "platform",
        "host_facts",
        "thread_count",
        "seed",
        "cache_state",
        "input_root",
        "budgets",
        "parity_ledger_row",
        "scenario",
    }
    missing = sorted(key for key in start_required if key not in records[0])
    if missing:
        raise EvidenceError(f"{path}: run_start missing fields {missing!r}")
    for key in ("claim_ids", "invariant_ids", "gate_ids"):
        value = records[0][key]
        if (
            not isinstance(value, list)
            or not value
            or not all(isinstance(item, str) and item for item in value)
        ):
            raise EvidenceError(f"{path}: {key} must be a non-empty string array")
    if not isinstance(records[0]["argv"], list) or not all(
        isinstance(item, str) for item in records[0]["argv"]
    ):
        raise EvidenceError(f"{path}: argv must be a string array")
    if not re.fullmatch(r"sha256:[0-9a-f]{64}", str(records[0]["input_root"])):
        raise EvidenceError(f"{path}: input_root is not a canonical SHA-256 tree root")
    budgets = records[0]["budgets"]
    if (
        not isinstance(budgets, dict)
        or not budgets
        or not all(
            isinstance(value, int) and not isinstance(value, bool) and value > 0
            for value in budgets.values()
        )
    ):
        raise EvidenceError(f"{path}: budgets must be positive integer facts")
    host_facts = records[0]["host_facts"]
    if not isinstance(host_facts, dict) or not all(
        isinstance(host_facts.get(key), str) and host_facts[key]
        for key in ("system", "release", "machine", "python")
    ):
        raise EvidenceError(f"{path}: host facts are incomplete")
    if (
        not isinstance(records[0]["parity_ledger_row"], str)
        or not records[0]["parity_ledger_row"]
    ):
        raise EvidenceError(f"{path}: parity ledger classification is missing")
    if (
        not isinstance(records[0]["thread_count"], int)
        or isinstance(records[0]["thread_count"], bool)
        or records[0]["thread_count"] <= 0
    ):
        raise EvidenceError(f"{path}: thread count must be a positive integer")
    profile = records[0]["profile"]
    allowed_profiles = (
        {
            "local",
            "ci",
            "self-test-driver",
            "self-test-plant",
            "self-test-cancellation",
            "evidence-manifest-self-test",
        }
        if schema == "fln.check/2"
        else {"e2e"}
    )
    if profile not in allowed_profiles:
        raise EvidenceError(f"{path}: unknown run profile {profile!r}")
    if schema == "fln.check/2" and not isinstance(records[0].get("planted"), str):
        raise EvidenceError(f"{path}: planted-stage binding must be a string")
    if schema == "fln.check/2" and profile != "evidence-manifest-self-test":
        if records[0].get("ubs_inventory") != "ubs-inventory.json":
            raise EvidenceError(f"{path}: quality gate lacks its UBS inventory binding")
        validate_ubs_inventory(
            path.parent / "ubs-inventory.json",
            Path(records[0]["cwd"]) if live_context else None,
        )
    if schema == "fln.e2e/2" or profile != "evidence-manifest-self-test":
        if records[0].get("vendor_binding") != "vendor-binding.json":
            raise EvidenceError(f"{path}: run lacks its Reference vendor binding")
        recorded_binding = read_json_object(path.parent / "vendor-binding.json")
        validate_vendor_binding_document(recorded_binding)
        if live_context:
            live_binding = verify_vendor_binding(
                Path(records[0]["cwd"]), "vendor/lean4-src"
            )
            if recorded_binding != live_binding:
                raise EvidenceError(f"{path}: Reference vendor binding is stale")
    terminal_required = {
        "reason_code",
        "process_exit",
        "duration_ns",
        "cleanup_status",
        "final_state",
        "evidence_manifest",
        "bundle_commit",
        "evidence_state",
        "logical_root",
        "receipt_root",
        "first_divergence",
    }
    missing = sorted(key for key in terminal_required if key not in terminal)
    if missing:
        raise EvidenceError(f"{path}: run_end missing fields {missing!r}")
    expected_process_exits = {
        "pass": {0},
        "fail": {1},
        "internal_fault": {2},
        "inconclusive": {3},
        "cancelled": {4, 129, 130, 143},
    }
    if expected_verdict not in expected_process_exits:
        raise EvidenceError(f"{path}: unknown terminal verdict {expected_verdict!r}")
    if terminal.get("process_exit") not in expected_process_exits[expected_verdict]:
        raise EvidenceError(f"{path}: verdict and process_exit disagree")
    if not isinstance(terminal.get("duration_ns"), int) or terminal["duration_ns"] < 0:
        raise EvidenceError(f"{path}: terminal duration is malformed")
    for key in (
        "reason_code",
        "active_stage" if schema == "fln.check/2" else "active_step",
    ):
        if not isinstance(terminal.get(key), str) or not terminal[key]:
            raise EvidenceError(f"{path}: terminal {key} is malformed")
    if terminal.get("cleanup_status") != "retained_by_policy":
        raise EvidenceError(f"{path}: terminal cleanup policy is unknown")
    if (
        expected_verdict == "pass"
        and terminal.get("final_state") != records[0]["input_root"]
    ):
        raise EvidenceError(f"{path}: passing run changed its canonical input root")
    if terminal.get("logical_root") != terminal.get("final_state"):
        raise EvidenceError(f"{path}: terminal logical root disagrees with final state")
    if (
        not isinstance(terminal.get("receipt_root"), str)
        or not terminal["receipt_root"]
    ):
        raise EvidenceError(f"{path}: terminal receipt-root classification is missing")
    if expected_verdict == "pass" and terminal.get("first_divergence") != "none":
        raise EvidenceError(f"{path}: passing run claims a first divergence")
    if expected_verdict != "pass" and not isinstance(
        terminal.get("first_divergence"), str
    ):
        raise EvidenceError(f"{path}: failing run lacks first-divergence data")
    if expected_verdict != "pass" and terminal.get("first_divergence") != terminal.get(
        "reason_code"
    ):
        raise EvidenceError(
            f"{path}: first divergence does not identify the terminal reason"
        )
    if terminal.get("evidence_state") != "pending_bundle_commit":
        raise EvidenceError(f"{path}: run terminal must declare pending bundle commit")
    if terminal.get("bundle_commit") != "bundle.complete.json":
        raise EvidenceError(
            f"{path}: run terminal names an unknown bundle commit marker"
        )
    if expected_active_stage is not None:
        active = terminal.get("active_stage", terminal.get("active_step"))
        if active != expected_active_stage:
            raise EvidenceError(
                f"{path}: terminal active item {active!r}, expected {expected_active_stage!r}"
            )

    allowed_events = (
        {"run_start", "stage", "self_test", "run_end"}
        if schema == "fln.check/2"
        else {"run_start", "step", "run_end"}
    )
    seen_ids: set[str] = set()
    for index, record in enumerate(records[1:-1], 2):
        event = record.get("event")
        if event not in allowed_events:
            raise EvidenceError(f"{path}:{index}: unknown event {event!r}")
        if event == "stage":
            required = {"stage", "outcome", "reason_code", "expected", "actual"}
            missing = sorted(key for key in required if key not in record)
            if missing:
                raise EvidenceError(f"{path}:{index}: stage missing {missing!r}")
            if not isinstance(record["stage"], str) or not record["stage"]:
                raise EvidenceError(f"{path}:{index}: invalid stage identity")
            event_id = record["stage"]
            if record["outcome"] != "skipped":
                if record.get("supervisor_available") is False:
                    if (
                        record["outcome"] != "internal_fault"
                        or record.get("reason_code") != "missing_supervisor_metadata"
                        or record.get("wrapper_exit") != SETUP_FAILURE
                    ):
                        raise EvidenceError(
                            f"{path}:{index}: invalid missing-supervisor event"
                        )
                else:
                    validate_supervisor_object(
                        path,
                        index,
                        record.get("supervisor"),
                        expected_stage_id=event_id,
                    )
                    if record["supervisor"]["classification"] != record["outcome"]:
                        raise EvidenceError(
                            f"{path}:{index}: stage/supervisor outcome mismatch"
                        )
                    if (
                        record.get("wrapper_exit")
                        != record["supervisor"]["wrapper_exit"]
                    ):
                        raise EvidenceError(
                            f"{path}:{index}: stage/supervisor exit mismatch"
                        )
            elif (
                event_id != "ubs"
                or records[0]["profile"] == "ci"
                or record.get("reason_code") != "typed_limitation"
                or record.get("expected") != "not_applicable"
                or record.get("actual") != "skipped"
                or not isinstance(record.get("limitation"), str)
                or not record["limitation"]
            ):
                raise EvidenceError(f"{path}:{index}: invalid skipped obligation")
        elif event == "step":
            required = {
                "step_id",
                "assertion",
                "expected",
                "actual",
                "input_root",
                "final_state",
                "validation_artifact",
                "supervisor",
                "expected_supervisor_classification",
                "expected_wrapper_exit",
                "expected_child_exit",
                "subject_root",
                "subject_final_state",
            }
            missing = sorted(key for key in required if key not in record)
            if missing:
                raise EvidenceError(f"{path}:{index}: step missing {missing!r}")
            if not isinstance(record["step_id"], str) or not record["step_id"]:
                raise EvidenceError(f"{path}:{index}: invalid step identity")
            event_id = record["step_id"]
            validate_supervisor_object(
                path, index, record.get("supervisor"), expected_stage_id=event_id
            )
            supervisor = record["supervisor"]
            if record["assertion"] not in {"pass", "fail"}:
                raise EvidenceError(f"{path}:{index}: unknown assertion outcome")
            if record["assertion"] == "pass":
                if (
                    supervisor["classification"]
                    != record["expected_supervisor_classification"]
                ):
                    raise EvidenceError(
                        f"{path}:{index}: unexpected supervisor classification"
                    )
                if supervisor["wrapper_exit"] != record["expected_wrapper_exit"]:
                    raise EvidenceError(
                        f"{path}:{index}: unexpected supervisor wrapper exit"
                    )
                if supervisor["child_exit"] != record["expected_child_exit"]:
                    raise EvidenceError(
                        f"{path}:{index}: unexpected supervised child exit"
                    )
            for root_key in (
                "input_root",
                "final_state",
                "subject_root",
                "subject_final_state",
            ):
                if not re.fullmatch(r"sha256:[0-9a-f]{64}", str(record[root_key])):
                    raise EvidenceError(
                        f"{path}:{index}: {root_key} is not a canonical tree root"
                    )
            if record["subject_root"] != record["subject_final_state"]:
                raise EvidenceError(
                    f"{path}:{index}: step subject changed during assertion"
                )
            if record["assertion"] == "pass" and (
                record["input_root"] != records[0]["input_root"]
                or record["final_state"] != records[0]["input_root"]
            ):
                raise EvidenceError(
                    f"{path}:{index}: passing step used a foreign global root"
                )
            validation_artifact = record["validation_artifact"]
            if validation_artifact != "not_applicable":
                candidate = require_within(
                    path.parent / str(validation_artifact),
                    path.parent,
                    label="validation artifact",
                )
                stable_file_facts(candidate)
        elif event == "self_test":
            required = {"stage", "ok", "planted_exit", "artifact"}
            missing = sorted(key for key in required if key not in record)
            if missing or not isinstance(record.get("ok"), bool):
                raise EvidenceError(f"{path}:{index}: malformed self_test event")
            if not isinstance(record["stage"], str) or not record["stage"]:
                raise EvidenceError(f"{path}:{index}: invalid self-test identity")
            event_id = f"self_test:{record['stage']}"
        else:
            raise EvidenceError(f"{path}:{index}: nested run boundary")
        if event_id in seen_ids:
            raise EvidenceError(f"{path}:{index}: duplicate event id {event_id!r}")
        seen_ids.add(event_id)

    exercised = records[1:-1]
    if schema == "fln.check/2":
        profile = records[0]["profile"]
        if profile == "evidence-manifest-self-test":
            expected_ids = ["manifest-stage"]
            actual_ids = [
                str(record.get("stage"))
                for record in exercised
                if record.get("event") == "stage"
            ]
            if len(actual_ids) != len(exercised):
                raise EvidenceError(
                    f"{path}: manifest self-test contains foreign events"
                )
        elif profile == "self-test-driver":
            expected_ids = CHECK_SELF_TEST_ORDER
            actual_ids = [
                str(record.get("stage"))
                for record in exercised
                if record.get("event") == "self_test"
            ]
            if len(actual_ids) != len(exercised):
                raise EvidenceError(f"{path}: check self-test contains foreign events")
        else:
            expected_ids = CHECK_STAGE_ORDER
            actual_ids = [
                str(record.get("stage"))
                for record in exercised
                if record.get("event") == "stage"
            ]
            if len(actual_ids) != len(exercised):
                raise EvidenceError(f"{path}: quality gate contains foreign events")
        if actual_ids != expected_ids[: len(actual_ids)]:
            raise EvidenceError(
                f"{path}: non-canonical check obligation order: {actual_ids!r}"
            )
        if expected_verdict == "pass" and actual_ids != expected_ids:
            raise EvidenceError(f"{path}: passing check omitted mandatory obligations")
        bound_plant = records[0]["planted"]
        planted_events = [
            record
            for record in exercised
            if record.get("event") == "stage"
            and isinstance(record.get("supervisor"), dict)
            and record["supervisor"].get("planted") is True
        ]
        if bound_plant:
            if (
                profile != "self-test-plant"
                or expected_verdict != "fail"
                or actual_ids[-1:] != [bound_plant]
                or len(planted_events) != 1
                or planted_events[0].get("stage") != bound_plant
                or planted_events[0].get("outcome") != "fail"
            ):
                raise EvidenceError(f"{path}: planted failure contract is inconsistent")
        elif planted_events:
            raise EvidenceError(f"{path}: unbound planted failure evidence")
    else:
        if scenario not in E2E_STEP_ORDERS:
            raise EvidenceError(f"{path}: unknown E2E scenario {scenario!r}")
        expected_ids = E2E_STEP_ORDERS[scenario]
        actual_ids = [
            str(record.get("step_id"))
            for record in exercised
            if record.get("event") == "step"
        ]
        if len(actual_ids) != len(exercised):
            raise EvidenceError(f"{path}: E2E run contains foreign events")
        if actual_ids != expected_ids[: len(actual_ids)]:
            raise EvidenceError(
                f"{path}: non-canonical E2E obligation order: {actual_ids!r}"
            )
        if expected_verdict == "pass" and actual_ids != expected_ids:
            raise EvidenceError(
                f"{path}: passing E2E run omitted mandatory obligations"
            )
    if expected_verdict == "pass":
        if not records[1:-1]:
            raise EvidenceError(
                f"{path}: passing run contains no exercised obligations"
            )
        for index, record in enumerate(records[1:-1], 2):
            if record.get("event") == "stage" and record.get("outcome") not in {
                "pass",
                "skipped",
            }:
                raise EvidenceError(
                    f"{path}:{index}: passing run contains failed stage"
                )
            if record.get("event") == "step" and record.get("assertion") != "pass":
                raise EvidenceError(
                    f"{path}:{index}: passing run contains failed assertion"
                )
            if record.get("event") == "self_test" and record.get("ok") is not True:
                raise EvidenceError(
                    f"{path}:{index}: passing run contains failed self-test"
                )
    if expected_planted_stage is not None:
        matching = [
            record
            for record in records[1:-1]
            if record.get("event") == "stage"
            and record.get("stage") == expected_planted_stage
        ]
        if len(matching) != 1:
            raise EvidenceError(f"{path}: expected exactly one planted stage event")
        planted_record = matching[0]
        if (
            planted_record.get("outcome") != "fail"
            or planted_record["supervisor"].get("planted") is not True
        ):
            raise EvidenceError(f"{path}: requested stage is not the planted failure")
        for record in records[1 : records.index(planted_record)]:
            if record.get("event") == "stage" and record.get("outcome") not in {
                "pass",
                "skipped",
            }:
                raise EvidenceError(
                    f"{path}: an earlier stage failed before the requested plant"
                )
        if records[0].get("planted") != expected_planted_stage:
            raise EvidenceError(f"{path}: run start does not bind the requested plant")
    return {
        "schema": "fln.validation/1",
        "subject": path.name,
        "valid": True,
        "records": len(records),
        "run_id": run_id,
        "verdict": expected_verdict,
        "sha256": digest,
        "bundle_committed": False,
    }


def validate_supervisor_object(
    path: Path,
    record_number: int,
    value: Any,
    *,
    expected_stage_id: str,
) -> None:
    if not isinstance(value, dict) or value.get("schema") != "fln.supervisor/1":
        raise EvidenceError(f"{path}:{record_number}: missing supervisor envelope")
    required = {
        "stage_id",
        "argv",
        "cwd",
        "classification",
        "reason_code",
        "wrapper_exit",
        "child_exit",
        "child_signal",
        "monotonic_start_ns",
        "monotonic_end_ns",
        "duration_ns",
        "resource",
        "stdout",
        "stderr",
        "planted",
        "semantic_failure_exits",
        "readiness",
    }
    missing = sorted(key for key in required if key not in value)
    if missing:
        raise EvidenceError(f"{path}:{record_number}: supervisor missing {missing!r}")
    if not isinstance(value["argv"], list) or not all(
        isinstance(item, str) for item in value["argv"]
    ):
        raise EvidenceError(
            f"{path}:{record_number}: supervisor argv is not a string array"
        )
    if value["stage_id"] != expected_stage_id:
        raise EvidenceError(
            f"{path}:{record_number}: supervisor stage identity mismatch"
        )
    if not isinstance(value["planted"], bool):
        raise EvidenceError(
            f"{path}:{record_number}: supervisor planted flag is not boolean"
        )
    semantic_exits = value["semantic_failure_exits"]
    if (
        not isinstance(semantic_exits, list)
        or semantic_exits != sorted(set(semantic_exits))
        or any(
            not isinstance(item, int)
            or isinstance(item, bool)
            or item <= 0
            or item > 255
            for item in semantic_exits
        )
    ):
        raise EvidenceError(f"{path}:{record_number}: malformed semantic failure exits")
    for key in ("monotonic_start_ns", "monotonic_end_ns", "duration_ns"):
        if (
            not isinstance(value[key], int)
            or isinstance(value[key], bool)
            or value[key] < 0
        ):
            raise EvidenceError(f"{path}:{record_number}: malformed supervisor timing")
    if value["monotonic_end_ns"] - value["monotonic_start_ns"] != value["duration_ns"]:
        raise EvidenceError(f"{path}:{record_number}: supervisor duration mismatch")
    expected_wrapper = {
        "pass": 0,
        "fail": 1,
        "internal_fault": 2,
        "inconclusive": 3,
        "cancelled": 4,
    }
    classification = value["classification"]
    if (
        classification not in expected_wrapper
        or value["wrapper_exit"] != expected_wrapper[classification]
    ):
        raise EvidenceError(
            f"{path}:{record_number}: supervisor classification/exit mismatch"
        )
    if classification == "pass" and (
        value["child_exit"] != 0 or value["child_signal"] is not None
    ):
        raise EvidenceError(
            f"{path}:{record_number}: passing supervisor has nonzero child"
        )
    if classification == "fail" and (
        value["child_exit"] not in semantic_exits or value["child_signal"] is not None
    ):
        raise EvidenceError(
            f"{path}:{record_number}: failed supervisor lacks semantic failure"
        )
    if classification == "inconclusive" and value["reason_code"].startswith(
        "child_signal_"
    ):
        if (
            not isinstance(value["child_signal"], str)
            or value["child_exit"] is not None
        ):
            raise EvidenceError(
                f"{path}:{record_number}: child signal is not typed inconclusive"
            )
    if classification == "internal_fault" and value["child_exit"] not in {None, 0}:
        if value["child_exit"] in semantic_exits:
            raise EvidenceError(
                f"{path}:{record_number}: semantic child failure was marked internal"
            )
    resource_facts = value["resource"]
    if not isinstance(resource_facts, dict):
        raise EvidenceError(
            f"{path}:{record_number}: supervisor resource facts missing"
        )
    positive_integer_facts = (
        "capture_bytes_per_stream",
        "output_budget_bytes",
        "timeout_ms",
        "kill_grace_ms",
    )
    for key in positive_integer_facts:
        fact = resource_facts.get(key)
        if not isinstance(fact, int) or isinstance(fact, bool) or fact <= 0:
            raise EvidenceError(
                f"{path}:{record_number}: malformed resource fact {key}"
            )
    if (
        resource_facts["output_budget_bytes"]
        < resource_facts["capture_bytes_per_stream"]
    ):
        raise EvidenceError(f"{path}:{record_number}: impossible output budget")
    for key in ("total_output_bytes", "max_rss_kib_observed"):
        fact = resource_facts.get(key)
        if not isinstance(fact, int) or isinstance(fact, bool) or fact < 0:
            raise EvidenceError(
                f"{path}:{record_number}: malformed resource fact {key}"
            )
    for key in ("user_cpu_seconds", "system_cpu_seconds"):
        fact = resource_facts.get(key)
        if (
            not isinstance(fact, (int, float))
            or isinstance(fact, bool)
            or not float(fact) >= 0.0
            or not float(fact) < float("inf")
        ):
            raise EvidenceError(
                f"{path}:{record_number}: malformed resource fact {key}"
            )
    for key in ("term_sent", "kill_sent"):
        if not isinstance(resource_facts.get(key), bool):
            raise EvidenceError(
                f"{path}:{record_number}: malformed resource fact {key}"
            )
    if resource_facts.get("process_tree_scope") != "linux_subreaper_plus_pidfd":
        raise EvidenceError(f"{path}:{record_number}: unknown process-tree scope")
    if resource_facts.get("surviving_pids") != []:
        raise EvidenceError(f"{path}:{record_number}: supervisor left live descendants")
    readiness_path = require_within(
        path.parent / str(value["readiness"]), path.parent, label="readiness artifact"
    )
    readiness = read_json_object(readiness_path)
    if (
        readiness.get("schema") != "fln.supervisor-readiness/1"
        or readiness.get("stage_id") != expected_stage_id
    ):
        raise EvidenceError(f"{path}:{record_number}: malformed readiness artifact")
    readiness_status = readiness.get("status")
    if readiness_status == "spawn_failed" and classification != "internal_fault":
        raise EvidenceError(f"{path}:{record_number}: spawn failure was not internal")
    if readiness_status not in {"ready", "spawn_failed"}:
        raise EvidenceError(f"{path}:{record_number}: unknown readiness status")
    wrapper_pid = readiness.get("wrapper_pid")
    wrapper_ticks = readiness.get("wrapper_start_ticks")
    if (
        not isinstance(wrapper_pid, int)
        or isinstance(wrapper_pid, bool)
        or wrapper_pid <= 1
        or not isinstance(wrapper_ticks, int)
        or isinstance(wrapper_ticks, bool)
        or wrapper_ticks <= 0
    ):
        raise EvidenceError(
            f"{path}:{record_number}: malformed wrapper readiness identity"
        )
    if readiness_status == "ready":
        child_pid = readiness.get("child_pid")
        child_pgid = readiness.get("child_pgid")
        child_ticks = readiness.get("child_start_ticks")
        if (
            not isinstance(child_pid, int)
            or isinstance(child_pid, bool)
            or child_pid <= 1
            or child_pid != child_pgid
            or not isinstance(child_ticks, int)
            or isinstance(child_ticks, bool)
            or child_ticks <= 0
        ):
            raise EvidenceError(
                f"{path}:{record_number}: malformed child readiness identity"
            )
    elif any(
        readiness.get(key) is not None
        for key in ("child_pid", "child_pgid", "child_start_ticks")
    ):
        raise EvidenceError(
            f"{path}:{record_number}: spawn-failed readiness names a child"
        )
    stream_artifacts: set[str] = set()
    for stream in ("stdout", "stderr"):
        facts = value[stream]
        if not isinstance(facts, dict):
            raise EvidenceError(f"{path}:{record_number}: missing {stream} facts")
        for key in (
            "artifact",
            "sha256",
            "retained_sha256",
            "total_bytes",
            "retained_bytes",
            "head_bytes",
            "tail_bytes",
            "truncated",
        ):
            if key not in facts:
                raise EvidenceError(
                    f"{path}:{record_number}: incomplete {stream} facts"
                )
        if not isinstance(facts["artifact"], str) or not facts["artifact"]:
            raise EvidenceError(
                f"{path}:{record_number}: malformed {stream} artifact name"
            )
        if facts["artifact"] in stream_artifacts:
            raise EvidenceError(f"{path}:{record_number}: streams share an artifact")
        stream_artifacts.add(facts["artifact"])
        if not SHA256_HEX.fullmatch(str(facts["sha256"])) or not SHA256_HEX.fullmatch(
            str(facts["retained_sha256"])
        ):
            raise EvidenceError(f"{path}:{record_number}: malformed {stream} digest")
        for key in ("total_bytes", "retained_bytes", "head_bytes", "tail_bytes"):
            fact = facts[key]
            if not isinstance(fact, int) or isinstance(fact, bool) or fact < 0:
                raise EvidenceError(
                    f"{path}:{record_number}: malformed {stream} size facts"
                )
        if not isinstance(facts["truncated"], bool):
            raise EvidenceError(
                f"{path}:{record_number}: malformed {stream} truncation flag"
            )
        if facts["retained_bytes"] > resource_facts["capture_bytes_per_stream"]:
            raise EvidenceError(
                f"{path}:{record_number}: {stream} capture exceeded bound"
            )
        if facts["total_bytes"] < facts["retained_bytes"]:
            raise EvidenceError(
                f"{path}:{record_number}: {stream} retained more than produced"
            )
        if facts["head_bytes"] + facts["tail_bytes"] > facts["retained_bytes"]:
            raise EvidenceError(
                f"{path}:{record_number}: impossible {stream} head/tail facts"
            )
        if not facts["truncated"] and (
            facts["total_bytes"] != facts["retained_bytes"]
            or facts["head_bytes"] != facts["retained_bytes"]
            or facts["tail_bytes"] != 0
            or facts["sha256"] != facts["retained_sha256"]
        ):
            raise EvidenceError(
                f"{path}:{record_number}: inconsistent untruncated {stream}"
            )
        if facts["truncated"] and facts["total_bytes"] <= facts["retained_bytes"]:
            raise EvidenceError(
                f"{path}:{record_number}: inconsistent truncated {stream}"
            )
        artifact = require_within(
            path.parent / str(facts["artifact"]),
            path.parent,
            label=f"{stream} artifact",
        )
        _data, size, digest = stable_file_facts(artifact)
        if size != facts["retained_bytes"] or digest != facts["retained_sha256"]:
            raise EvidenceError(
                f"{path}:{record_number}: {stream} artifact facts disagree"
            )
    if resource_facts.get("total_output_bytes") != (
        value["stdout"]["total_bytes"] + value["stderr"]["total_bytes"]
    ):
        raise EvidenceError(f"{path}:{record_number}: total output accounting mismatch")
    if (
        classification in {"pass", "fail"}
        and resource_facts["total_output_bytes"] > resource_facts["output_budget_bytes"]
    ):
        raise EvidenceError(
            f"{path}:{record_number}: conclusive stage exceeded output budget"
        )


def sha256_file(path: Path) -> str:
    _data, _size, digest = stable_file_facts(path)
    return digest


def iter_tree_files(root: Path, requested: Sequence[str]) -> Iterable[tuple[str, Path]]:
    seen: set[str] = set()
    for raw in sorted(requested):
        raw_path = Path(raw)
        if raw_path.is_absolute() or ".." in raw_path.parts:
            raise EvidenceError(f"hash input escapes root: {raw}")
        candidate = require_within(root / raw_path, root, label="hash input")
        try:
            candidate.lstat()
        except FileNotFoundError as error:
            raise EvidenceError(f"hash input does not exist: {raw}") from error
        candidate_mode = candidate.lstat().st_mode
        paths = [candidate]
        if stat.S_ISDIR(candidate_mode):
            paths = sorted(
                candidate.rglob("*"), key=lambda item: item.as_posix().encode()
            )
        elif not (stat.S_ISREG(candidate_mode) or stat.S_ISLNK(candidate_mode)):
            raise EvidenceError(f"special file is not a canonical input: {candidate}")
        for path in paths:
            try:
                mode = path.lstat().st_mode
            except FileNotFoundError as error:
                raise EvidenceError(f"hash input disappeared: {path}") from error
            if stat.S_ISDIR(mode):
                continue
            if not (stat.S_ISREG(mode) or stat.S_ISLNK(mode)):
                raise EvidenceError(f"special file is not a canonical input: {path}")
            rel = path.relative_to(root).as_posix()
            if rel in seen:
                continue
            seen.add(rel)
            yield rel, path


def tree_hash_once(root: Path, requested: Sequence[str]) -> str:
    root = lexical_absolute(root)
    _root, root_fd = open_directory_nofollow(root, create=False)
    os.close(root_fd)
    digest = hashlib.sha256(b"fln-canonical-tree/1\0")
    count = 0
    for rel, path in iter_tree_files(root, requested):
        rel_bytes = rel.encode("utf-8")
        full_mode = path.lstat().st_mode
        mode = full_mode & 0o7777
        if stat.S_ISLNK(full_mode):
            _data, file_size, file_digest_hex = stable_symlink_facts(path)
            kind = b"L"
        else:
            _data, file_size, file_digest_hex = stable_file_facts(path)
            kind = b"F"
        file_digest = bytes.fromhex(file_digest_hex)
        digest.update(len(rel_bytes).to_bytes(8, "big"))
        digest.update(rel_bytes)
        digest.update(kind)
        digest.update(file_size.to_bytes(8, "big"))
        digest.update(mode.to_bytes(4, "big"))
        digest.update(file_digest)
        count += 1
    digest.update(count.to_bytes(8, "big"))
    return f"sha256:{digest.hexdigest()}"


def ubs_inventory_binding(inventory: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema": inventory["schema"],
        "scope": inventory["scope"],
        "count": inventory["count"],
        "inventory_root": inventory["inventory_root"],
        "files": inventory["files"],
    }


def tree_hash(
    root: Path,
    requested: Sequence[str],
    *,
    inventory_path: Path | None = None,
    vendor_path: str | None = None,
) -> str:
    previous: str | None = None
    for _attempt in range(6):
        vendor_before = (
            verify_vendor_binding(root, vendor_path) if vendor_path else None
        )
        tree_root = tree_hash_once(root, requested)
        vendor_after = verify_vendor_binding(root, vendor_path) if vendor_path else None
        if vendor_before != vendor_after:
            previous = None
            continue
        components: dict[str, Any] = {
            "schema": "fln-canonical-input/2",
            "tree_root": tree_root,
        }
        if vendor_before is not None:
            components["vendor_binding"] = vendor_before
        if inventory_path is not None:
            inventory = validate_ubs_inventory(inventory_path, root)
            components["ubs_inventory"] = ubs_inventory_binding(inventory)
        if len(components) == 2:
            current = tree_root
        else:
            digest = hashlib.sha256(b"fln-canonical-input/2\0")
            digest.update(canonical_json(components))
            current = f"sha256:{digest.hexdigest()}"
        if current == previous:
            return current
        previous = current
    raise EvidenceError("canonical tree did not stabilize across consecutive snapshots")


def split_git_nul(data: bytes, *, subject: str) -> list[str]:
    if not data:
        return []
    if not data.endswith(b"\0"):
        raise EvidenceError(f"{subject} did not produce NUL-terminated paths")
    result: list[str] = []
    for raw in data[:-1].split(b"\0"):
        if not raw:
            raise EvidenceError(f"{subject} produced an empty path")
        try:
            result.append(raw.decode("utf-8"))
        except UnicodeDecodeError as error:
            raise EvidenceError(f"{subject} produced a non-UTF-8 path") from error
    return result


def git_paths(root: Path, args: Sequence[str], *, subject: str) -> list[str]:
    return split_git_nul(run_git(root, args, subject=subject), subject=subject)


def run_git(
    root: Path,
    args: Sequence[str],
    *,
    subject: str,
    accepted_exits: set[int] | None = None,
) -> bytes:
    root = lexical_absolute(root)
    git_dir = root / ".git"
    try:
        git_mode = git_dir.lstat().st_mode
    except FileNotFoundError as error:
        raise EvidenceError(f"{subject} requires an explicit repository .git directory") from error
    if stat.S_ISLNK(git_mode) or not stat.S_ISDIR(git_mode):
        raise EvidenceError(f"{subject} requires a real repository .git directory")
    git_environment = {
        key: value for key, value in os.environ.items() if not key.startswith("GIT_")
    }
    git_environment.update(
        {
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_OPTIONAL_LOCKS": "0",
            "GIT_TERMINAL_PROMPT": "0",
        }
    )
    command = [
        "git",
        f"--git-dir={git_dir}",
        f"--work-tree={root}",
        "-c",
        "core.fsmonitor=false",
        "-c",
        "core.ignoreStat=false",
        "-c",
        "core.filemode=true",
        *args,
    ]
    completed = subprocess.run(
        command,
        cwd=root,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
        env=git_environment,
    )
    permitted = accepted_exits or {0}
    if completed.returncode not in permitted:
        detail = completed.stderr.decode("utf-8", errors="replace")[-1000:]
        raise EvidenceError(
            f"{subject} failed with exit {completed.returncode}: {detail}"
        )
    if len(completed.stdout) > MAX_LOG_BYTES or len(completed.stderr) > MAX_LOG_BYTES:
        raise EvidenceError(f"{subject} exceeded the Git output budget")
    return completed.stdout


def git_text(root: Path, args: Sequence[str], *, subject: str) -> str:
    data = run_git(root, args, subject=subject)
    try:
        value = data.decode("ascii").strip()
    except UnicodeDecodeError as error:
        raise EvidenceError(f"{subject} produced non-ASCII identity data") from error
    if not value or "\n" in value:
        raise EvidenceError(f"{subject} produced malformed identity data")
    return value


def parse_reference_lock(root: Path) -> dict[str, str]:
    data, _size, _digest = stable_file_facts(
        root / "SUITE.lock", max_bytes=MAX_RECORD_BYTES
    )
    try:
        lines = data.decode("utf-8").splitlines()
    except UnicodeDecodeError as error:
        raise EvidenceError("SUITE.lock is not UTF-8") from error
    rows = [line.split() for line in lines if line.startswith("reference ")]
    if len(rows) != 1 or len(rows[0]) != 5:
        raise EvidenceError("SUITE.lock must contain exactly one strict Reference row")
    directive, repository, tag_field, commit_field, tree_field, *extra = rows[0]
    if directive != "reference" or extra:
        raise EvidenceError("SUITE.lock Reference row is malformed")
    fields = {
        "repository": repository,
        "tag": tag_field.removeprefix("tag="),
        "commit": commit_field.removeprefix("commit="),
        "tree": tree_field.removeprefix("tree="),
    }
    if (
        fields["repository"] != "leanprover/lean4"
        or tag_field == fields["tag"]
        or commit_field == fields["commit"]
        or tree_field == fields["tree"]
        or not re.fullmatch(r"[0-9a-f]{40}", fields["commit"])
        or not re.fullmatch(r"[0-9a-f]{40}", fields["tree"])
    ):
        raise EvidenceError("SUITE.lock Reference identity is malformed")
    return fields


def verify_vendor_binding(root: Path, vendor_path: str) -> dict[str, Any]:
    root = lexical_absolute(root)
    if vendor_path != "vendor/lean4-src":
        raise EvidenceError(
            "only the constitutional vendor/lean4-src binding is supported"
        )
    vendor = require_within(root / vendor_path, root, label="Reference vendor tree")
    mode = vendor.lstat().st_mode
    if stat.S_ISLNK(mode) or not stat.S_ISDIR(mode):
        raise EvidenceError("Reference vendor tree must be a real directory")
    for required in (vendor / "LICENSE", vendor / "LICENSES", root / "vendor/NOTICE"):
        _data, _size, _digest = stable_file_facts(required, max_bytes=MAX_LOG_BYTES)
    if os.path.lexists(vendor / ".git"):
        raise EvidenceError(
            "nested Git metadata is forbidden in the Reference vendor tree"
        )
    reference = parse_reference_lock(root)

    def repository_state() -> tuple[str, str]:
        toplevel = git_text(
            root, ["rev-parse", "--show-toplevel"], subject="repository top level"
        )
        if lexical_absolute(Path(toplevel)) != root:
            raise EvidenceError(
                f"repository top level mismatch: expected={root} actual={toplevel}"
            )
        head = git_text(root, ["rev-parse", "HEAD"], subject="repository HEAD")
        tree = git_text(
            root,
            ["rev-parse", f"{head}:{vendor_path}"],
            subject="Reference HEAD subtree",
        )
        if tree != reference["tree"]:
            raise EvidenceError(
                f"Reference HEAD tree mismatch: expected={reference['tree']} actual={tree}"
            )
        run_git(
            root,
            [
                "diff",
                "--cached",
                "--quiet",
                "--no-ext-diff",
                "--ignore-submodules=none",
                head,
                "--",
                vendor_path,
            ],
            subject="Reference staged-index diff",
        )
        return head, tree

    def scan_index_and_worktree() -> None:
        unmerged = run_git(
            root,
            ["ls-files", "-u", "-z", "--", vendor_path],
            subject="Reference unmerged-index scan",
        )
        if unmerged:
            raise EvidenceError("Reference vendor tree contains unmerged index entries")
        flags = split_git_nul(
            run_git(
                root,
                ["ls-files", "-v", "-z", "--", vendor_path],
                subject="Reference index-flag scan",
            ),
            subject="Reference index-flag scan",
        )
        for value in flags:
            if len(value) < 3 or value[1] != " ":
                raise EvidenceError(
                    "Reference index-flag scan produced a malformed row"
                )
            if value[0] == "S" or value[0].islower():
                raise EvidenceError(
                    "Reference index entry carries a hidden-worktree flag: "
                    f"{value[2:]}"
                )
        run_git(
            root,
            [
                "diff",
                "--quiet",
                "--no-ext-diff",
                "--ignore-submodules=none",
                "--",
                vendor_path,
            ],
            subject="Reference worktree diff",
        )
        if run_git(
            root,
            ["ls-files", "--others", "-z", "--", vendor_path],
            subject="Reference untracked scan",
        ):
            raise EvidenceError("Reference vendor tree contains untracked files")
        if run_git(
            root,
            [
                "ls-files",
                "--others",
                "--ignored",
                "--exclude-standard",
                "-z",
                "--",
                vendor_path,
            ],
            subject="Reference ignored-file scan",
        ):
            raise EvidenceError(
                "Reference vendor tree contains ignored untracked files"
            )

    first_head, first_tree = repository_state()
    scan_index_and_worktree()
    second_head, second_tree = repository_state()
    scan_index_and_worktree()
    third_head, third_tree = repository_state()
    if not (
        (first_head, first_tree)
        == (second_head, second_tree)
        == (third_head, third_tree)
    ):
        raise EvidenceError("Reference repository state changed during verification")
    object_format = git_text(
        root, ["rev-parse", "--show-object-format"], subject="Git object format"
    )
    if object_format != "sha1":
        raise EvidenceError(
            f"unexpected Git object format for pinned Reference tree: {object_format}"
        )
    return {
        "schema": "fln.git-tree-binding/1",
        "path": vendor_path,
        "repository": reference["repository"],
        "tag": reference["tag"],
        "commit": reference["commit"],
        "object_format": object_format,
        "tree": first_tree,
    }


def validate_vendor_binding_document(binding: Any) -> dict[str, Any]:
    if not isinstance(binding, dict) or set(binding) != {
        "schema",
        "path",
        "repository",
        "tag",
        "commit",
        "object_format",
        "tree",
    }:
        raise EvidenceError("Reference vendor binding has unknown or missing fields")
    if (
        binding.get("schema") != "fln.git-tree-binding/1"
        or binding.get("path") != "vendor/lean4-src"
        or binding.get("repository") != "leanprover/lean4"
        or binding.get("object_format") != "sha1"
        or not isinstance(binding.get("tag"), str)
        or not binding["tag"]
        or not re.fullmatch(r"[0-9a-f]{40}", str(binding.get("commit")))
        or not re.fullmatch(r"[0-9a-f]{40}", str(binding.get("tree")))
    ):
        raise EvidenceError("Reference vendor binding is malformed")
    return binding


def inventory_root(rows: Sequence[dict[str, Any]]) -> str:
    digest = hashlib.sha256(b"fln-ubs-inventory/1\0")
    digest.update(canonical_json(list(rows)))
    return f"sha256:{digest.hexdigest()}"


def collect_ubs_inventory(root: Path, scope: str) -> dict[str, Any]:
    root = lexical_absolute(root)
    _root, descriptor = open_directory_nofollow(root, create=False)
    os.close(descriptor)
    if scope == "all-tracked":
        candidates = git_paths(
            root,
            ["ls-files", "-z", "--", "*.rs", "*.toml", "*.py"],
            subject="tracked UBS inventory",
        )
    elif scope == "changed":
        candidates = [
            *git_paths(
                root,
                ["diff", "--name-only", "-z", "HEAD", "--"],
                subject="changed UBS inventory",
            ),
            *git_paths(
                root,
                ["ls-files", "--others", "--exclude-standard", "-z", "--"],
                subject="untracked UBS inventory",
            ),
        ]
    else:
        raise EvidenceError(f"unsupported UBS scope: {scope!r}")
    selected: set[str] = set()
    for rel in candidates:
        rel_path = Path(rel)
        if (
            rel_path.is_absolute()
            or ".." in rel_path.parts
            or rel.startswith("vendor/")
        ):
            if rel.startswith("vendor/"):
                continue
            raise EvidenceError(f"non-canonical UBS path: {rel!r}")
        if not rel.endswith((".rs", ".toml", ".py")):
            continue
        candidate = require_within(root / rel_path, root, label="UBS input")
        try:
            mode = candidate.lstat().st_mode
        except FileNotFoundError:
            continue
        if stat.S_ISLNK(mode) or not stat.S_ISREG(mode):
            raise EvidenceError(
                f"UBS input is not a regular no-follow file: {candidate}"
            )
        selected.add(rel_path.as_posix())
    rows: list[dict[str, Any]] = []
    for rel in sorted(selected, key=lambda value: value.encode("utf-8")):
        _data, size, digest = stable_file_facts(root / rel)
        rows.append({"path": rel, "bytes": size, "sha256": digest})
    return {
        "schema": "fln.ubs-inventory/1",
        "scope": scope,
        "count": len(rows),
        "inventory_root": inventory_root(rows),
        "files": rows,
    }


def validate_ubs_inventory_document(inventory: Any) -> dict[str, Any]:
    if not isinstance(inventory, dict) or set(inventory) != {
        "schema",
        "scope",
        "count",
        "inventory_root",
        "files",
    }:
        raise EvidenceError("UBS inventory has unknown or missing fields")
    if inventory.get("schema") != "fln.ubs-inventory/1" or inventory.get(
        "scope"
    ) not in {
        "changed",
        "all-tracked",
    }:
        raise EvidenceError("UBS inventory identity is malformed")
    rows = inventory.get("files")
    if not isinstance(rows, list) or inventory.get("count") != len(rows):
        raise EvidenceError("UBS inventory count is malformed")
    expected_paths: list[str] = []
    for row in rows:
        if not isinstance(row, dict) or set(row) != {"path", "bytes", "sha256"}:
            raise EvidenceError("UBS inventory row is malformed")
        rel = row.get("path")
        if (
            not isinstance(rel, str)
            or not rel
            or Path(rel).is_absolute()
            or ".." in Path(rel).parts
            or rel.startswith("vendor/")
            or not rel.endswith((".rs", ".toml", ".py"))
        ):
            raise EvidenceError(f"UBS inventory path is non-canonical: {rel!r}")
        if (
            not isinstance(row.get("bytes"), int)
            or isinstance(row.get("bytes"), bool)
            or row["bytes"] < 0
            or not SHA256_HEX.fullmatch(str(row.get("sha256")))
        ):
            raise EvidenceError(f"UBS inventory facts are malformed: {rel}")
        expected_paths.append(rel)
    if expected_paths != sorted(
        set(expected_paths), key=lambda value: value.encode("utf-8")
    ):
        raise EvidenceError("UBS inventory paths are duplicate or unsorted")
    if inventory.get("inventory_root") != inventory_root(rows):
        raise EvidenceError("UBS inventory root is inconsistent")
    return inventory


def validate_ubs_inventory(path: Path, root: Path | None) -> dict[str, Any]:
    inventory = validate_ubs_inventory_document(read_json_object(path))
    if root is None:
        return inventory
    root = lexical_absolute(root)
    _root, descriptor = open_directory_nofollow(root, create=False)
    os.close(descriptor)
    recomputed = collect_ubs_inventory(root, inventory["scope"])
    if recomputed != inventory:
        raise EvidenceError(
            "UBS inventory does not exactly cover its declared live repository scope"
        )
    for row in inventory["files"]:
        rel = row["path"]
        candidate = require_within(root / rel, root, label="UBS inventory input")
        mode = candidate.lstat().st_mode
        if stat.S_ISLNK(mode) or not stat.S_ISREG(mode):
            raise EvidenceError(f"UBS inventory input is not regular: {candidate}")
        _data, size, digest = stable_file_facts(candidate)
        if row["bytes"] != size or row["sha256"] != digest:
            raise EvidenceError(f"UBS inventory input changed: {rel}")
    if collect_ubs_inventory(root, inventory["scope"]) != inventory:
        raise EvidenceError("UBS inventory scope changed during validation")
    return inventory


def emergency_kill(
    readiness_path: Path, expected_wrapper_pid: int, expected_stage_id: str
) -> None:
    readiness = read_json_object(readiness_path)
    if readiness.get("schema") != "fln.supervisor-readiness/1":
        raise EvidenceError("emergency kill readiness schema mismatch")
    if (
        readiness.get("status") != "ready"
        or readiness.get("stage_id") != expected_stage_id
    ):
        raise EvidenceError("emergency kill readiness identity mismatch")
    wrapper_pid = readiness.get("wrapper_pid")
    child_pid = readiness.get("child_pid")
    child_pgid = readiness.get("child_pgid")
    if wrapper_pid != expected_wrapper_pid or child_pid != child_pgid:
        raise EvidenceError("emergency kill PID binding mismatch")
    if not all(
        isinstance(value, int) and not isinstance(value, bool) and value > 1
        for value in (wrapper_pid, child_pid)
    ):
        raise EvidenceError("emergency kill PIDs are malformed")
    wrapper_facts = proc_stat_facts(wrapper_pid)
    child_facts = proc_stat_facts(child_pid)
    if (
        wrapper_facts is None
        or child_facts is None
        or wrapper_facts[0] == "Z"
        or child_facts[0] == "Z"
        or wrapper_facts[2] != readiness.get("wrapper_start_ticks")
        or child_facts[2] != readiness.get("child_start_ticks")
        or child_facts[1] != child_pgid
        or os.getpgid(child_pid) != child_pgid
    ):
        raise EvidenceError("emergency kill readiness is stale")
    handles: ProcessHandles = {}
    try:
        if not remember_process(wrapper_pid, handles) or not remember_process(
            child_pid, handles
        ):
            raise EvidenceError("emergency kill could not bind process lifetimes")
        if (
            handles[wrapper_pid][0] != wrapper_facts[2]
            or handles[child_pid][0] != child_facts[2]
        ):
            raise EvidenceError("emergency kill process identity changed")

        # Freeze the wrapper-owned subreaper tree before killing it. This catches
        # descendants that created their own sessions and prevents any bound parent
        # from forking across the final scan. Pidfds make every signal lifetime-safe.
        live = live_tree_members(wrapper_pid, handles)
        if wrapper_pid not in live or child_pid not in live:
            raise EvidenceError("emergency kill readiness tree is incomplete")
        freeze_deadline = time.monotonic() + 1.0
        while time.monotonic() < freeze_deadline:
            for pid in live:
                signal_process_handle(pid, handles[pid], signal.SIGSTOP)
            time.sleep(0.01)
            repeated = live_tree_members(wrapper_pid, handles)
            all_stopped = all(
                (facts := proc_stat_facts(pid)) is not None
                and facts[0] in {"T", "t"}
                and facts[2] == handles[pid][0]
                for pid in repeated
            )
            if repeated == live and all_stopped:
                live = repeated
                break
            live = repeated
        else:
            raise EvidenceError("emergency kill could not freeze the complete tree")

        for pid in sorted(live, key=lambda value: value == wrapper_pid):
            signal_process_handle(pid, handles[pid], signal.SIGKILL)
        deadline = time.monotonic() + 1.0
        while time.monotonic() < deadline:
            live = live_tree_members(wrapper_pid, handles)
            if not live:
                return
            for pid in live:
                signal_process_handle(pid, handles[pid], signal.SIGKILL)
            time.sleep(0.01)
        raise EvidenceError(f"emergency kill left live processes: {sorted(live)}")
    finally:
        close_process_handles(handles)


def artifact_role(rel: str) -> str:
    if rel == "run.ndjson":
        return "run_log"
    if rel.startswith("fixtures/"):
        return "repro_fixture"
    if rel.endswith(".ndjson"):
        return "child_log"
    if rel.endswith(".out"):
        return "stdout"
    if rel.endswith(".err"):
        return "stderr"
    if rel.endswith(".meta.json"):
        return "supervisor_metadata"
    if rel.endswith(".ready.json"):
        return "supervisor_readiness"
    if rel.endswith(".validation.json"):
        return "validation_report"
    if rel == "vendor-binding.json":
        return "reference_tree_binding"
    if rel == "ubs-inventory.json":
        return "ubs_inventory"
    return "artifact"


def artifact_inventory_once(
    art_dir: Path, *, excluded: set[Path]
) -> list[dict[str, Any]]:
    entries: list[dict[str, Any]] = []
    for path in sorted(art_dir.rglob("*"), key=lambda item: item.as_posix().encode()):
        absolute = lexical_absolute(path)
        if absolute in excluded:
            continue
        try:
            mode = path.lstat().st_mode
        except FileNotFoundError as error:
            raise EvidenceError(
                f"artifact disappeared during inventory: {path}"
            ) from error
        if stat.S_ISLNK(mode):
            raise EvidenceError(f"artifact symlink is forbidden: {path}")
        rel = path.relative_to(art_dir).as_posix()
        if rel.startswith("/") or ".." in Path(rel).parts or ".partial." in rel:
            raise EvidenceError(f"non-canonical or incomplete artifact path: {rel}")
        if stat.S_ISDIR(mode):
            entries.append(
                {
                    "path": rel,
                    "role": "directory",
                    "bytes": 0,
                    "sha256": hashlib.sha256(b"fln-artifact-directory/1").hexdigest(),
                    "complete": True,
                }
            )
        elif stat.S_ISREG(mode):
            _data, size, digest = stable_file_facts(path)
            entries.append(
                {
                    "path": rel,
                    "role": artifact_role(rel),
                    "bytes": size,
                    "sha256": digest,
                    "complete": True,
                }
            )
        else:
            raise EvidenceError(f"special artifact file is forbidden: {path}")
    return entries


def artifact_inventory(art_dir: Path, *, excluded: set[Path]) -> list[dict[str, Any]]:
    previous: list[dict[str, Any]] | None = None
    for _attempt in range(6):
        current = artifact_inventory_once(art_dir, excluded=excluded)
        if current == previous:
            return current
        previous = current
    raise EvidenceError(
        "artifact inventory did not stabilize across consecutive snapshots"
    )


def generate_manifest(
    art_dir: Path,
    output: Path,
    digest_output: Path,
    run_id: str,
    bead: str,
    scenario: str,
    verdict: str,
    input_root: str,
    final_root: str,
) -> dict[str, Any]:
    art_dir = lexical_absolute(art_dir)
    _root, root_fd = open_directory_nofollow(art_dir, create=False)
    os.close(root_fd)
    output = require_within(output, art_dir, label="manifest output")
    digest_output = require_within(digest_output, art_dir, label="manifest digest")
    run_log = art_dir / "run.ndjson"
    run_records = load_ndjson(run_log)
    run_schema = run_records[0].get("schema")
    if run_schema not in RUN_SCHEMAS:
        raise EvidenceError("run log has an unsupported schema")
    run_report = validate_run(run_log, run_schema, verdict)
    start = run_records[0]
    terminal = run_records[-1]
    expected_identity = {
        "run_id": run_id,
        "bead": bead,
        "scenario": scenario,
        "verdict": verdict,
        "input_root": input_root,
        "final_root": final_root,
    }
    observed_identity = {
        "run_id": start.get("run_id"),
        "bead": start.get("bead"),
        "scenario": start.get("scenario"),
        "verdict": terminal.get("verdict"),
        "input_root": start.get("input_root"),
        "final_root": terminal.get("final_state"),
    }
    if observed_identity != expected_identity:
        raise EvidenceError(
            f"manifest identity arguments disagree with run: expected={observed_identity!r} actual={expected_identity!r}"
        )
    validation_path = art_dir / "run.validation.json"
    if read_json_object(validation_path) != run_report:
        raise EvidenceError("run validation report does not match the manifested run")
    entries = artifact_inventory(art_dir, excluded={output, digest_output})
    present = {entry["path"] for entry in entries}
    required = {"run.ndjson", "run.validation.json"}
    if not required.issubset(present):
        raise EvidenceError(
            f"manifest is missing required artifacts: {sorted(required - present)!r}"
        )
    manifest = {
        "schema": "fln.evidence-manifest/1",
        "run_schema": run_schema,
        "run_id": run_id,
        "bead": bead,
        "scenario": scenario,
        "verdict": verdict,
        "created_utc": utc_now(),
        "input_root": input_root,
        "final_root": final_root,
        "final_state_matches_input": input_root == final_root,
        "artifacts": entries,
    }
    data = canonical_json(manifest)
    write_new(output, data)
    digest = hashlib.sha256(data).hexdigest()
    write_new(digest_output, f"sha256:{digest}  {output.name}\n".encode())
    validate_manifest(art_dir, output, digest_output)
    return manifest


def validate_manifest(
    art_dir: Path,
    manifest_path: Path,
    digest_path: Path,
    *,
    live_context: bool = True,
) -> None:
    art_dir = lexical_absolute(art_dir)
    _root, root_fd = open_directory_nofollow(art_dir, create=False)
    os.close(root_fd)
    manifest_path = require_within(manifest_path, art_dir, label="manifest")
    digest_path = require_within(digest_path, art_dir, label="manifest digest")
    manifest = read_json_object(manifest_path)
    if manifest.get("schema") != "fln.evidence-manifest/1":
        raise EvidenceError("wrong evidence manifest schema")
    if manifest.get("run_schema") not in RUN_SCHEMAS:
        raise EvidenceError("manifest run schema is unsupported")
    if manifest.get("verdict") not in {
        "pass",
        "fail",
        "internal_fault",
        "inconclusive",
        "cancelled",
    }:
        raise EvidenceError("manifest verdict is unsupported")
    for key in ("input_root", "final_root"):
        if not re.fullmatch(r"sha256:[0-9a-f]{64}", str(manifest.get(key))):
            raise EvidenceError(f"manifest {key} is not a canonical tree root")
    entries = manifest.get("artifacts")
    if not isinstance(entries, list):
        raise EvidenceError("manifest artifacts must be a list")
    observed_paths: list[str] = []
    seen_paths: set[str] = set()
    for entry in entries:
        expected_row_keys = {"path", "role", "bytes", "sha256", "complete"}
        if (
            not isinstance(entry, dict)
            or set(entry) != expected_row_keys
            or not isinstance(entry.get("path"), str)
        ):
            raise EvidenceError("malformed manifest artifact row")
        rel = entry["path"]
        if rel in seen_paths:
            raise EvidenceError(f"duplicate manifest artifact row: {rel}")
        seen_paths.add(rel)
        if rel.startswith("/") or ".." in Path(rel).parts or ".partial." in rel:
            raise EvidenceError(f"non-canonical manifest path: {rel}")
        path = require_within(art_dir / rel, art_dir, label="manifest artifact")
        if entry.get("role") == "directory":
            _directory, descriptor = open_directory_nofollow(path, create=False)
            os.close(descriptor)
            expected_directory_digest = hashlib.sha256(
                b"fln-artifact-directory/1"
            ).hexdigest()
            if (
                entry.get("bytes") != 0
                or entry.get("sha256") != expected_directory_digest
            ):
                raise EvidenceError(f"manifest directory facts mismatch: {rel}")
        else:
            _data, size, digest = stable_file_facts(path)
            if entry.get("bytes") != size:
                raise EvidenceError(f"manifest byte count mismatch: {rel}")
            if entry.get("sha256") != digest:
                raise EvidenceError(f"manifest digest mismatch: {rel}")
        if entry.get("complete") is not True:
            raise EvidenceError(f"manifest artifact is not complete: {rel}")
        observed_paths.append(rel)
    if observed_paths != sorted(observed_paths, key=lambda value: value.encode()):
        raise EvidenceError("manifest artifact rows are not canonically sorted")
    if manifest.get("final_state_matches_input") != (
        manifest.get("input_root") == manifest.get("final_root")
    ):
        raise EvidenceError("manifest final-state assertion is inconsistent")
    if (
        manifest.get("verdict") == "pass"
        and manifest.get("final_state_matches_input") is not True
    ):
        raise EvidenceError(
            "passing manifest does not preserve its canonical input root"
        )
    actual_entries = artifact_inventory(
        art_dir,
        excluded={manifest_path, digest_path, art_dir / "bundle.complete.json"},
    )
    if entries != actual_entries:
        raise EvidenceError(
            f"manifest inventory mismatch: recorded={entries!r} actual={actual_entries!r}"
        )
    required = {"run.ndjson", "run.validation.json"}
    if not required.issubset(seen_paths):
        raise EvidenceError(
            f"manifest is missing required artifacts: {sorted(required - seen_paths)!r}"
        )
    run_log = art_dir / "run.ndjson"
    run_report = validate_run(
        run_log,
        manifest["run_schema"],
        str(manifest.get("verdict")),
        live_context=live_context,
    )
    if read_json_object(art_dir / "run.validation.json") != run_report:
        raise EvidenceError("manifested run validation report is stale or forged")
    terminal = load_ndjson(run_log)[-1]
    start = load_ndjson(run_log)[0]
    for key, manifest_key in (
        ("run_id", "run_id"),
        ("bead", "bead"),
        ("verdict", "verdict"),
        ("final_state", "final_root"),
    ):
        if terminal.get(key) != manifest.get(manifest_key):
            raise EvidenceError(f"manifest/run terminal mismatch for {key}")
    for key in ("run_id", "bead", "scenario", "input_root"):
        if start.get(key) != manifest.get(key):
            raise EvidenceError(f"manifest/run start mismatch for {key}")
    if terminal.get("evidence_manifest") != manifest_path.name:
        raise EvidenceError("run terminal names a different evidence manifest")
    expected_digest = f"sha256:{sha256_file(manifest_path)}  {manifest_path.name}\n"
    digest_data, _size, _digest = stable_file_facts(digest_path)
    try:
        digest_text = digest_data.decode("utf-8")
    except UnicodeDecodeError as error:
        raise EvidenceError("manifest digest sidecar is not UTF-8") from error
    if not hmac.compare_digest(digest_text, expected_digest):
        raise EvidenceError("manifest digest sidecar mismatch")


def complete_bundle(
    art_dir: Path,
    manifest_path: Path,
    digest_path: Path,
    output: Path,
    *,
    governed_root: Path,
    governed_paths: Sequence[str],
    expected_root: str,
    inventory_path: Path | None = None,
    vendor_path: str | None = None,
) -> dict[str, Any]:
    art_dir = lexical_absolute(art_dir)
    output = require_within(output, art_dir, label="bundle commit")
    if output.name != "bundle.complete.json":
        raise EvidenceError("bundle commit marker must be named bundle.complete.json")
    validate_manifest(art_dir, manifest_path, digest_path)
    manifest = read_json_object(manifest_path)
    run_log = art_dir / "run.ndjson"
    terminal = load_ndjson(run_log)[-1]
    if terminal.get("bundle_commit") != output.name:
        raise EvidenceError("run terminal names a different bundle commit marker")
    initial_bindings = (
        sha256_file(run_log),
        sha256_file(manifest_path),
        sha256_file(digest_path),
    )
    marker: dict[str, Any] = {
        "schema": "fln.evidence-bundle-commit/1",
        "status": "committed",
        "run_id": manifest["run_id"],
        "bead": manifest["bead"],
        "scenario": manifest["scenario"],
        "verdict": manifest["verdict"],
        "process_exit": terminal["process_exit"],
        "created_utc": utc_now(),
        "run_log": {"path": "run.ndjson", "sha256": initial_bindings[0]},
        "manifest": {"path": manifest_path.name, "sha256": initial_bindings[1]},
        "manifest_digest": {
            "path": digest_path.name,
            "sha256": initial_bindings[2],
        },
    }
    validate_marker_bindings(marker, manifest, terminal, initial_bindings)
    marker_data = canonical_json(marker)
    # Repeat the whole bundle validation before committing. Any cross-read or
    # inventory race must stabilize before the marker can exist.
    validate_manifest(art_dir, manifest_path, digest_path)
    repeated_bindings = (
        sha256_file(run_log),
        sha256_file(manifest_path),
        sha256_file(digest_path),
    )
    if repeated_bindings != initial_bindings:
        raise EvidenceError("bundle bindings changed during prospective validation")
    validate_marker_bindings(
        marker,
        read_json_object(manifest_path),
        load_ndjson(run_log)[-1],
        repeated_bindings,
    )
    current_root = tree_hash(
        governed_root,
        governed_paths,
        inventory_path=inventory_path,
        vendor_path=vendor_path,
    )
    if current_root != expected_root or current_root != manifest.get("final_root"):
        raise EvidenceError("governed inputs changed before bundle commit")
    # This durable, exclusive publication is deliberately the final operation.
    write_new(output, marker_data)
    return marker


def validate_marker_bindings(
    marker: dict[str, Any],
    manifest: dict[str, Any],
    terminal: dict[str, Any],
    bindings: tuple[str, str, str],
) -> None:
    if set(marker) != {
        "schema",
        "status",
        "run_id",
        "bead",
        "scenario",
        "verdict",
        "process_exit",
        "created_utc",
        "run_log",
        "manifest",
        "manifest_digest",
    }:
        raise EvidenceError("bundle marker has unknown or missing fields")
    if (
        marker.get("schema") != "fln.evidence-bundle-commit/1"
        or marker.get("status") != "committed"
    ):
        raise EvidenceError("invalid evidence bundle commit marker")
    for key in ("run_id", "bead", "scenario", "verdict"):
        if marker.get(key) != manifest.get(key):
            raise EvidenceError(f"bundle marker identity mismatch for {key}")
    if marker.get("process_exit") != terminal.get("process_exit"):
        raise EvidenceError("bundle marker process exit disagrees with terminal")
    expected_files = {
        "run_log": ("run.ndjson", bindings[0]),
        "manifest": ("manifest.json", bindings[1]),
        "manifest_digest": ("manifest.digest", bindings[2]),
    }
    for key, (expected_name, expected_digest) in expected_files.items():
        value = marker.get(key)
        if (
            not isinstance(value, dict)
            or set(value) != {"path", "sha256"}
            or value.get("path") != expected_name
            or value.get("sha256") != expected_digest
        ):
            raise EvidenceError(f"bundle marker has invalid {key} binding")


def validate_bundle(
    art_dir: Path,
    manifest_path: Path,
    digest_path: Path,
    commit_path: Path,
) -> dict[str, Any]:
    art_dir = lexical_absolute(art_dir)
    manifest_path = require_within(manifest_path, art_dir, label="manifest")
    digest_path = require_within(digest_path, art_dir, label="manifest digest")
    commit_path = require_within(commit_path, art_dir, label="bundle commit")
    if (
        manifest_path.name != "manifest.json"
        or digest_path.name != "manifest.digest"
        or commit_path.name != "bundle.complete.json"
    ):
        raise EvidenceError("bundle uses non-canonical artifact names")
    validate_manifest(art_dir, manifest_path, digest_path, live_context=False)
    manifest = read_json_object(manifest_path)
    marker = read_json_object(commit_path)
    run_log = art_dir / "run.ndjson"
    terminal = load_ndjson(run_log)[-1]
    validate_marker_bindings(
        marker,
        manifest,
        terminal,
        (sha256_file(run_log), sha256_file(manifest_path), sha256_file(digest_path)),
    )
    return {
        "schema": "fln.bundle-validation/1",
        "valid": True,
        "committed": True,
        "run_id": marker["run_id"],
        "verdict": marker["verdict"],
        "process_exit": marker["process_exit"],
        "commit_sha256": sha256_file(commit_path),
    }


def add_fields(record: dict[str, Any], args: argparse.Namespace) -> None:
    occupied = set(record)
    for values, kind in (
        (args.string or [], "string"),
        (args.integer or [], "integer"),
        (args.boolean or [], "boolean"),
        (args.json_value or [], "json"),
    ):
        for key, raw in values:
            if key in occupied:
                raise EvidenceError(f"duplicate field: {key}")
            occupied.add(key)
            if kind == "string":
                record[key] = raw
            elif kind == "integer":
                record[key] = int(raw)
            elif kind == "boolean":
                if raw not in {"true", "false"}:
                    raise EvidenceError(f"boolean field {key} must be true or false")
                record[key] = raw == "true"
            else:
                record[key] = parse_json(raw, subject=f"field {key}")
    for key in args.null or []:
        if key in occupied:
            raise EvidenceError(f"duplicate field: {key}")
        occupied.add(key)
        record[key] = None
    for key, value in args.append_string or []:
        prior = record.setdefault(key, [])
        if not isinstance(prior, list):
            raise EvidenceError(f"field {key} is not a list")
        prior.append(value)
    for key, path_raw in args.json_file or []:
        if key in occupied:
            raise EvidenceError(f"duplicate field: {key}")
        occupied.add(key)
        data, _size, _digest = stable_file_facts(
            Path(path_raw), max_bytes=MAX_RECORD_BYTES
        )
        record[key] = parse_json(data, subject=path_raw)


def cmd_emit(args: argparse.Namespace) -> int:
    require_within(Path(args.file), Path(args.artifact_root), label="NDJSON log")
    record: dict[str, Any] = {}
    add_fields(record, args)
    append_record(Path(args.file), record, must_be_new=args.new_log)
    return PASS


def cmd_run(args: argparse.Namespace) -> int:
    argv = list(args.command)
    if argv and argv[0] == "--":
        argv = argv[1:]
    return run_supervised(
        argv=argv,
        cwd=Path(args.cwd).resolve(strict=True),
        metadata_path=Path(args.metadata),
        stdout_path=Path(args.stdout),
        stderr_path=Path(args.stderr),
        readiness_path=Path(args.readiness),
        artifact_root=Path(args.artifact_root),
        capture_bytes=args.capture_bytes,
        output_budget_bytes=args.output_budget_bytes,
        timeout_ms=args.timeout_ms,
        grace_ms=args.grace_ms,
        stage_id=args.stage_id,
        planted=args.planted,
        semantic_failure_exits=args.semantic_failure_exit or [],
        cancel_after_ms=args.cancel_after_ms,
    )


def cmd_validate_guard(args: argparse.Namespace) -> int:
    report = validate_guard(
        Path(args.file),
        args.expected_exit,
        args.expected_verdict,
        args.finding or [],
        args.expected_root,
        args.observed_exit,
    )
    if args.output:
        require_within(
            Path(args.output), Path(args.artifact_root), label="guard validation"
        )
        write_new(Path(args.output), canonical_json(report))
    else:
        sys.stdout.buffer.write(canonical_json(report))
    return PASS


def cmd_validate_run(args: argparse.Namespace) -> int:
    report = validate_run(
        Path(args.file),
        args.schema,
        args.expected_verdict,
        expected_active_stage=args.expected_active_stage,
        expected_planted_stage=args.expected_planted_stage,
        live_context=not args.offline,
    )
    if args.output:
        require_within(
            Path(args.output), Path(args.artifact_root), label="run validation"
        )
        write_new(Path(args.output), canonical_json(report))
    else:
        sys.stdout.buffer.write(canonical_json(report))
    return PASS


def cmd_hash_tree(args: argparse.Namespace) -> int:
    inventory_path = Path(args.inventory) if args.inventory else None
    root = tree_hash(
        Path(args.root),
        args.path,
        inventory_path=inventory_path,
        vendor_path=args.vendor_path,
    )
    if args.output:
        if not args.artifact_root:
            raise EvidenceError("hash-tree --output requires --artifact-root")
        require_within(
            Path(args.output), Path(args.artifact_root), label="tree-hash output"
        )
        write_new(Path(args.output), f"{root}\n".encode())
    else:
        print(root)
    return PASS


def cmd_vendor_binding(args: argparse.Namespace) -> int:
    binding = verify_vendor_binding(Path(args.root), args.vendor_path)
    if args.output:
        require_within(
            Path(args.output), Path(args.artifact_root), label="vendor binding"
        )
        write_new(Path(args.output), canonical_json(binding))
    else:
        sys.stdout.buffer.write(canonical_json(binding))
    return PASS


def cmd_ubs_inventory(args: argparse.Namespace) -> int:
    root = Path(args.root)
    inventory = collect_ubs_inventory(root, args.scope)
    output = Path(args.output)
    require_within(output, Path(args.artifact_root), label="UBS inventory")
    write_new(output, canonical_json(inventory))
    validate_ubs_inventory(output, root)
    return PASS


def cmd_validate_ubs_inventory(args: argparse.Namespace) -> int:
    report = validate_ubs_inventory(Path(args.inventory), Path(args.root))
    sys.stdout.buffer.write(canonical_json(report))
    return PASS


def cmd_exec_ubs_inventory(args: argparse.Namespace) -> int:
    command = list(args.command)
    if command and command[0] == "--":
        command = command[1:]
    if not command:
        raise EvidenceError("inventory execution requires a command")
    inventory = validate_ubs_inventory(Path(args.inventory), Path(args.root))
    argv = [*command, *(row["path"] for row in inventory["files"])]
    os.execvp(argv[0], argv)
    raise EvidenceError("inventory execution unexpectedly returned")


def cmd_emergency_kill(args: argparse.Namespace) -> int:
    emergency_kill(
        Path(args.readiness), args.expected_wrapper_pid, args.expected_stage_id
    )
    return PASS


def cmd_manifest(args: argparse.Namespace) -> int:
    generate_manifest(
        Path(args.art_dir),
        Path(args.output),
        Path(args.digest_output),
        args.run_id,
        args.bead,
        args.scenario,
        args.verdict,
        args.input_root,
        args.final_root,
    )
    return PASS


def cmd_validate_manifest(args: argparse.Namespace) -> int:
    validate_manifest(
        Path(args.art_dir),
        Path(args.manifest),
        Path(args.digest),
        live_context=not args.offline,
    )
    return PASS


def cmd_complete_bundle(args: argparse.Namespace) -> int:
    complete_bundle(
        Path(args.art_dir),
        Path(args.manifest),
        Path(args.digest),
        Path(args.output),
        governed_root=Path(args.governed_root),
        governed_paths=args.governed_path,
        expected_root=args.expected_root,
        inventory_path=Path(args.inventory) if args.inventory else None,
        vendor_path=args.vendor_path,
    )
    return PASS


def cmd_validate_bundle(args: argparse.Namespace) -> int:
    report = validate_bundle(
        Path(args.art_dir),
        Path(args.manifest),
        Path(args.digest),
        Path(args.commit),
    )
    if args.output:
        output = lexical_absolute(Path(args.output))
        art_dir = lexical_absolute(Path(args.art_dir))
        try:
            output.relative_to(art_dir)
        except ValueError:
            pass
        else:
            raise EvidenceError(
                "bundle validation output cannot mutate the committed bundle"
            )
        require_within(
            Path(args.output), Path(args.artifact_root), label="bundle validation"
        )
        write_new(Path(args.output), canonical_json(report))
    else:
        sys.stdout.buffer.write(canonical_json(report))
    return PASS


def read_json_object(path: Path) -> dict[str, Any]:
    data, _size, _digest = stable_file_facts(path, max_bytes=MAX_LOG_BYTES)
    value = parse_json(data, subject=str(path))
    if not isinstance(value, dict):
        raise EvidenceError(f"expected JSON object: {path}")
    return value


def require(condition: bool, detail: str) -> None:
    if not condition:
        raise EvidenceError(detail)


def cmd_self_test(args: argparse.Namespace) -> int:
    """Exercise supervisor boundary cases without mocks or disposable fixtures."""
    art_dir = lexical_absolute(Path(args.art_dir))
    if art_dir.exists() or art_dir.is_symlink():
        raise EvidenceError(f"self-test artifact directory already exists: {art_dir}")
    _created, created_fd = open_directory_nofollow(art_dir, create=True)
    os.close(created_fd)
    cases: list[dict[str, Any]] = []

    def case_dir(name: str) -> Path:
        path = art_dir / name
        path.mkdir()
        return path

    def run_case(
        name: str,
        command: Sequence[str],
        *,
        capture: int = 4096,
        budget: int = 262_144,
        timeout: int = 5000,
        cancel_after: int | None = None,
        stdout_override: Path | None = None,
        semantic_exits: Sequence[int] = (),
    ) -> tuple[int, dict[str, Any], Path]:
        root = case_dir(name)
        metadata = root / "stage.meta.json"
        stdout = stdout_override or root / "stage.out"
        stderr = root / "stage.err"
        readiness = root / "stage.ready.json"
        rc = run_supervised(
            argv=command,
            cwd=art_dir,
            metadata_path=metadata,
            stdout_path=stdout,
            stderr_path=stderr,
            readiness_path=readiness,
            artifact_root=art_dir,
            capture_bytes=capture,
            output_budget_bytes=budget,
            timeout_ms=timeout,
            grace_ms=500,
            stage_id=name,
            planted=False,
            semantic_failure_exits=semantic_exits,
            cancel_after_ms=cancel_after,
        )
        meta = read_json_object(metadata)
        return rc, meta, root

    flood_size = 32_768
    flood_program = (
        "import sys;"
        f"sys.stdout.buffer.write(b'A'*{flood_size}+b'OUT_TAIL');"
        f"sys.stderr.buffer.write(b'B'*{flood_size}+b'ERR_TAIL')"
    )
    rc, meta, root = run_case(
        "large_output_pass",
        [sys.executable, "-c", flood_program, "--token=supersecret"],
        capture=4096,
        budget=262_144,
    )
    require(
        rc == PASS and meta["classification"] == "pass", "large output changed exit"
    )
    require(
        meta["stdout"]["truncated"] and meta["stderr"]["truncated"],
        "flood not truncated",
    )
    out_data, out_size, _out_digest = stable_file_facts(root / "stage.out")
    err_data, err_size, _err_digest = stable_file_facts(root / "stage.err")
    require(out_size <= 4096, "stdout capture exceeded bound")
    require(err_size <= 4096, "stderr capture exceeded bound")
    require(out_data.endswith(b"OUT_TAIL"), "stdout tail lost")
    require(err_data.endswith(b"ERR_TAIL"), "stderr tail lost")
    serialized = canonical_json(meta)
    require(
        b"supersecret" not in serialized and b"<redacted>" in serialized,
        "secret leaked",
    )
    cases.append(
        {
            "case": "large_output_pass",
            "ok": True,
            "metadata": str(root / "stage.meta.json"),
        }
    )

    rc, meta, root = run_case(
        "semantic_failure",
        [sys.executable, "-c", "raise SystemExit(7)"],
        semantic_exits=[7],
    )
    require(
        rc == FAIL and meta["classification"] == "fail",
        "semantic exit was not a failure",
    )
    require(meta["child_exit"] == 7, "semantic child exit was not retained")
    cases.append(
        {
            "case": "semantic_failure",
            "ok": True,
            "metadata": str(root / "stage.meta.json"),
        }
    )

    rc, meta, root = run_case(
        "unexpected_child_exit",
        [sys.executable, "-c", "raise SystemExit(7)"],
    )
    require(
        rc == SETUP_FAILURE and meta["classification"] == "internal_fault",
        "unexpected child exit was mislabeled semantic",
    )
    cases.append(
        {
            "case": "unexpected_child_exit",
            "ok": True,
            "metadata": str(root / "stage.meta.json"),
        }
    )

    rc, meta, root = run_case(
        "unexpected_child_signal",
        [sys.executable, "-c", "import os,signal;os.kill(os.getpid(),signal.SIGKILL)"],
    )
    require(
        rc == INCONCLUSIVE and meta["classification"] == "inconclusive",
        "unexpected child signal was mislabeled semantic",
    )
    cases.append(
        {
            "case": "unexpected_child_signal",
            "ok": True,
            "metadata": str(root / "stage.meta.json"),
        }
    )

    endless_output = "import os; b=b'x'*65536\nwhile True: os.write(1,b); os.write(2,b)"
    rc, meta, root = run_case(
        "output_budget_exhausted",
        [sys.executable, "-c", endless_output],
        capture=4096,
        budget=8192,
        timeout=5000,
    )
    require(rc == INCONCLUSIVE, "output exhaustion did not return inconclusive")
    require(meta["classification"] == "inconclusive", "output exhaustion misclassified")
    require(
        meta["reason_code"] == "output_budget_exhausted",
        "wrong output exhaustion reason",
    )
    cases.append(
        {
            "case": "output_budget_exhausted",
            "ok": True,
            "metadata": str(root / "stage.meta.json"),
        }
    )

    rc, meta, root = run_case(
        "spawn_failure",
        [str(art_dir / "definitely-missing-command")],
        capture=4096,
        budget=65_536,
    )
    require(rc == SETUP_FAILURE, "spawn failure did not return internal-fault exit")
    require(meta["classification"] == "internal_fault", "spawn failure misclassified")
    spawn_ready = read_json_object(root / "stage.ready.json")
    require(
        spawn_ready["status"] == "spawn_failed", "spawn failure readiness is untyped"
    )
    cases.append(
        {"case": "spawn_failure", "ok": True, "metadata": str(root / "stage.meta.json")}
    )

    pid_file = art_dir / "timeout-pids.txt"
    tree_program = (
        "import os,pathlib,subprocess,sys,time;"
        "code='import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(60)';"
        "p=subprocess.Popen([sys.executable,'-c',code],start_new_session=True);"
        f"pathlib.Path({str(pid_file)!r}).write_text(str(os.getpid())+'\\n'+str(p.pid)+'\\n');"
        "time.sleep(60)"
    )
    rc, meta, root = run_case(
        "timeout",
        [sys.executable, "-c", tree_program],
        capture=4096,
        budget=65_536,
        timeout=250,
    )
    require(
        rc == INCONCLUSIVE and meta["reason_code"] == "timeout", "timeout misclassified"
    )
    pids = [int(value) for value in pid_file.read_text(encoding="utf-8").splitlines()]
    time.sleep(0.1)
    require(
        not any(process_alive(pid) for pid in pids),
        "timeout left a live process-tree member",
    )
    cases.append(
        {
            "case": "timeout",
            "ok": True,
            "metadata": str(root / "stage.meta.json"),
            "pids": pids,
        }
    )

    leader_root = case_dir("leader_exit_with_inherited_pipe")
    leader_pid_file = leader_root / "pids.txt"
    leader_program = (
        "import os,pathlib,subprocess,sys;"
        "code='import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(60)';"
        "p=subprocess.Popen([sys.executable,'-c',code],start_new_session=True);"
        f"pathlib.Path({str(leader_pid_file)!r}).write_text(str(os.getpid())+'\\n'+str(p.pid)+'\\n')"
    )
    rc = run_supervised(
        argv=[sys.executable, "-c", leader_program],
        cwd=art_dir,
        metadata_path=leader_root / "stage.meta.json",
        stdout_path=leader_root / "stage.out",
        stderr_path=leader_root / "stage.err",
        readiness_path=leader_root / "stage.ready.json",
        artifact_root=art_dir,
        capture_bytes=4096,
        output_budget_bytes=65_536,
        timeout_ms=5000,
        grace_ms=500,
        stage_id="leader_exit_with_inherited_pipe",
        planted=False,
    )
    leader_meta = read_json_object(leader_root / "stage.meta.json")
    require(
        rc == SETUP_FAILURE, "leader-first descendant leak was not an internal fault"
    )
    leader_pids = [
        int(value) for value in leader_pid_file.read_text(encoding="utf-8").splitlines()
    ]
    require(
        not any(process_alive(pid) for pid in leader_pids),
        "leader-first inherited-pipe descendant survived",
    )
    cases.append(
        {
            "case": "leader_exit_with_inherited_pipe",
            "ok": True,
            "metadata": str(leader_root / "stage.meta.json"),
            "pids": leader_pids,
            "classification": leader_meta["classification"],
        }
    )

    cancel_root = case_dir("cancel_term")
    cancel_pid_file = cancel_root / "pids.txt"
    cancel_program = (
        "import os,pathlib,subprocess,sys,time;"
        "code='import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(60)';"
        "p=subprocess.Popen([sys.executable,'-c',code],start_new_session=True);"
        f"pathlib.Path({str(cancel_pid_file)!r}).write_text(str(os.getpid())+'\\n'+str(p.pid)+'\\n');"
        "time.sleep(60)"
    )
    wrapper = subprocess.Popen(
        [
            sys.executable,
            str(Path(__file__).resolve()),
            "run",
            "--cwd",
            str(art_dir),
            "--metadata",
            str(cancel_root / "stage.meta.json"),
            "--stdout",
            str(cancel_root / "stage.out"),
            "--stderr",
            str(cancel_root / "stage.err"),
            "--readiness",
            str(cancel_root / "stage.ready.json"),
            "--artifact-root",
            str(art_dir),
            "--capture-bytes",
            "4096",
            "--output-budget-bytes",
            "65536",
            "--timeout-ms",
            "5000",
            "--grace-ms",
            "500",
            "--stage-id",
            "cancel_term",
            "--",
            sys.executable,
            "-c",
            cancel_program,
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    wait_deadline = time.monotonic() + 3
    while (
        not (cancel_pid_file.exists() and (cancel_root / "stage.ready.json").exists())
        and wrapper.poll() is None
        and time.monotonic() < wait_deadline
    ):
        time.sleep(0.02)
    require(cancel_pid_file.exists(), "cancellation child did not publish PIDs")
    require(
        (cancel_root / "stage.ready.json").exists(),
        "supervisor readiness was not published",
    )
    wrapper.send_signal(signal.SIGTERM)
    _wrapper_out, wrapper_err = wrapper.communicate(timeout=5)
    require(
        wrapper.returncode == CANCELLED,
        f"cancellation wrapper exit {wrapper.returncode}: {wrapper_err!r}",
    )
    cancel_meta = read_json_object(cancel_root / "stage.meta.json")
    require(
        cancel_meta["classification"] == "cancelled",
        "TERM was not typed as cancellation",
    )
    cancel_pids = [
        int(value) for value in cancel_pid_file.read_text(encoding="utf-8").splitlines()
    ]
    time.sleep(0.1)
    require(
        not any(process_alive(pid) for pid in cancel_pids),
        "TERM left a live process-tree member",
    )
    cases.append(
        {
            "case": "cancel_term",
            "ok": True,
            "metadata": str(cancel_root / "stage.meta.json"),
            "pids": cancel_pids,
        }
    )

    collision_root = case_dir("artifact_publication_failure")
    collision = collision_root / "not-a-directory"
    write_new(collision, b"collision\n")
    metadata = collision_root / "stage.meta.json"
    rc = run_supervised(
        argv=[sys.executable, "-c", "print('must-not-pass')"],
        cwd=art_dir,
        metadata_path=metadata,
        stdout_path=collision / "stage.out",
        stderr_path=collision_root / "stage.err",
        readiness_path=collision_root / "stage.ready.json",
        artifact_root=art_dir,
        capture_bytes=4096,
        output_budget_bytes=65_536,
        timeout_ms=5000,
        grace_ms=500,
        stage_id="artifact_publication_failure",
        planted=False,
    )
    meta = read_json_object(metadata)
    require(rc == SETUP_FAILURE, "artifact publication failure returned success")
    require(
        meta["classification"] == "internal_fault",
        "artifact failure was not internal fault",
    )
    require(
        meta["reason_code"] == "artifact_publication_failure",
        "artifact failure reason lost",
    )
    cases.append(
        {"case": "artifact_publication_failure", "ok": True, "metadata": str(metadata)}
    )

    malformed_root = case_dir("malformed_evidence")
    malformed = malformed_root / "malformed.ndjson"
    write_new(malformed, b'{"schema":"fln.check/2"\n')
    try:
        validate_run(malformed, "fln.check/2", "pass")
    except EvidenceError:
        pass
    else:
        raise EvidenceError("malformed NDJSON was accepted")
    incomplete = malformed_root / "incomplete.ndjson"
    write_new(
        incomplete,
        canonical_json(
            {
                "schema": "fln.check/2",
                "event": "run_start",
                "run_id": "incomplete",
                "bead": "fln-8mj",
                "sequence": 0,
                "monotonic_ns": 1,
                "wall_time_utc": utc_now(),
            }
        ),
    )
    try:
        validate_run(incomplete, "fln.check/2", "pass")
    except EvidenceError:
        pass
    else:
        raise EvidenceError("unterminated run was accepted")
    cases.append({"case": "malformed_evidence", "ok": True})

    hash_root = case_dir("canonical_hash")
    write_new(hash_root / "a", b"alpha")
    write_new(hash_root / "b", b"beta")
    first_hash = tree_hash(hash_root, ["a", "b"])
    second_hash = tree_hash(hash_root, ["b", "a"])
    require(first_hash == second_hash, "canonical tree hash depends on argument order")
    cases.append({"case": "canonical_hash", "ok": True, "root": first_hash})

    manifest_root = case_dir("write_once_manifest")
    manifest_run_id = "manifest-self-test"
    manifest_meta = manifest_root / "manifest-stage.meta.json"
    manifest_rc = run_supervised(
        argv=[sys.executable, "-c", "print('manifest-stage')"],
        cwd=art_dir,
        metadata_path=manifest_meta,
        stdout_path=manifest_root / "manifest-stage.out",
        stderr_path=manifest_root / "manifest-stage.err",
        readiness_path=manifest_root / "manifest-stage.ready.json",
        artifact_root=manifest_root,
        capture_bytes=4096,
        output_budget_bytes=65_536,
        timeout_ms=5000,
        grace_ms=500,
        stage_id="manifest-stage",
        planted=False,
    )
    require(manifest_rc == PASS, "manifest self-test stage failed")
    manifest_supervisor = read_json_object(manifest_meta)
    manifest_records = [
        {
            "schema": "fln.check/2",
            "event": "run_start",
            "run_id": manifest_run_id,
            "bead": "fln-8mj",
            "scenario": "self_test",
            "sequence": 0,
            "monotonic_ns": 1,
            "wall_time_utc": utc_now(),
            "argv": ["evidence.py", "self-test"],
            "cwd": str(art_dir),
            "claim_ids": ["FLN-EVIDENCE-SELF-TEST"],
            "invariant_ids": ["FL-INV-07"],
            "gate_ids": ["G0-10"],
            "epoch": "lean-v4.32.0",
            "mode": "sound",
            "profile": "evidence-manifest-self-test",
            "platform": platform.platform(),
            "host_facts": {
                "machine": platform.machine(),
                "python": platform.python_version(),
                "release": platform.release(),
                "system": platform.system(),
            },
            "thread_count": 1,
            "seed": "deterministic",
            "cache_state": "not_applicable",
            "input_root": first_hash,
            "budgets": {"timeout_ms": 5000},
            "parity_ledger_row": "not_applicable_evidence_self_test",
            "planted": "",
        },
        {
            "schema": "fln.check/2",
            "event": "stage",
            "run_id": manifest_run_id,
            "bead": "fln-8mj",
            "scenario": "self_test",
            "sequence": 1,
            "monotonic_ns": 2,
            "wall_time_utc": utc_now(),
            "stage": "manifest-stage",
            "outcome": "pass",
            "reason_code": "exit_zero",
            "expected": "exit_zero",
            "actual": "pass",
            "wrapper_exit": 0,
            "supervisor": manifest_supervisor,
        },
        {
            "schema": "fln.check/2",
            "event": "run_end",
            "run_id": manifest_run_id,
            "bead": "fln-8mj",
            "scenario": "self_test",
            "sequence": 2,
            "monotonic_ns": 3,
            "wall_time_utc": utc_now(),
            "verdict": "pass",
            "reason_code": "self_test_complete",
            "process_exit": 0,
            "active_stage": "complete",
            "duration_ns": 2,
            "cleanup_status": "retained_by_policy",
            "final_state": first_hash,
            "logical_root": first_hash,
            "receipt_root": "not_applicable_evidence_self_test",
            "first_divergence": "none",
            "evidence_manifest": "manifest.json",
            "bundle_commit": "bundle.complete.json",
            "evidence_state": "pending_bundle_commit",
        },
    ]
    write_new(
        manifest_root / "run.ndjson",
        b"".join(canonical_json(record) for record in manifest_records),
    )
    run_report = validate_run(manifest_root / "run.ndjson", "fln.check/2", "pass")
    write_new(manifest_root / "run.validation.json", canonical_json(run_report))
    generate_manifest(
        manifest_root,
        manifest_root / "manifest.json",
        manifest_root / "manifest.digest",
        manifest_run_id,
        "fln-8mj",
        "self_test",
        "pass",
        first_hash,
        first_hash,
    )
    try:
        validate_bundle(
            manifest_root,
            manifest_root / "manifest.json",
            manifest_root / "manifest.digest",
            manifest_root / "bundle.complete.json",
        )
    except (EvidenceError, FileNotFoundError):
        pass
    else:
        raise EvidenceError("bundle without a commit marker was accepted")
    complete_bundle(
        manifest_root,
        manifest_root / "manifest.json",
        manifest_root / "manifest.digest",
        manifest_root / "bundle.complete.json",
        governed_root=hash_root,
        governed_paths=["a", "b"],
        expected_root=first_hash,
    )
    validate_bundle(
        manifest_root,
        manifest_root / "manifest.json",
        manifest_root / "manifest.digest",
        manifest_root / "bundle.complete.json",
    )
    try:
        write_new(manifest_root / "bundle.complete.json", b"overwrite\n")
    except FileExistsError:
        pass
    else:
        raise EvidenceError("write-once bundle marker was overwritten")
    cases.append({"case": "write_once_manifest", "ok": True})

    race_root = case_dir("write_collision_race")
    race_path = race_root / "collision-race.txt"
    race_results: list[str] = []

    def race_writer(value: bytes) -> None:
        try:
            write_new(race_path, value)
            race_results.append("published")
        except FileExistsError:
            race_results.append("collision")

    first_writer = threading.Thread(target=race_writer, args=(b"first\n",))
    second_writer = threading.Thread(target=race_writer, args=(b"second\n",))
    first_writer.start()
    second_writer.start()
    first_writer.join()
    second_writer.join()
    require(
        sorted(race_results) == ["collision", "published"],
        "collision race was not exclusive",
    )
    race_data, _race_size, _race_digest = stable_file_facts(race_path)
    require(race_data in {b"first\n", b"second\n"}, "collision race corrupted evidence")
    cases.append({"case": "write_collision_race", "ok": True})

    report = {
        "schema": "fln.evidence-self-test/1",
        "verdict": "pass",
        "created_utc": utc_now(),
        "cases": cases,
    }
    write_new(art_dir / "self-test.json", canonical_json(report))
    print(
        f"evidence self-test: PASS ({len(cases)} cases); artifacts: {art_dir}",
        file=sys.stderr,
    )
    return PASS


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="subcommand", required=True)

    emit_parser = subparsers.add_parser("emit", help="append one encoded NDJSON event")
    emit_parser.add_argument("--file", required=True)
    emit_parser.add_argument("--artifact-root", required=True)
    emit_parser.add_argument("--new-log", action="store_true")
    emit_parser.add_argument("--string", nargs=2, action="append")
    emit_parser.add_argument("--integer", nargs=2, action="append")
    emit_parser.add_argument("--boolean", nargs=2, action="append")
    emit_parser.add_argument("--null", action="append")
    emit_parser.add_argument("--json-value", nargs=2, action="append")
    emit_parser.add_argument("--append-string", nargs=2, action="append")
    emit_parser.add_argument("--json-file", nargs=2, action="append")
    emit_parser.set_defaults(func=cmd_emit)

    run_parser = subparsers.add_parser(
        "run", help="run one command under bounded capture"
    )
    run_parser.add_argument("--cwd", required=True)
    run_parser.add_argument("--metadata", required=True)
    run_parser.add_argument("--stdout", required=True)
    run_parser.add_argument("--stderr", required=True)
    run_parser.add_argument("--readiness", required=True)
    run_parser.add_argument("--artifact-root", required=True)
    run_parser.add_argument("--capture-bytes", type=int, required=True)
    run_parser.add_argument("--output-budget-bytes", type=int, required=True)
    run_parser.add_argument("--timeout-ms", type=int, required=True)
    run_parser.add_argument("--grace-ms", type=int, required=True)
    run_parser.add_argument("--stage-id", required=True)
    run_parser.add_argument("--planted", action="store_true")
    run_parser.add_argument("--semantic-failure-exit", type=int, action="append")
    run_parser.add_argument("--cancel-after-ms", type=int)
    run_parser.add_argument("command", nargs=argparse.REMAINDER)
    run_parser.set_defaults(func=cmd_run)

    guard_parser = subparsers.add_parser(
        "validate-guard", help="validate exact structure-guard NDJSON semantics"
    )
    guard_parser.add_argument("--file", required=True)
    guard_parser.add_argument("--expected-exit", type=int, required=True)
    guard_parser.add_argument("--expected-verdict", required=True)
    guard_parser.add_argument("--expected-root", required=True)
    guard_parser.add_argument("--observed-exit", type=int, required=True)
    guard_parser.add_argument("--artifact-root", required=True)
    guard_parser.add_argument("--finding", action="append")
    guard_parser.add_argument("--output")
    guard_parser.set_defaults(func=cmd_validate_guard)

    run_validation = subparsers.add_parser(
        "validate-run", help="validate a check/E2E run envelope"
    )
    run_validation.add_argument("--file", required=True)
    run_validation.add_argument("--schema", required=True)
    run_validation.add_argument("--expected-verdict", required=True)
    run_validation.add_argument("--expected-active-stage")
    run_validation.add_argument("--expected-planted-stage")
    run_validation.add_argument("--artifact-root", required=True)
    run_validation.add_argument("--output")
    run_validation.add_argument("--offline", action="store_true")
    run_validation.set_defaults(func=cmd_validate_run)

    hash_parser = subparsers.add_parser("hash-tree", help="hash canonical input files")
    hash_parser.add_argument("--root", required=True)
    hash_parser.add_argument("--path", action="append", required=True)
    hash_parser.add_argument("--inventory")
    hash_parser.add_argument("--vendor-path")
    hash_parser.add_argument("--output")
    hash_parser.add_argument("--artifact-root")
    hash_parser.set_defaults(func=cmd_hash_tree)

    vendor_parser = subparsers.add_parser(
        "vendor-binding",
        help="verify and publish the pinned Reference Git-tree binding",
    )
    vendor_parser.add_argument("--root", required=True)
    vendor_parser.add_argument("--vendor-path", required=True)
    vendor_parser.add_argument("--output")
    vendor_parser.add_argument("--artifact-root")
    vendor_parser.set_defaults(func=cmd_vendor_binding)

    inventory_parser = subparsers.add_parser(
        "ubs-inventory", help="publish an exact project-authored UBS file inventory"
    )
    inventory_parser.add_argument("--root", required=True)
    inventory_parser.add_argument(
        "--scope", required=True, choices=("changed", "all-tracked")
    )
    inventory_parser.add_argument("--output", required=True)
    inventory_parser.add_argument("--artifact-root", required=True)
    inventory_parser.set_defaults(func=cmd_ubs_inventory)

    inventory_validation = subparsers.add_parser(
        "validate-ubs-inventory",
        help="verify an exact UBS inventory against the workspace",
    )
    inventory_validation.add_argument("--root", required=True)
    inventory_validation.add_argument("--inventory", required=True)
    inventory_validation.set_defaults(func=cmd_validate_ubs_inventory)

    inventory_execution = subparsers.add_parser(
        "exec-ubs-inventory", help="exec a command with validated UBS paths appended"
    )
    inventory_execution.add_argument("--root", required=True)
    inventory_execution.add_argument("--inventory", required=True)
    inventory_execution.add_argument("command", nargs=argparse.REMAINDER)
    inventory_execution.set_defaults(func=cmd_exec_ubs_inventory)

    emergency_parser = subparsers.add_parser(
        "emergency-kill", help="validate readiness and SIGKILL its bound child group"
    )
    emergency_parser.add_argument("--readiness", required=True)
    emergency_parser.add_argument("--expected-wrapper-pid", type=int, required=True)
    emergency_parser.add_argument("--expected-stage-id", required=True)
    emergency_parser.set_defaults(func=cmd_emergency_kill)

    manifest_parser = subparsers.add_parser(
        "manifest", help="publish an evidence manifest"
    )
    manifest_parser.add_argument("--art-dir", required=True)
    manifest_parser.add_argument("--output", required=True)
    manifest_parser.add_argument("--digest-output", required=True)
    manifest_parser.add_argument("--run-id", required=True)
    manifest_parser.add_argument("--bead", required=True)
    manifest_parser.add_argument("--scenario", required=True)
    manifest_parser.add_argument("--verdict", required=True)
    manifest_parser.add_argument("--input-root", required=True)
    manifest_parser.add_argument("--final-root", required=True)
    manifest_parser.set_defaults(func=cmd_manifest)

    manifest_validation = subparsers.add_parser(
        "validate-manifest",
        help="verify every manifested artifact and terminal binding",
    )
    manifest_validation.add_argument("--art-dir", required=True)
    manifest_validation.add_argument("--manifest", required=True)
    manifest_validation.add_argument("--digest", required=True)
    manifest_validation.add_argument("--offline", action="store_true")
    manifest_validation.set_defaults(func=cmd_validate_manifest)

    complete_parser = subparsers.add_parser(
        "complete-bundle", help="commit a fully validated evidence bundle"
    )
    complete_parser.add_argument("--art-dir", required=True)
    complete_parser.add_argument("--manifest", required=True)
    complete_parser.add_argument("--digest", required=True)
    complete_parser.add_argument("--output", required=True)
    complete_parser.add_argument("--governed-root", required=True)
    complete_parser.add_argument("--governed-path", action="append", required=True)
    complete_parser.add_argument("--expected-root", required=True)
    complete_parser.add_argument("--inventory")
    complete_parser.add_argument("--vendor-path")
    complete_parser.set_defaults(func=cmd_complete_bundle)

    bundle_validation = subparsers.add_parser(
        "validate-bundle", help="verify a committed evidence bundle"
    )
    bundle_validation.add_argument("--art-dir", required=True)
    bundle_validation.add_argument("--manifest", required=True)
    bundle_validation.add_argument("--digest", required=True)
    bundle_validation.add_argument("--commit", required=True)
    bundle_validation.add_argument("--artifact-root", required=True)
    bundle_validation.add_argument("--output")
    bundle_validation.set_defaults(func=cmd_validate_bundle)

    self_test_parser = subparsers.add_parser(
        "self-test", help="exercise capture, cancellation, exhaustion, and validation"
    )
    self_test_parser.add_argument("--art-dir", required=True)
    self_test_parser.set_defaults(func=cmd_self_test)
    return parser


def main() -> int:
    try:
        args = build_parser().parse_args()
        return int(args.func(args))
    except (
        EvidenceError,
        OSError,
        ValueError,
        TypeError,
        KeyError,
        IndexError,
    ) as error:
        print(f"evidence: {error}", file=sys.stderr)
        return SETUP_FAILURE


if __name__ == "__main__":
    raise SystemExit(main())
