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
import errno
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
from functools import partial
from pathlib import Path
from typing import Any, Callable, Iterable, Sequence


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
PROCESS_GROUP_FREEZE_ATTEMPTS = 8
PROCESS_GROUP_FREEZE_TIMEOUT_S = 10.0
PROCESS_GROUP_KILL_ATTEMPTS = 2000
PROCESS_GROUP_KILL_TIMEOUT_S = 10.0
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


def require_exact_artifact_path(
    path: Path, art_dir: Path, filename: str, *, label: str
) -> Path:
    """Bind a canonical bundle control file to the artifact-directory root."""
    root = lexical_absolute(art_dir)
    absolute = require_within(path, root, label=label)
    expected = root / filename
    if absolute != expected:
        raise EvidenceError(f"{label} must be exactly {expected}")
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


def prepare_atomic_file(parent_fd: int, data: bytes, mode: int = 0o644) -> int:
    if not hasattr(os, "O_TMPFILE"):
        raise EvidenceError("atomic evidence publication requires Linux O_TMPFILE")
    descriptor = os.open(
        ".",
        os.O_WRONLY | os.O_TMPFILE | os.O_CLOEXEC,
        mode,
        dir_fd=parent_fd,
    )
    try:
        view = memoryview(data)
        while view:
            written = os.write(descriptor, view)
            if written <= 0:
                raise EvidenceError("short write while preparing atomic evidence")
            view = view[written:]
        os.fsync(descriptor)
        return descriptor
    except BaseException:
        os.close(descriptor)
        raise


def link_prepared_atomic_file(
    parent_fd: int,
    descriptor: int,
    name: str,
    *,
    test_fail_after_link: bool = False,
) -> bool:
    try:
        os.link(
            f"/proc/self/fd/{descriptor}",
            name,
            dst_dir_fd=parent_fd,
            follow_symlinks=True,
        )
    except FileExistsError:
        return False
    if test_fail_after_link:
        raise EvidenceError("injected failure after atomic link")
    os.fsync(parent_fd)
    return True


def write_atomic_new(path: Path, data: bytes, mode: int = 0o644) -> None:
    """Publish complete bytes at an absent final name in one atomic link step."""
    absolute = lexical_absolute(path)
    _parent, parent_fd = open_directory_nofollow(absolute.parent, create=True)
    descriptor: int | None = None
    try:
        descriptor = prepare_atomic_file(parent_fd, data, mode)
        if not link_prepared_atomic_file(parent_fd, descriptor, absolute.name):
            raise FileExistsError(absolute)
    finally:
        if descriptor is not None:
            os.close(descriptor)
        os.close(parent_fd)


def write_signal_committed_atomic_new(
    path: Path,
    data: bytes,
    mode: int = 0o644,
    *,
    decision_path: Path | None = None,
    restore_signal_state: bool = True,
    test_fail_after_link: bool = False,
) -> None:
    """Race cancellation and commit on one write-once cross-process decision."""
    absolute = lexical_absolute(path)
    decision_absolute = (
        lexical_absolute(decision_path) if decision_path is not None else None
    )
    if (
        decision_absolute is not None
        and decision_absolute.parent != absolute.parent
    ):
        raise EvidenceError("commit decision and final marker must share a directory")
    _parent, parent_fd = open_directory_nofollow(absolute.parent, create=True)
    descriptor: int | None = None
    watched = (signal.SIGHUP, signal.SIGINT, signal.SIGTERM)
    old_handlers = {signum: signal.getsignal(signum) for signum in watched}
    previous_mask: set[signal.Signals] | None = None
    try:
        descriptor = prepare_atomic_file(parent_fd, data, mode)
        previous_mask = signal.pthread_sigmask(signal.SIG_BLOCK, watched)
        if any(signum in signal.sigpending() for signum in watched):
            for signum in watched:
                signal.signal(signum, signal.SIG_IGN)
            signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)
            previous_mask = None
            raise EvidenceError("signal arrived before atomic evidence commit")
        # The pending-signal sample is the commit point. Later watched signals are
        # blocked locally, while the shared decision path also arbitrates signals
        # already observed by the parent shell.
        for signum in watched:
            signal.signal(signum, signal.SIG_IGN)
        if decision_absolute is None:
            if not link_prepared_atomic_file(
                parent_fd,
                descriptor,
                absolute.name,
                test_fail_after_link=test_fail_after_link,
            ):
                raise FileExistsError(absolute)
        else:
            decision_won = link_prepared_atomic_file(
                parent_fd,
                descriptor,
                decision_absolute.name,
                test_fail_after_link=test_fail_after_link,
            )
            if not decision_won:
                decision_data, _size, _digest = stable_file_facts(decision_absolute)
                if not hmac.compare_digest(decision_data, data):
                    raise EvidenceError("cancellation won the bundle decision race")
            try:
                os.link(
                    decision_absolute.name,
                    absolute.name,
                    src_dir_fd=parent_fd,
                    dst_dir_fd=parent_fd,
                    follow_symlinks=False,
                )
            except FileExistsError:
                marker_data, _size, _digest = stable_file_facts(absolute)
                if not hmac.compare_digest(marker_data, data):
                    raise EvidenceError("bundle marker disagrees with commit decision")
            os.fsync(parent_fd)
    finally:
        if previous_mask is not None:
            signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)
        if restore_signal_state:
            for signum, handler in old_handlers.items():
                signal.signal(signum, handler)
        if descriptor is not None:
            os.close(descriptor)
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
    except OSError as error:
        if error.errno in {errno.ENOENT, errno.ESRCH}:
            return None
        raise EvidenceError(f"cannot inspect process {pid}: {error}") from error
    except UnicodeError as error:
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


def arm_parent_death_kill(expected_parent_pid: int) -> None:
    """Kill this process if its exact launching parent exits."""
    if sys.platform != "linux":
        raise EvidenceError("parent-death containment currently requires Linux")
    if expected_parent_pid <= 1 or expected_parent_pid == os.getpid():
        raise EvidenceError("parent-death identity is malformed")
    if os.getppid() != expected_parent_pid:
        raise EvidenceError("launcher parent changed before parent-death binding")
    libc = ctypes.CDLL(None, use_errno=True)
    # Linux prctl(PR_SET_PDEATHSIG, SIGKILL). The second parent check closes the
    # race where the parent exits after the first check but before prctl.
    if libc.prctl(1, signal.SIGKILL, 0, 0, 0) != 0:
        error_number = ctypes.get_errno()
        raise EvidenceError(
            f"cannot arm launcher parent-death signal: errno {error_number}"
        )
    if os.getppid() != expected_parent_pid:
        os.kill(os.getpid(), signal.SIGKILL)
        raise EvidenceError("launcher parent changed during parent-death binding")


def proc_children(pid: int) -> set[int]:
    task_root = Path(f"/proc/{pid}/task")
    try:
        task_paths = list(task_root.iterdir())
    except OSError as error:
        if error.errno in {errno.ENOENT, errno.ESRCH}:
            return set()
        raise EvidenceError(f"cannot inspect descendants of {pid}: {error}") from error
    children: set[int] = set()
    for task_path in task_paths:
        try:
            raw = (task_path / "children").read_text(encoding="ascii").strip()
        except OSError as error:
            if error.errno in {errno.ENOENT, errno.ESRCH}:
                continue
            raise EvidenceError(
                f"cannot inspect task descendants of {pid}: {error}"
            ) from error
        except UnicodeError as error:
            raise EvidenceError(
                f"cannot inspect task descendants of {pid}: {error}"
            ) from error
        if not raw:
            continue
        try:
            children.update(int(value) for value in raw.split())
        except ValueError as error:
            raise EvidenceError(f"malformed Linux children list for {pid}") from error
    return children


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


def open_process_handle(
    pid: int, *, expected_parent_pid: int | None = None
) -> tuple[int, int] | None:
    """Bind a Linux PID to its lifetime before it can be signalled."""
    if not hasattr(os, "pidfd_open") or not hasattr(signal, "pidfd_send_signal"):
        raise EvidenceError("process supervision requires Linux pidfd support")
    if expected_parent_pid is not None and pid not in proc_children(
        expected_parent_pid
    ):
        return None
    facts = proc_stat_facts(pid)
    if facts is None or facts[0] == "Z":
        return None
    try:
        descriptor = os.pidfd_open(pid, 0)
    except ProcessLookupError:
        return None
    repeated = proc_stat_facts(pid)
    if (
        repeated is None
        or repeated[0] == "Z"
        or repeated[2] != facts[2]
        or (
            expected_parent_pid is not None
            and pid not in proc_children(expected_parent_pid)
        )
    ):
        os.close(descriptor)
        return None
    return facts[2], descriptor


def bind_direct_child_until(
    pid: int,
    expected_parent_pid: int,
    deadline: float,
    *,
    open_handle: Callable[[], tuple[int, int] | None] | None = None,
) -> tuple[int, int]:
    """Retry a lifetime bind while the same live direct child is still unreaped."""
    if open_handle is None:
        open_handle = partial(
            open_process_handle, pid, expected_parent_pid=expected_parent_pid
        )
    while True:
        handle = open_handle()
        if handle is not None:
            return handle
        facts = proc_stat_facts(pid)
        if (
            facts is None
            or facts[0] == "Z"
            or pid not in proc_children(expected_parent_pid)
        ):
            raise EvidenceError("process disappeared before identity binding")
        if time.monotonic() >= deadline:
            raise EvidenceError("process identity did not stabilize in time")
        time.sleep(0.005)


def close_process_handles(handles: ProcessHandles) -> None:
    for _start_ticks, descriptor in handles.values():
        os.close(descriptor)
    handles.clear()


def process_handle_alive(pid: int, handle: tuple[int, int]) -> bool:
    facts = proc_stat_facts(pid)
    return facts is not None and facts[0] != "Z" and facts[2] == handle[0]


def remember_process(
    pid: int, handles: ProcessHandles, *, expected_parent_pid: int | None = None
) -> bool:
    current = handles.get(pid)
    if current is not None:
        if process_handle_alive(pid, current):
            return True
        os.close(current[1])
        del handles[pid]
    opened = open_process_handle(pid)
    if opened is None:
        return False
    if expected_parent_pid is not None and pid not in proc_children(expected_parent_pid):
        os.close(opened[1])
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
        if pid == os.getpid() or pid in visited:
            continue
        if pid == root_pid and pid in known and process_handle_alive(pid, known[pid]):
            visited.add(pid)
            for child in proc_children(pid):
                if child not in visited:
                    pending.append(child)
            continue
        parent_pid = next(
            (
                candidate
                for candidate in ({root_pid, os.getpid()} | visited)
                if pid in proc_children(candidate)
            ),
            None,
        )
        if parent_pid is None or not remember_process(
            pid, known, expected_parent_pid=parent_pid
        ):
            continue
        visited.add(pid)
        for child in proc_children(pid):
            if child not in visited:
                pending.append(child)
    # Once a lifetime was admitted through a proven parent edge, keep it in scope
    # across subreaper/init reparenting until its pidfd-bound identity is dead.
    return {
        pid
        for pid, handle in known.items()
        if pid != os.getpid() and process_handle_alive(pid, handle)
    }


def reap_adopted_children(exclude_pid: int | None = None) -> None:
    for child_pid in proc_children(os.getpid()):
        if child_pid == exclude_pid:
            continue
        try:
            os.waitpid(child_pid, os.WNOHANG)
        except ChildProcessError:
            continue


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
        reap_adopted_children(proc.pid)
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
            reap_adopted_children(proc.pid)
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
    restore_signal_state: bool = True,
    test_terminal_delay_ms: int = 0,
    test_terminal_ready_path: Path | None = None,
    guardian_identity: tuple[int, int] | None = None,
    initial_signal_mask: set[signal.Signals] | None = None,
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
    if test_terminal_delay_ms < 0:
        raise EvidenceError("test terminal delay must be non-negative")
    if test_terminal_ready_path is not None:
        test_terminal_ready_path = require_within(
            test_terminal_ready_path,
            artifact_root,
            label="test terminal readiness",
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
    supervisor_pid = os.getpid()
    supervisor_initial_facts = proc_stat_facts(supervisor_pid)
    supervisor_start_ticks = (
        supervisor_initial_facts[2] if supervisor_initial_facts is not None else 0
    )
    wrapper_pid, wrapper_start_ticks = (
        guardian_identity
        if guardian_identity is not None
        else (supervisor_pid, supervisor_start_ticks)
    )

    def remember_signal(signum: int, _frame: Any) -> None:
        nonlocal cancel_signal
        if cancel_signal is None:
            cancel_signal = signum

    rendered_argv, had_redaction = redacted_argv(argv)
    try:
        enable_child_subreaper()
        for signum in watched_signals:
            signal.signal(signum, remember_signal)
        if initial_signal_mask is not None:
            signal.pthread_sigmask(signal.SIG_SETMASK, initial_signal_mask)
        proc = subprocess.Popen(
            list(argv),
            cwd=cwd,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            start_new_session=True,
        )
        child_facts = proc_stat_facts(proc.pid)
        supervisor_facts = proc_stat_facts(supervisor_pid)
        wrapper_facts = proc_stat_facts(wrapper_pid)
        if (
            child_facts is None
            or supervisor_facts is None
            or supervisor_facts[2] != supervisor_start_ticks
            or wrapper_facts is None
            or wrapper_facts[2] != wrapper_start_ticks
        ):
            raise EvidenceError("cannot capture process identity facts for readiness")
        if child_facts[0] != "Z" and not remember_process(proc.pid, known_descendants):
            raise EvidenceError("cannot bind child process lifetime")
        write_new(
            readiness_path,
            canonical_json(
                {
                    "schema": "fln.supervisor-readiness/1",
                    "stage_id": stage_id,
                    "wrapper_pid": wrapper_pid,
                    "wrapper_start_ticks": wrapper_start_ticks,
                    "supervisor_pid": supervisor_pid,
                    "supervisor_start_ticks": supervisor_start_ticks,
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
                        "wrapper_pid": wrapper_pid,
                        "wrapper_start_ticks": wrapper_start_ticks,
                        "supervisor_pid": supervisor_pid,
                        "supervisor_start_ticks": supervisor_start_ticks,
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

    def classify_terminal(observed_cancel: int | None) -> tuple[str, str, int]:
        if capture_publication_failed:
            return "internal_fault", "artifact_publication_failure", SETUP_FAILURE
        if errors:
            return "internal_fault", "supervisor_or_capture_failure", SETUP_FAILURE
        if observed_cancel is not None:
            return (
                "cancelled",
                f"signal_{signal.Signals(observed_cancel).name}",
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

    classification, reason_code, wrapper_exit = classify_terminal(cancel_signal)

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
            "process_tree_scope": (
                "linux_nested_subreapers_pidfd_procfs_best_effort"
                if guardian_identity is not None
                else "linux_subreaper_pidfd_procfs_best_effort"
            ),
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
    candidate_data: dict[int, bytes] = {}
    base_key = 0

    def candidate_for(observed_cancel: int | None) -> bytes:
        candidate = dict(metadata)
        candidate_class, candidate_reason, candidate_exit = classify_terminal(
            observed_cancel
        )
        candidate["classification"] = candidate_class
        candidate["reason_code"] = candidate_reason
        candidate["wrapper_exit"] = candidate_exit
        candidate["cancel_signal"] = (
            signal.Signals(observed_cancel).name
            if observed_cancel is not None
            else None
        )
        return canonical_json(candidate)

    candidate_data[base_key] = candidate_for(cancel_signal)
    for signum in watched_signals:
        candidate_data[signum] = candidate_for(cancel_signal or signum)

    metadata_parent, metadata_parent_fd = open_directory_nofollow(
        metadata_path.parent, create=True
    )
    del metadata_parent
    prepared: dict[int, int] = {}
    winner: list[int] = []
    commit_errors: list[BaseException] = []
    try:
        for key, data in candidate_data.items():
            prepared[key] = prepare_atomic_file(metadata_parent_fd, data)
        if test_terminal_ready_path is not None:
            write_atomic_new(test_terminal_ready_path, b"candidates_ready\n")
        if test_terminal_delay_ms:
            time.sleep(test_terminal_delay_ms / 1000)

        def commit_signal(signum: int, _frame: Any) -> None:
            if winner or commit_errors:
                return
            key = signum if signum in prepared else base_key
            try:
                if link_prepared_atomic_file(
                    metadata_parent_fd, prepared[key], metadata_path.name
                ):
                    winner.append(key)
            except BaseException as error:
                commit_errors.append(error)

        for signum in watched_signals:
            signal.signal(signum, commit_signal)
        signal.pthread_sigmask(signal.SIG_SETMASK, previous_signal_mask)
        if not winner and not commit_errors:
            initial_key = cancel_signal or base_key
            if link_prepared_atomic_file(
                metadata_parent_fd, prepared[initial_key], metadata_path.name
            ):
                winner.append(initial_key)
        signal.pthread_sigmask(signal.SIG_BLOCK, watched_signals)
        for signum in watched_signals:
            signal.signal(signum, signal.SIG_IGN)
        signal.pthread_sigmask(signal.SIG_SETMASK, previous_signal_mask)
        if commit_errors:
            raise commit_errors[0]
        if len(winner) != 1:
            raise EvidenceError("metadata atomic publication had no unique winner")
        selected = parse_json(candidate_data[winner[0]], subject="metadata candidate")
        if not isinstance(selected, dict):
            raise EvidenceError("metadata candidate is not an object")
        classification = str(selected["classification"])
        reason_code = str(selected["reason_code"])
        wrapper_exit = int(selected["wrapper_exit"])
    except BaseException as error:
        fallback = {
            "schema": "fln.supervisor/1",
            "classification": "internal_fault",
            "reason_code": "metadata_publication_failure",
            "metadata_path": str(metadata_path),
            "error": f"{type(error).__name__}: {error}",
        }
        sys.stderr.buffer.write(canonical_json(fallback))
        if restore_signal_state:
            for signum, handler in old_handlers.items():
                signal.signal(signum, handler)
            signal.pthread_sigmask(signal.SIG_SETMASK, previous_signal_mask)
        close_process_handles(known_descendants)
        return SETUP_FAILURE
    finally:
        for descriptor in prepared.values():
            os.close(descriptor)
        os.close(metadata_parent_fd)
    if restore_signal_state:
        signal.pthread_sigmask(signal.SIG_BLOCK, watched_signals)
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
            "finalizer-self-test",
            "evidence-manifest-self-test",
        }
        if schema == "fln.check/2"
        else {"e2e"}
    )
    if profile not in allowed_profiles:
        raise EvidenceError(f"{path}: unknown run profile {profile!r}")
    if schema == "fln.check/2" and not isinstance(records[0].get("planted"), str):
        raise EvidenceError(f"{path}: planted-stage binding must be a string")
    binding_free_profiles = {
        "evidence-manifest-self-test",
        "finalizer-self-test",
    }
    if schema == "fln.check/2" and profile not in binding_free_profiles:
        if records[0].get("ubs_inventory") != "ubs-inventory.json":
            raise EvidenceError(f"{path}: quality gate lacks its UBS inventory binding")
        validate_ubs_inventory(
            path.parent / "ubs-inventory.json",
            Path(records[0]["cwd"]) if live_context else None,
        )
    if schema == "fln.e2e/2" or profile not in binding_free_profiles:
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
        elif profile == "finalizer-self-test":
            expected_ids = ["finalizer-probe"]
            actual_ids = [
                str(record.get("stage"))
                for record in exercised
                if record.get("event") == "self_test"
            ]
            if len(actual_ids) != len(exercised):
                raise EvidenceError(
                    f"{path}: finalizer self-test contains foreign events"
                )
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
    if resource_facts.get("process_tree_scope") not in {
        "linux_nested_subreapers_pidfd_procfs_best_effort",
        "linux_subreaper_pidfd_procfs_best_effort",
    }:
        raise EvidenceError(f"{path}:{record_number}: unknown process-tree scope")
    if resource_facts.get("surviving_pids") != []:
        raise EvidenceError(f"{path}:{record_number}: supervisor left live descendants")
    readiness_path = require_within(
        path.parent / str(value["readiness"]), path.parent, label="readiness artifact"
    )
    readiness = read_json_object(readiness_path)
    readiness_keys = {
        "schema",
        "stage_id",
        "wrapper_pid",
        "wrapper_start_ticks",
        "supervisor_pid",
        "supervisor_start_ticks",
        "child_pid",
        "child_pgid",
        "child_start_ticks",
        "monotonic_ns",
        "status",
    }
    if (
        set(readiness) != readiness_keys
        or not isinstance(readiness.get("monotonic_ns"), int)
        or isinstance(readiness.get("monotonic_ns"), bool)
        or readiness.get("monotonic_ns", 0) <= 0
        or readiness.get("schema") != "fln.supervisor-readiness/1"
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
    supervisor_pid = readiness.get("supervisor_pid")
    supervisor_ticks = readiness.get("supervisor_start_ticks")
    if (
        not isinstance(wrapper_pid, int)
        or isinstance(wrapper_pid, bool)
        or wrapper_pid <= 1
        or not isinstance(wrapper_ticks, int)
        or isinstance(wrapper_ticks, bool)
        or wrapper_ticks <= 0
        or not isinstance(supervisor_pid, int)
        or isinstance(supervisor_pid, bool)
        or supervisor_pid <= 1
        or not isinstance(supervisor_ticks, int)
        or isinstance(supervisor_ticks, bool)
        or supervisor_ticks <= 0
        or (
            supervisor_pid == wrapper_pid and supervisor_ticks != wrapper_ticks
        )
    ):
        raise EvidenceError(
            f"{path}:{record_number}: malformed wrapper readiness identity"
        )
    expected_scope = (
        "linux_nested_subreapers_pidfd_procfs_best_effort"
        if supervisor_pid != wrapper_pid
        else "linux_subreaper_pidfd_procfs_best_effort"
    )
    if resource_facts.get("process_tree_scope") != expected_scope:
        raise EvidenceError(
            f"{path}:{record_number}: readiness/process-tree scope mismatch"
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
            or child_pid in {wrapper_pid, supervisor_pid}
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
            or not hmac.compare_digest(
                str(facts["sha256"]), str(facts["retained_sha256"])
            )
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
        if size != facts["retained_bytes"] or not hmac.compare_digest(
            digest, str(facts["retained_sha256"])
        ):
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
        if row["bytes"] != size or not hmac.compare_digest(row["sha256"], digest):
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
    supervisor_pid = readiness.get("supervisor_pid")
    child_pid = readiness.get("child_pid")
    child_pgid = readiness.get("child_pgid")
    if wrapper_pid != expected_wrapper_pid or child_pid != child_pgid:
        raise EvidenceError("emergency kill PID binding mismatch")
    if not all(
        isinstance(value, int) and not isinstance(value, bool) and value > 1
        for value in (wrapper_pid, supervisor_pid, child_pid)
    ):
        raise EvidenceError("emergency kill PIDs are malformed")
    wrapper_facts = proc_stat_facts(wrapper_pid)
    supervisor_facts = proc_stat_facts(supervisor_pid)
    child_facts = proc_stat_facts(child_pid)
    if (
        wrapper_facts is None
        or supervisor_facts is None
        or child_facts is None
        or wrapper_facts[0] == "Z"
        or supervisor_facts[0] == "Z"
        or child_facts[0] == "Z"
        or wrapper_facts[2] != readiness.get("wrapper_start_ticks")
        or supervisor_facts[2] != readiness.get("supervisor_start_ticks")
        or child_facts[2] != readiness.get("child_start_ticks")
        or child_facts[1] != child_pgid
        or os.getpgid(child_pid) != child_pgid
    ):
        raise EvidenceError("emergency kill readiness is stale")
    handles: ProcessHandles = {}
    frozen_scope: set[int] | None = None
    try:
        if not remember_process(wrapper_pid, handles):
            raise EvidenceError("emergency kill could not bind process lifetimes")
        if supervisor_pid != wrapper_pid and not remember_process(
            supervisor_pid, handles, expected_parent_pid=wrapper_pid
        ):
            raise EvidenceError("emergency kill could not bind supervisor lifetime")
        if not remember_process(
            child_pid, handles, expected_parent_pid=supervisor_pid
        ):
            raise EvidenceError("emergency kill could not bind child lifetime")
        if (
            handles[wrapper_pid][0] != wrapper_facts[2]
            or handles[supervisor_pid][0] != supervisor_facts[2]
            or handles[child_pid][0] != child_facts[2]
        ):
            raise EvidenceError("emergency kill process identity changed")

        # Freeze the wrapper-owned subreaper tree before killing it. This catches
        # descendants that created their own sessions and prevents any bound parent
        # from forking across the final scan. Pidfds make every signal lifetime-safe.
        live = live_tree_members(wrapper_pid, handles)
        if (
            wrapper_pid not in live
            or supervisor_pid not in live
            or child_pid not in live
        ):
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
                frozen_scope = set(repeated)
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
    except BaseException:
        if frozen_scope is None:
            # Until a complete fixed point is proven, killing the guardian could
            # orphan an unbound descendant. Resume anything tentatively stopped and
            # leave the outer guardian alive to retain the subreaper boundary.
            for pid, handle in list(handles.items()):
                signal_process_handle(pid, handle, signal.SIGCONT)
        else:
            # Once the whole scope is frozen, finish the authorized teardown with
            # descendants/inner supervisor first and the outer guardian last.
            for pid in sorted(
                frozen_scope, key=lambda value: value == wrapper_pid
            ):
                handle = handles.get(pid)
                if handle is not None:
                    signal_process_handle(pid, handle, signal.SIGKILL)
        raise
    finally:
        close_process_handles(handles)


def kill_bound_process_group(
    pid: int, expected_start_ticks: int, expected_parent_pid: int
) -> None:
    """Freeze and pidfd-kill every member of one exact session process group."""
    if (
        pid <= 1
        or expected_start_ticks <= 0
        or expected_parent_pid <= 1
        or pid == expected_parent_pid
    ):
        raise EvidenceError("bound process-group identity is malformed")
    opened = open_process_handle(pid, expected_parent_pid=expected_parent_pid)
    if opened is None:
        return
    facts = proc_stat_facts(pid)
    if facts is None or facts[2] != expected_start_ticks or opened[0] != expected_start_ticks:
        os.close(opened[1])
        return
    if facts[1] != pid:
        os.close(opened[1])
        raise EvidenceError("bound process is not the expected session leader")
    handles: ProcessHandles = {pid: opened}
    frozen = False
    try:
        deadline = time.monotonic() + PROCESS_GROUP_FREEZE_TIMEOUT_S
        prior_members: set[int] | None = None
        for _attempt in range(PROCESS_GROUP_FREEZE_ATTEMPTS):
            if time.monotonic() >= deadline:
                break
            observed = live_process_group_members(pid)
            for member_pid in observed:
                current = handles.get(member_pid)
                if current is None:
                    current = open_process_handle(member_pid)
                    if current is None:
                        continue
                    member_facts = proc_stat_facts(member_pid)
                    if (
                        member_facts is None
                        or member_facts[0] == "Z"
                        or member_facts[1] != pid
                        or member_facts[2] != current[0]
                    ):
                        os.close(current[1])
                        continue
                    handles[member_pid] = current
                signal_process_handle(member_pid, current, signal.SIGSTOP)
            time.sleep(0.005)
            repeated = live_process_group_members(pid)
            bound_live = {
                member_pid
                for member_pid, member_handle in handles.items()
                if process_handle_alive(member_pid, member_handle)
                and (member_facts := proc_stat_facts(member_pid)) is not None
                and member_facts[1] == pid
            }
            all_stopped = all(
                (member_facts := proc_stat_facts(member_pid)) is not None
                and member_facts[0] in {"T", "t"}
                and member_facts[2] == handles[member_pid][0]
                for member_pid in bound_live
            )
            if repeated == bound_live and repeated == prior_members and all_stopped:
                frozen = True
                break
            prior_members = repeated if repeated == bound_live and all_stopped else None
        if not frozen:
            raise EvidenceError("bound process group did not reach a frozen fixed point")
        for member_pid in sorted(handles, key=lambda value: value == pid):
            signal_process_handle(
                member_pid, handles[member_pid], signal.SIGKILL
            )
        deadline = time.monotonic() + PROCESS_GROUP_KILL_TIMEOUT_S
        for _attempt in range(PROCESS_GROUP_KILL_ATTEMPTS):
            live = {
                member_pid
                for member_pid, member_handle in handles.items()
                if process_handle_alive(member_pid, member_handle)
            }
            if not live and not live_process_group_members(pid):
                return
            for member_pid in live:
                signal_process_handle(
                    member_pid, handles[member_pid], signal.SIGKILL
                )
            if time.monotonic() >= deadline:
                break
            time.sleep(0.005)
        raise EvidenceError("bound process group remained live after pidfd SIGKILL")
    except BaseException:
        # Every signal remains tied to a pidfd-bound lifetime. If the fixed-point
        # proof fails, kill what was proven and report cleanup uncertainty.
        for member_pid, member_handle in handles.items():
            signal_process_handle(member_pid, member_handle, signal.SIGKILL)
        raise
    finally:
        if not frozen:
            for member_pid, member_handle in handles.items():
                signal_process_handle(member_pid, member_handle, signal.SIGKILL)
        close_process_handles(handles)


def signal_bound_process(pid: int, expected_start_ticks: int, signum: int) -> None:
    """Signal one exact Linux process lifetime without numeric-PID reuse risk."""
    if pid <= 1 or expected_start_ticks <= 0:
        raise EvidenceError("bound process identity is malformed")
    handle = open_process_handle(pid)
    if handle is None:
        return
    try:
        if handle[0] != expected_start_ticks:
            return
        signal_process_handle(pid, handle, signum)
    finally:
        os.close(handle[1])


def cleanup_guardian_descendants(worker_pid: int, grace_s: float = 1.0) -> list[int]:
    """Contain descendants adopted after an inner supervisor exits unexpectedly."""
    known: ProcessHandles = {}
    try:
        live = live_tree_members(worker_pid, known)
        if not live:
            time.sleep(0.01)
            live = live_tree_members(worker_pid, known)
        if not live:
            reap_adopted_children()
            return []

        freeze_deadline = time.monotonic() + grace_s
        while time.monotonic() < freeze_deadline:
            for pid in live:
                signal_process_handle(pid, known[pid], signal.SIGSTOP)
            time.sleep(0.01)
            repeated = live_tree_members(worker_pid, known)
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
            signal_process_handle(pid, known[pid], signal.SIGKILL)
        kill_deadline = time.monotonic() + grace_s
        while time.monotonic() < kill_deadline:
            reap_adopted_children()
            live = live_tree_members(worker_pid, known)
            if not live:
                reap_adopted_children()
                return []
            for pid in live:
                signal_process_handle(pid, known[pid], signal.SIGKILL)
            time.sleep(0.01)
        return sorted(live)
    finally:
        close_process_handles(known)


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
    output = require_exact_artifact_path(
        output, art_dir, "manifest.json", label="manifest output"
    )
    digest_output = require_exact_artifact_path(
        digest_output, art_dir, "manifest.digest", label="manifest digest"
    )
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
    entries = artifact_inventory(
        art_dir,
        excluded={
            output,
            digest_output,
            art_dir / "bundle.decision",
            art_dir / "bundle.complete.json",
        },
    )
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
    manifest_path = require_exact_artifact_path(
        manifest_path, art_dir, "manifest.json", label="manifest"
    )
    digest_path = require_exact_artifact_path(
        digest_path, art_dir, "manifest.digest", label="manifest digest"
    )
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
                or not hmac.compare_digest(
                    str(entry.get("sha256")), expected_directory_digest
                )
            ):
                raise EvidenceError(f"manifest directory facts mismatch: {rel}")
        else:
            _data, size, digest = stable_file_facts(path)
            if entry.get("bytes") != size:
                raise EvidenceError(f"manifest byte count mismatch: {rel}")
            if not hmac.compare_digest(str(entry.get("sha256")), digest):
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
        excluded={
            manifest_path,
            digest_path,
            art_dir / "bundle.decision",
            art_dir / "bundle.complete.json",
        },
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


def durably_sync_manifested_bundle(
    art_dir: Path,
    manifest_path: Path,
    digest_path: Path,
    commit_path: Path | None = None,
) -> None:
    """Order every artifact and directory-creation edge before the bundle marker."""
    art_dir = lexical_absolute(art_dir)
    manifest_path = require_exact_artifact_path(
        manifest_path, art_dir, "manifest.json", label="manifest"
    )
    digest_path = require_exact_artifact_path(
        digest_path, art_dir, "manifest.digest", label="manifest digest"
    )
    if commit_path is not None:
        commit_path = require_exact_artifact_path(
            commit_path, art_dir, "bundle.complete.json", label="bundle commit"
        )
    manifest = read_json_object(manifest_path)
    files = [
        require_within(art_dir / entry["path"], art_dir, label="durable artifact")
        for entry in manifest["artifacts"]
        if entry["role"] != "directory"
    ]
    files.extend((manifest_path, digest_path))
    if commit_path is not None:
        files.append(
            require_within(commit_path, art_dir, label="durable bundle commit")
        )
        files.append(
            require_within(
                commit_path.with_name("bundle.decision"),
                art_dir,
                label="durable bundle decision",
            )
        )
    directories = {art_dir}
    for path in files:
        _absolute, descriptor = open_regular_nofollow(path)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
        parent = path.parent
        while parent != art_dir:
            if parent == parent.parent or art_dir not in parent.parents:
                raise EvidenceError(
                    f"durable artifact parent escapes artifact root: {path}"
                )
            directories.add(parent)
            parent = parent.parent
    for entry in manifest["artifacts"]:
        if entry["role"] == "directory":
            directories.add(
                require_within(
                    art_dir / entry["path"], art_dir, label="durable directory"
                )
            )
    # The shells create a fresh per-attempt artifact directory.  Syncing only that
    # directory persists its children but not its own name in the parent.  Include
    # the complete ancestor chain so first-run ART_ROOT creation is durable too.
    ancestor = art_dir.parent
    while True:
        directories.add(ancestor)
        if ancestor == ancestor.parent:
            break
        ancestor = ancestor.parent
    for directory in sorted(
        directories, key=lambda path: len(path.parts), reverse=True
    ):
        _absolute, descriptor = open_directory_nofollow(directory, create=False)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)


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
    restore_signal_state: bool = True,
    test_fail_after_link: bool = False,
) -> dict[str, Any]:
    art_dir = lexical_absolute(art_dir)
    manifest_path = require_exact_artifact_path(
        manifest_path, art_dir, "manifest.json", label="manifest"
    )
    digest_path = require_exact_artifact_path(
        digest_path, art_dir, "manifest.digest", label="manifest digest"
    )
    output = require_exact_artifact_path(
        output, art_dir, "bundle.complete.json", label="bundle commit"
    )
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
    current_root = tree_hash(
        governed_root,
        governed_paths,
        inventory_path=inventory_path,
        vendor_path=vendor_path,
    )
    if current_root != expected_root or current_root != manifest.get("final_root"):
        raise EvidenceError("governed inputs changed before bundle commit")
    # The governed hash can be long. Revalidate every artifact after it, then prove
    # both sides stable across another full pass before publishing the marker.
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
    repeated_root = tree_hash(
        governed_root,
        governed_paths,
        inventory_path=inventory_path,
        vendor_path=vendor_path,
    )
    if repeated_root != current_root:
        raise EvidenceError("governed inputs changed during prospective validation")
    durably_sync_manifested_bundle(art_dir, manifest_path, digest_path)
    validate_manifest(art_dir, manifest_path, digest_path)
    durable_bindings = (
        sha256_file(run_log),
        sha256_file(manifest_path),
        sha256_file(digest_path),
    )
    if durable_bindings != initial_bindings:
        raise EvidenceError("bundle bindings changed during durable synchronization")
    final_root = tree_hash(
        governed_root,
        governed_paths,
        inventory_path=inventory_path,
        vendor_path=vendor_path,
    )
    if final_root != current_root:
        raise EvidenceError("governed inputs changed before durable bundle commit")
    validate_manifest(art_dir, manifest_path, digest_path)
    final_bindings = (
        sha256_file(run_log),
        sha256_file(manifest_path),
        sha256_file(digest_path),
    )
    if final_bindings != initial_bindings:
        raise EvidenceError("bundle bindings changed before durable bundle commit")
    validate_marker_bindings(
        marker,
        read_json_object(manifest_path),
        load_ndjson(run_log)[-1],
        final_bindings,
    )
    # This durable, exclusive publication is deliberately the final operation.
    write_signal_committed_atomic_new(
        output,
        marker_data,
        decision_path=output.with_name("bundle.decision"),
        restore_signal_state=restore_signal_state,
        test_fail_after_link=test_fail_after_link,
    )
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
            or not hmac.compare_digest(str(value.get("sha256")), expected_digest)
        ):
            raise EvidenceError(f"bundle marker has invalid {key} binding")


def validate_bundle(
    art_dir: Path,
    manifest_path: Path,
    digest_path: Path,
    commit_path: Path,
) -> dict[str, Any]:
    art_dir = lexical_absolute(art_dir)
    manifest_path = require_exact_artifact_path(
        manifest_path, art_dir, "manifest.json", label="manifest"
    )
    digest_path = require_exact_artifact_path(
        digest_path, art_dir, "manifest.digest", label="manifest digest"
    )
    commit_path = require_exact_artifact_path(
        commit_path, art_dir, "bundle.complete.json", label="bundle commit"
    )
    run_log = art_dir / "run.ndjson"
    validate_manifest(art_dir, manifest_path, digest_path, live_context=False)
    manifest = read_json_object(manifest_path)
    terminal = load_ndjson(run_log)[-1]
    bindings = (
        sha256_file(run_log),
        sha256_file(manifest_path),
        sha256_file(digest_path),
    )
    decision_path = art_dir / "bundle.decision"
    decision_marker = read_json_object(decision_path)
    validate_marker_bindings(decision_marker, manifest, terminal, bindings)
    _parent, parent_fd = open_directory_nofollow(art_dir, create=False)
    try:
        try:
            os.link(
                decision_path.name,
                commit_path.name,
                src_dir_fd=parent_fd,
                dst_dir_fd=parent_fd,
                follow_symlinks=False,
            )
        except FileExistsError:
            pass
        os.fsync(parent_fd)
    finally:
        os.close(parent_fd)
    decision_data, _size, _digest = stable_file_facts(decision_path)
    commit_data, _size, _digest = stable_file_facts(commit_path)
    if not hmac.compare_digest(decision_data, commit_data):
        raise EvidenceError("bundle marker does not match its commit decision")
    marker = read_json_object(commit_path)
    validate_marker_bindings(
        marker,
        manifest,
        terminal,
        bindings,
    )
    # A publisher can die after the commit decision wins but before the canonical
    # marker link/fsync. A validator recovers that marker, durably orders the whole
    # bundle, and revalidates the adopted bytes before reporting commitment.
    durably_sync_manifested_bundle(
        art_dir, manifest_path, digest_path, commit_path=commit_path
    )
    validate_manifest(art_dir, manifest_path, digest_path, live_context=False)
    manifest = read_json_object(manifest_path)
    decision_marker = read_json_object(decision_path)
    marker = read_json_object(commit_path)
    terminal = load_ndjson(run_log)[-1]
    bindings = (
        sha256_file(run_log),
        sha256_file(manifest_path),
        sha256_file(digest_path),
    )
    validate_marker_bindings(decision_marker, manifest, terminal, bindings)
    validate_marker_bindings(
        marker,
        manifest,
        terminal,
        bindings,
    )
    decision_data, _size, _digest = stable_file_facts(decision_path)
    commit_data, _size, _digest = stable_file_facts(commit_path)
    if not hmac.compare_digest(decision_data, commit_data):
        raise EvidenceError("durable bundle marker changed from its commit decision")
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


def run_supervised_from_args(
    args: argparse.Namespace,
    guardian_identity: tuple[int, int] | None = None,
    initial_signal_mask: set[signal.Signals] | None = None,
) -> int:
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
        restore_signal_state=False,
        test_terminal_delay_ms=args.test_terminal_delay_ms,
        test_terminal_ready_path=(
            Path(args.test_terminal_ready) if args.test_terminal_ready else None
        ),
        guardian_identity=guardian_identity,
        initial_signal_mask=initial_signal_mask,
    )


def cmd_run(args: argparse.Namespace) -> int:
    """Keep an outer subreaper alive if the inner supervisor is hard-killed."""
    enable_child_subreaper()
    guardian_facts = proc_stat_facts(os.getpid())
    if guardian_facts is None or guardian_facts[0] == "Z":
        raise EvidenceError("cannot bind guardian process identity")
    guardian_identity = (os.getpid(), guardian_facts[2])
    preflight_handle = open_process_handle(os.getpid())
    if preflight_handle is None:
        raise EvidenceError("cannot preflight guardian pidfd support")
    os.close(preflight_handle[1])
    watched = (signal.SIGHUP, signal.SIGINT, signal.SIGTERM)
    previous_mask = signal.pthread_sigmask(signal.SIG_BLOCK, watched)
    if bool(args.launch_ready) != bool(args.launch_release):
        raise EvidenceError("guardian launch gate requires both control paths")
    if args.launch_ready:
        artifact_root = lexical_absolute(Path(args.artifact_root))
        launch_ready = require_within(
            Path(args.launch_ready), artifact_root, label="guardian launch readiness"
        )
        launch_release = require_within(
            Path(args.launch_release), artifact_root, label="guardian launch release"
        )
        launch_identity = {
            "schema": "fln.guardian-launch/1",
            "status": "awaiting_release",
            "stage_id": args.stage_id,
            "guardian_pid": guardian_identity[0],
            "guardian_start_ticks": guardian_identity[1],
        }
        write_atomic_new(launch_ready, canonical_json(launch_identity))
        release_deadline = time.monotonic() + 30.0
        while True:
            try:
                release = read_json_object(launch_release)
            except FileNotFoundError:
                if time.monotonic() >= release_deadline:
                    raise EvidenceError("guardian launch release timed out")
                time.sleep(0.01)
                continue
            expected_release = dict(launch_identity)
            expected_release["status"] = "released"
            if release != expected_release:
                raise EvidenceError("guardian launch release identity mismatch")
            break
    worker_pid = os.fork()
    if worker_pid == 0:
        try:
            try:
                worker_exit = run_supervised_from_args(
                    args,
                    guardian_identity,
                    initial_signal_mask=previous_mask,
                )
            except BaseException as error:
                sys.stderr.write(
                    f"evidence worker: {type(error).__name__}: {error}\n"
                )
                worker_exit = SETUP_FAILURE
            os._exit(worker_exit)
        except BaseException:
            os._exit(SETUP_FAILURE)

    worker_handle: tuple[int, int] | None = None
    waited_status: int | None = None
    waited_pid = 0
    setup_error: BaseException | None = None
    cleanup_errors: list[str] = []
    survivors: list[int] = []
    try:
        if args.test_fail_guardian_pidfd_open:
            if args.test_guardian_child_ready:
                readiness = require_within(
                    Path(args.test_guardian_child_ready),
                    Path(args.artifact_root),
                    label="guardian fault child readiness",
                )
                deadline = time.monotonic() + 15.0
                previous_payload: bytes | None = None
                stable_reads = 0
                while time.monotonic() < deadline:
                    try:
                        payload, _size, _digest = stable_file_facts(
                            readiness, max_bytes=128
                        )
                        values = tuple(
                            int(value)
                            for value in payload.decode("ascii").splitlines()
                        )
                        if (
                            len(values) == 2
                            and len(set(values)) == 2
                            and all(value > 1 for value in values)
                        ):
                            stable_reads = (
                                stable_reads + 1 if payload == previous_payload else 1
                            )
                            previous_payload = payload
                            if stable_reads >= 2:
                                break
                        else:
                            stable_reads = 0
                            previous_payload = None
                    except (EvidenceError, FileNotFoundError, UnicodeError, ValueError):
                        stable_reads = 0
                        previous_payload = None
                    time.sleep(0.01)
                else:
                    raise EvidenceError(
                        "guardian fault child PID handshake did not stabilize"
                    )
            else:
                readiness = Path(args.readiness)
                deadline = time.monotonic() + 15.0
                while not readiness.exists() and time.monotonic() < deadline:
                    time.sleep(0.01)
                if not readiness.exists():
                    raise EvidenceError("guardian fault readiness timed out")
            raise OSError(errno.EMFILE, "injected post-fork pidfd_open failure")
        worker_handle = open_process_handle(worker_pid)
        if worker_handle is None:
            waited_pid, status = os.waitpid(worker_pid, os.WNOHANG)
            if waited_pid == worker_pid:
                waited_status = status
            else:
                raise EvidenceError("cannot bind live inner supervisor")

        def forward_signal(signum: int, _frame: Any) -> None:
            if worker_handle is not None:
                signal_process_handle(worker_pid, worker_handle, signum)

        for signum in watched:
            signal.signal(signum, forward_signal)
        signal.pthread_sigmask(signal.SIG_SETMASK, previous_mask)
        while waited_status is None:
            try:
                waited_pid, waited_status = os.waitpid(worker_pid, 0)
            except InterruptedError:
                continue
            if waited_pid != worker_pid:
                raise EvidenceError("guardian reaped an unexpected process")
    except BaseException as error:
        setup_error = error
        try:
            signal.pthread_sigmask(signal.SIG_BLOCK, watched)
        except BaseException as cleanup_error:
            cleanup_errors.append(f"cannot block cleanup signals: {cleanup_error}")
        for signum in watched:
            try:
                signal.signal(signum, signal.SIG_IGN)
            except BaseException as cleanup_error:
                cleanup_errors.append(
                    f"cannot ignore cleanup signal {signum}: {cleanup_error}"
                )
        if waited_status is None:
            signalled = False
            if worker_handle is not None:
                try:
                    signalled = signal_process_handle(
                        worker_pid, worker_handle, signal.SIGKILL
                    )
                except BaseException as cleanup_error:
                    cleanup_errors.append(
                        f"cannot signal failed inner supervisor by pidfd: {cleanup_error}"
                    )
            if not signalled:
                try:
                    # W is still our unreaped direct child, so this numeric PID
                    # cannot be recycled before the following waitpid.
                    os.kill(worker_pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                except BaseException as cleanup_error:
                    cleanup_errors.append(
                        f"cannot signal failed inner supervisor by PID: {cleanup_error}"
                    )
            while True:
                try:
                    waited_pid, waited_status = os.waitpid(worker_pid, 0)
                    break
                except InterruptedError:
                    continue
                except ChildProcessError as cleanup_error:
                    cleanup_errors.append(
                        f"cannot reap failed inner supervisor: {cleanup_error}"
                    )
                    break
                except BaseException as cleanup_error:
                    cleanup_errors.append(
                        f"failed while reaping inner supervisor: {cleanup_error}"
                    )
                    break
            if waited_pid not in {0, worker_pid}:
                setup_error = EvidenceError(
                    "guardian lost the failed inner supervisor"
                )
    finally:
        if worker_handle is not None:
            try:
                os.close(worker_handle[1])
            except BaseException as cleanup_error:
                cleanup_errors.append(
                    f"cannot close inner supervisor pidfd: {cleanup_error}"
                )
        try:
            survivors = cleanup_guardian_descendants(worker_pid)
        except BaseException as cleanup_error:
            cleanup_errors.append(
                f"cannot prove guardian descendant cleanup: {cleanup_error}"
            )
    if survivors:
        raise EvidenceError(
            f"guardian containment remained unproven for PIDs {survivors}"
        )
    if cleanup_errors:
        raise EvidenceError("; ".join(cleanup_errors))
    if setup_error is not None:
        raise EvidenceError(
            f"guardian setup failed after fork: {type(setup_error).__name__}: {setup_error}"
        ) from setup_error
    if waited_status is None:
        raise EvidenceError("guardian lost inner supervisor status")
    worker_exit = os.waitstatus_to_exitcode(waited_status)
    if worker_exit in {PASS, FAIL, SETUP_FAILURE, INCONCLUSIVE, CANCELLED}:
        return worker_exit
    raise EvidenceError(f"inner supervisor died unexpectedly with status {worker_exit}")


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


def cmd_stopped_exec(args: argparse.Namespace) -> int:
    command = list(args.command)
    if command and command[0] == "--":
        command = command[1:]
    if not command:
        raise EvidenceError("stopped exec requires a command")
    arm_parent_death_kill(args.expected_parent_pid)
    os.kill(os.getpid(), signal.SIGSTOP)
    os.execvp(command[0], command)
    raise EvidenceError("stopped exec unexpectedly returned")


def cmd_emergency_kill(args: argparse.Namespace) -> int:
    emergency_kill(
        Path(args.readiness), args.expected_wrapper_pid, args.expected_stage_id
    )
    return PASS


def cmd_process_start_ticks(args: argparse.Namespace) -> int:
    if args.wait_ms < 0 or args.wait_ms > 30_000:
        raise EvidenceError("process identity wait must be between 0 and 30000 ms")
    if args.pid == os.getpid():
        raise EvidenceError("process identity target cannot be the binder itself")
    deadline = time.monotonic() + args.wait_ms / 1000
    handle = bind_direct_child_until(
        args.pid, args.expected_parent_pid, deadline
    )
    try:
        while True:
            facts = proc_stat_facts(args.pid)
            if (
                facts is None
                or facts[0] == "Z"
                or facts[2] != handle[0]
                or args.pid not in proc_children(args.expected_parent_pid)
            ):
                raise EvidenceError("process disappeared before session binding")
            session_ready = not args.session_leader or facts[1] == args.pid
            stopped_ready = not args.stopped or facts[0] in {"T", "t"}
            if session_ready and stopped_ready:
                print(handle[0])
                return PASS
            if time.monotonic() >= deadline:
                signal_process_handle(args.pid, handle, signal.SIGKILL)
                raise EvidenceError("process did not become a session leader in time")
            time.sleep(0.005)
    finally:
        os.close(handle[1])


def cmd_release_process_launch(args: argparse.Namespace) -> int:
    if args.wait_ms < 0 or args.wait_ms > 30_000:
        raise EvidenceError("guardian launch wait must be between 0 and 30000 ms")
    artifact_root = lexical_absolute(Path(args.artifact_root))
    ready_path = require_within(
        Path(args.ready), artifact_root, label="guardian launch readiness"
    )
    output_path = require_within(
        Path(args.output), artifact_root, label="guardian launch release"
    )
    deadline = time.monotonic() + args.wait_ms / 1000
    while True:
        try:
            ready = read_json_object(ready_path)
            break
        except FileNotFoundError:
            if time.monotonic() >= deadline:
                raise EvidenceError("guardian launch readiness timed out")
            time.sleep(0.005)
    expected = {
        "schema": "fln.guardian-launch/1",
        "status": "awaiting_release",
        "stage_id": args.stage_id,
        "guardian_pid": args.pid,
        "guardian_start_ticks": args.expected_start_ticks,
    }
    if ready != expected:
        raise EvidenceError("guardian launch readiness identity mismatch")
    released = dict(expected)
    released["status"] = "released"
    released_data = canonical_json(released)
    try:
        observed, _size, _digest = stable_file_facts(output_path)
    except FileNotFoundError:
        pass
    else:
        if not hmac.compare_digest(observed, released_data):
            raise EvidenceError("guardian launch release already has wrong bytes")
        return PASS
    if args.pid == os.getpid():
        raise EvidenceError("guardian launch target cannot be the releaser itself")
    handle = open_process_handle(
        args.pid, expected_parent_pid=args.expected_parent_pid
    )
    if handle is None or handle[0] != args.expected_start_ticks:
        if handle is not None:
            os.close(handle[1])
        raise EvidenceError("guardian changed before launch release")
    try:
        try:
            write_atomic_new(output_path, released_data)
        except BaseException:
            try:
                observed, _size, _digest = stable_file_facts(output_path)
            except BaseException:
                raise
            if not hmac.compare_digest(observed, released_data):
                raise
    finally:
        os.close(handle[1])
    return PASS


def cmd_kill_bound_group(args: argparse.Namespace) -> int:
    kill_bound_process_group(
        args.pid, args.expected_start_ticks, args.expected_parent_pid
    )
    return PASS


def cmd_kill_direct_child(args: argparse.Namespace) -> int:
    """Kill one currently direct child through a pidfd, never a numeric PID."""
    if (
        args.pid <= 1
        or args.expected_parent_pid <= 1
        or args.pid in {os.getpid(), args.expected_parent_pid}
        or args.wait_ms < 0
        or args.wait_ms > 5000
    ):
        raise EvidenceError("direct-child cleanup identity is malformed")
    handle = open_process_handle(
        args.pid, expected_parent_pid=args.expected_parent_pid
    )
    if handle is None:
        return PASS
    try:
        if not signal_process_handle(args.pid, handle, signal.SIGKILL):
            return PASS
        deadline = time.monotonic() + args.wait_ms / 1000
        while process_handle_alive(args.pid, handle):
            if time.monotonic() >= deadline:
                raise EvidenceError("direct child remained live after pidfd SIGKILL")
            time.sleep(0.005)
    finally:
        os.close(handle[1])
    return PASS


def cmd_signal_bound_process(args: argparse.Namespace) -> int:
    signum = {
        "HUP": signal.SIGHUP,
        "INT": signal.SIGINT,
        "TERM": signal.SIGTERM,
    }[args.signal]
    signal_bound_process(args.pid, args.expected_start_ticks, signum)
    return PASS


def cmd_resume_bound_process(args: argparse.Namespace) -> int:
    if args.pid == os.getpid():
        raise EvidenceError("resume target cannot be the helper itself")
    handle = open_process_handle(
        args.pid, expected_parent_pid=args.expected_parent_pid
    )
    if handle is None or handle[0] != args.expected_start_ticks:
        if handle is not None:
            os.close(handle[1])
        raise EvidenceError("stopped process changed before resume")
    try:
        facts = proc_stat_facts(args.pid)
        if (
            facts is None
            or facts[0] not in {"T", "t"}
            or facts[2] != args.expected_start_ticks
        ):
            raise EvidenceError("process was not stopped at resume linearization")
        if not signal_process_handle(args.pid, handle, signal.SIGCONT):
            raise EvidenceError("stopped process disappeared before resume")
    finally:
        os.close(handle[1])
    return PASS


def cmd_assert_process_group_empty(args: argparse.Namespace) -> int:
    if args.pgid <= 1 or args.wait_ms < 0 or args.wait_ms > 30_000:
        raise EvidenceError("process-group emptiness arguments are malformed")
    deadline = time.monotonic() + args.wait_ms / 1000
    while True:
        live = live_process_group_members(args.pgid)
        if not live:
            return PASS
        if time.monotonic() >= deadline:
            raise EvidenceError(
                f"process group {args.pgid} retained live members {sorted(live)}"
            )
        time.sleep(0.01)


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
        restore_signal_state=False,
        test_fail_after_link=args.test_fail_after_link,
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
        timeout: int = 30_000,
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

    def run_shell_finalizer_probe(
        point: str,
        signal_number: int,
        expected_exit: int,
        *,
        expect_committed_bundle: bool,
    ) -> dict[str, Any]:
        repo = Path(__file__).resolve().parent.parent
        check_script = repo / "scripts" / "check.sh"
        probe_root = art_dir / f"shell_finalizer_{point}"
        control_root = Path(f"{probe_root}.control")
        require(
            not probe_root.exists()
            and not probe_root.is_symlink()
            and not control_root.exists()
            and not control_root.is_symlink(),
            f"finalizer probe paths already exist: {point}",
        )
        probe_environment = {
            key: value
            for key, value in os.environ.items()
            if not key.startswith("FLN_CHECK_")
            and not key.startswith("FLN_FINALIZER_")
        }
        probe_environment.update(
            {
                "FLN_CHECK_ART_DIR": str(probe_root),
                "FLN_FINALIZER_TEST_POINT": point,
            }
        )
        child = subprocess.Popen(
            ["bash", str(check_script), "--finalizer-probe"],
            cwd=repo,
            env=probe_environment,
            start_new_session=True,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        child_handle: tuple[int, int] | None = None
        finalizer_handle: tuple[int, int] | None = None
        finalizer_pid = 0
        try:
            deadline = time.monotonic() + 5.0
            while time.monotonic() < deadline:
                child_handle = open_process_handle(
                    child.pid, expected_parent_pid=os.getpid()
                )
                child_facts = proc_stat_facts(child.pid)
                if (
                    child_handle is not None
                    and child_facts is not None
                    and child_facts[1] == child.pid
                    and child_facts[2] == child_handle[0]
                ):
                    break
                if child_handle is not None:
                    os.close(child_handle[1])
                    child_handle = None
                time.sleep(0.005)
            else:
                raise EvidenceError(f"finalizer probe shell was not bindable: {point}")

            ready_path = control_root / "ready"
            ready_timeout_s = 180.0 if point == "post_decision" else 60.0
            deadline = time.monotonic() + ready_timeout_s
            ready_values: tuple[int, int] | None = None
            while time.monotonic() < deadline:
                if child.poll() is not None:
                    raise EvidenceError(
                        f"finalizer probe exited before readiness: {point}={child.returncode}"
                    )
                try:
                    payload, _size, _digest = stable_file_facts(
                        ready_path, max_bytes=128
                    )
                    values = tuple(
                        int(value) for value in payload.decode("ascii").split()
                    )
                    if len(values) == 2:
                        ready_values = (values[0], values[1])
                        break
                except (EvidenceError, FileNotFoundError, UnicodeError, ValueError):
                    pass
                time.sleep(0.005)
            if ready_values is None:
                raise EvidenceError(f"finalizer probe readiness timed out: {point}")
            finalizer_pid, finalizer_ticks = ready_values
            if point == "post_decision":
                require(
                    ready_values == (0, 0),
                    "post-decision probe unexpectedly retained an active finalizer",
                )
            else:
                require(finalizer_pid > 1, f"invalid finalizer probe PID: {point}")
                deadline = time.monotonic() + 5.0
                while time.monotonic() < deadline:
                    finalizer_handle = open_process_handle(
                        finalizer_pid, expected_parent_pid=child.pid
                    )
                    finalizer_facts = proc_stat_facts(finalizer_pid)
                    if (
                        finalizer_handle is not None
                        and finalizer_facts is not None
                        and finalizer_facts[1] == finalizer_pid
                        and finalizer_facts[2] == finalizer_handle[0]
                        and (
                            (
                                point == "spawn_bind"
                                and finalizer_ticks == 0
                                and finalizer_facts[0] in {"T", "t"}
                            )
                            or (
                                point != "spawn_bind"
                                and finalizer_ticks > 0
                                and finalizer_handle[0] == finalizer_ticks
                                and finalizer_facts[0] not in {"T", "t", "Z"}
                            )
                        )
                    ):
                        break
                    if finalizer_handle is not None:
                        os.close(finalizer_handle[1])
                        finalizer_handle = None
                    time.sleep(0.005)
                else:
                    raise EvidenceError(
                        f"finalizer probe child was not precisely bound: {point}"
                    )

            require(
                signal_process_handle(child.pid, child_handle, signal_number),
                f"finalizer probe shell disappeared before signal: {point}",
            )
            if point == "post_decision":
                ack_path = control_root / "signal-ack"
                deadline = time.monotonic() + 60.0
                while time.monotonic() < deadline:
                    try:
                        ack, _size, _digest = stable_file_facts(
                            ack_path, max_bytes=32
                        )
                    except (EvidenceError, FileNotFoundError):
                        time.sleep(0.005)
                        continue
                    require(
                        hmac.compare_digest(
                            ack.decode("ascii").strip(),
                            signal.Signals(signal_number).name.removeprefix("SIG"),
                        ),
                        "post-decision probe acknowledged the wrong signal",
                    )
                    break
                else:
                    raise EvidenceError("post-decision signal was not acknowledged")
                write_new(control_root / "release", b"release\n")

            communicate_timeout_s = 180 if point == "post_decision" else 120
            _stdout, stderr = child.communicate(timeout=communicate_timeout_s)
            require(
                child.returncode == expected_exit,
                f"finalizer probe {point} exited {child.returncode}: {stderr[-1000:]!r}",
            )
            if not expect_committed_bundle:
                decision, _size, _digest = stable_file_facts(
                    probe_root / "bundle.decision", max_bytes=1
                )
                require(
                    decision == b"",
                    f"pre-decision finalizer probe crossed its decision: {point}",
                )
            if point in {"spawn_bind", "active_wait"}:
                require(
                    b"CANCELLED: signal_" in stderr,
                    f"finalizer cancellation lacked its terminal reason: {point}",
                )
            if point == "helper_failure":
                require(
                    b"process-tree cleanup was not proven" in stderr,
                    "helper-failure probe did not exercise cleanup uncertainty",
                )
            if finalizer_handle is not None:
                deadline = time.monotonic() + 5.0
                while True:
                    reap_adopted_children()
                    finalizer_facts = proc_stat_facts(finalizer_pid)
                    if (
                        finalizer_facts is None
                        or finalizer_facts[2] != finalizer_handle[0]
                    ):
                        break
                    if time.monotonic() >= deadline:
                        break
                    time.sleep(0.005)
                require(
                    (finalizer_facts := proc_stat_facts(finalizer_pid)) is None
                    or finalizer_facts[2] != finalizer_handle[0],
                    f"finalizer probe left its bound lifetime unreaped: {point}",
                )
            commit_path = probe_root / "bundle.complete.json"
            if expect_committed_bundle:
                validate_run(
                    probe_root / "run.ndjson",
                    "fln.check/2",
                    "pass",
                    live_context=False,
                )
                validate_bundle(
                    probe_root,
                    probe_root / "manifest.json",
                    probe_root / "manifest.digest",
                    commit_path,
                )
            else:
                require(
                    not commit_path.exists(),
                    f"pre-decision finalizer probe committed a bundle: {point}",
                )
        finally:
            if child.poll() is None:
                if child_handle is not None:
                    signal_process_handle(child.pid, child_handle, signal.SIGKILL)
                else:
                    child.kill()
                child.communicate(timeout=10)
            if finalizer_handle is not None:
                try:
                    if process_handle_alive(finalizer_pid, finalizer_handle):
                        signal_process_handle(
                            finalizer_pid, finalizer_handle, signal.SIGKILL
                        )
                finally:
                    os.close(finalizer_handle[1])
            if child_handle is not None:
                os.close(child_handle[1])
            reap_adopted_children()
        return {
            "case": f"shell_finalizer_{point}",
            "ok": True,
            "signal": signal.Signals(signal_number).name,
            "process_exit": expected_exit,
            "artifact": str(probe_root),
        }

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
        timeout=30_000,
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
        timeout=5000,
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
            "30000",
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
    wait_deadline = time.monotonic() + 15
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
    _wrapper_out, wrapper_err = wrapper.communicate(timeout=30)
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

    for terminal_signal in (signal.SIGHUP, signal.SIGINT, signal.SIGTERM):
        signal_name = signal.Signals(terminal_signal).name
        terminal_root = case_dir(f"terminal_commit_{signal_name.lower()}")
        child_done = terminal_root / "child.done"
        terminal_ready = terminal_root / "terminal.ready"
        terminal_wrapper = subprocess.Popen(
            [
                sys.executable,
                str(Path(__file__).resolve()),
                "run",
                "--cwd",
                str(art_dir),
                "--metadata",
                str(terminal_root / "stage.meta.json"),
                "--stdout",
                str(terminal_root / "stage.out"),
                "--stderr",
                str(terminal_root / "stage.err"),
                "--readiness",
                str(terminal_root / "stage.ready.json"),
                "--artifact-root",
                str(art_dir),
                "--capture-bytes",
                "4096",
                "--output-budget-bytes",
                "65536",
                "--timeout-ms",
                "30000",
                "--grace-ms",
                "500",
                "--stage-id",
                f"terminal_commit_{signal_name.lower()}",
                "--test-terminal-delay-ms",
                "500",
                "--test-terminal-ready",
                str(terminal_ready),
                "--",
                sys.executable,
                "-c",
                f"from pathlib import Path; Path({str(child_done)!r}).write_text('done')",
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        signal_deadline = time.monotonic() + 15
        while (
            not terminal_ready.exists()
            and terminal_wrapper.poll() is None
            and time.monotonic() < signal_deadline
        ):
            time.sleep(0.01)
        require(
            terminal_ready.exists(),
            f"{signal_name} terminal candidates were not prepared",
        )
        terminal_wrapper.send_signal(terminal_signal)
        _terminal_out, terminal_err = terminal_wrapper.communicate(timeout=30)
        require(
            terminal_wrapper.returncode == CANCELLED,
            f"{signal_name} terminal wrapper exit {terminal_wrapper.returncode}: {terminal_err!r}",
        )
        terminal_meta = read_json_object(terminal_root / "stage.meta.json")
        require(
            terminal_meta["classification"] == "cancelled"
            and hmac.compare_digest(
                str(terminal_meta["cancel_signal"]), signal_name
            ),
            f"{signal_name} did not win terminal metadata publication",
        )
        cases.append(
            {
                "case": f"terminal_commit_{signal_name.lower()}",
                "ok": True,
                "metadata": str(terminal_root / "stage.meta.json"),
            }
        )

    emergency_root = case_dir("emergency_kill_detached")
    emergency_pid_file = emergency_root / "pids.txt"
    emergency_program = (
        "import os,pathlib,subprocess,sys,time;"
        "code='import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(60)';"
        "p=subprocess.Popen([sys.executable,'-c',code],start_new_session=True);"
        f"pathlib.Path({str(emergency_pid_file)!r}).write_text(str(os.getpid())+'\\n'+str(p.pid)+'\\n');"
        "time.sleep(60)"
    )
    emergency_wrapper = subprocess.Popen(
        [
            sys.executable,
            str(Path(__file__).resolve()),
            "run",
            "--cwd",
            str(art_dir),
            "--metadata",
            str(emergency_root / "stage.meta.json"),
            "--stdout",
            str(emergency_root / "stage.out"),
            "--stderr",
            str(emergency_root / "stage.err"),
            "--readiness",
            str(emergency_root / "stage.ready.json"),
            "--artifact-root",
            str(art_dir),
            "--capture-bytes",
            "4096",
            "--output-budget-bytes",
            "65536",
            "--timeout-ms",
            "30000",
            "--grace-ms",
            "500",
            "--stage-id",
            "emergency_kill_detached",
            "--",
            sys.executable,
            "-c",
            emergency_program,
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    emergency_deadline = time.monotonic() + 15
    while (
        not (
            emergency_pid_file.exists()
            and (emergency_root / "stage.ready.json").exists()
        )
        and emergency_wrapper.poll() is None
        and time.monotonic() < emergency_deadline
    ):
        time.sleep(0.01)
    require(emergency_pid_file.exists(), "emergency-kill child did not publish PIDs")
    os.kill(emergency_wrapper.pid, signal.SIGSTOP)
    emergency_kill(
        emergency_root / "stage.ready.json",
        emergency_wrapper.pid,
        "emergency_kill_detached",
    )
    _emergency_out, emergency_err = emergency_wrapper.communicate(timeout=30)
    require(
        emergency_wrapper.returncode == -signal.SIGKILL,
        f"emergency wrapper exit {emergency_wrapper.returncode}: {emergency_err!r}",
    )
    emergency_pids = [
        int(value)
        for value in emergency_pid_file.read_text(encoding="utf-8").splitlines()
    ]
    time.sleep(0.1)
    require(
        not any(process_alive(pid) for pid in emergency_pids),
        "emergency kill left a detached descendant",
    )
    cases.append(
        {
            "case": "emergency_kill_detached",
            "ok": True,
            "pids": emergency_pids,
        }
    )

    forged_root = case_dir("emergency_kill_rejects_unrelated")
    forged_wrapper = subprocess.Popen(
        [sys.executable, "-c", "import time; time.sleep(60)"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    unrelated = subprocess.Popen(
        [sys.executable, "-c", "import time; time.sleep(60)"],
        start_new_session=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    forged_error: EvidenceError | None = None
    forged_wrapper_survived = False
    unrelated_survived = False
    try:
        forged_wrapper_facts = proc_stat_facts(forged_wrapper.pid)
        unrelated_facts = proc_stat_facts(unrelated.pid)
        require(
            forged_wrapper_facts is not None and unrelated_facts is not None,
            "forged-readiness processes disappeared during setup",
        )
        forged_readiness = forged_root / "stage.ready.json"
        write_new(
            forged_readiness,
            canonical_json(
                {
                    "schema": "fln.supervisor-readiness/1",
                    "status": "ready",
                    "stage_id": "emergency_kill_rejects_unrelated",
                    "wrapper_pid": forged_wrapper.pid,
                    "wrapper_start_ticks": forged_wrapper_facts[2],
                    "supervisor_pid": forged_wrapper.pid,
                    "supervisor_start_ticks": forged_wrapper_facts[2],
                    "child_pid": unrelated.pid,
                    "child_pgid": unrelated.pid,
                    "child_start_ticks": unrelated_facts[2],
                }
            ),
        )
        try:
            emergency_kill(
                forged_readiness,
                forged_wrapper.pid,
                "emergency_kill_rejects_unrelated",
            )
        except EvidenceError as error:
            forged_error = error
        time.sleep(0.05)
        forged_wrapper_survived = process_alive(forged_wrapper.pid)
        unrelated_survived = process_alive(unrelated.pid)
    finally:
        if forged_wrapper.poll() is None:
            forged_wrapper.kill()
        forged_wrapper.communicate(timeout=30)
        forged_wrapper.wait(timeout=0)
        if unrelated.poll() is None:
            unrelated.kill()
        unrelated.communicate(timeout=30)
        unrelated.wait(timeout=0)
    require(forged_error is not None, "forged readiness was accepted")
    require(
        forged_wrapper_survived,
        "unproven emergency cleanup killed the outer guardian",
    )
    require(unrelated_survived, "forged readiness killed an unrelated process")
    cases.append(
        {
            "case": "emergency_kill_rejects_unrelated",
            "ok": True,
            "error": str(forged_error),
        }
    )

    guardian_root = case_dir("guardian_contains_wrapper_death")
    guardian_pid_file = guardian_root / "pids.txt"
    guardian_program = (
        "import os,pathlib,signal,subprocess,sys,time;"
        "p=subprocess.Popen([sys.executable,'-c','import time;time.sleep(60)'],"
        "start_new_session=True);"
        f"pathlib.Path({str(guardian_pid_file)!r}).write_text(str(os.getpid())+'\\n'+str(p.pid)+'\\n');"
        "os.kill(os.getppid(),signal.SIGKILL);time.sleep(60)"
    )
    guardian_wrapper = subprocess.Popen(
        [
            sys.executable,
            str(Path(__file__).resolve()),
            "run",
            "--cwd",
            str(art_dir),
            "--metadata",
            str(guardian_root / "stage.meta.json"),
            "--stdout",
            str(guardian_root / "stage.out"),
            "--stderr",
            str(guardian_root / "stage.err"),
            "--readiness",
            str(guardian_root / "stage.ready.json"),
            "--artifact-root",
            str(art_dir),
            "--capture-bytes",
            "4096",
            "--output-budget-bytes",
            "65536",
            "--timeout-ms",
            "30000",
            "--grace-ms",
            "500",
            "--stage-id",
            "guardian_contains_wrapper_death",
            "--",
            sys.executable,
            "-c",
            guardian_program,
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    _guardian_out, guardian_err = guardian_wrapper.communicate(timeout=30)
    require(
        guardian_wrapper.returncode == SETUP_FAILURE,
        f"guardian wrapper exit {guardian_wrapper.returncode}: {guardian_err!r}",
    )
    require(guardian_pid_file.exists(), "wrapper-death child did not publish PIDs")
    guardian_pids = [
        int(value)
        for value in guardian_pid_file.read_text(encoding="utf-8").splitlines()
    ]
    time.sleep(0.1)
    require(
        not any(process_alive(pid) for pid in guardian_pids),
        "guardian left a process after inner-supervisor death",
    )
    cases.append(
        {
            "case": "guardian_contains_wrapper_death",
            "ok": True,
            "pids": guardian_pids,
        }
    )

    guardian_fault_root = case_dir("guardian_pidfd_open_failure")
    guardian_fault_ready = guardian_fault_root / "stage.ready.json"
    guardian_fault_pids = guardian_fault_root / "pids.txt"
    guardian_fault_program = (
        "import os,pathlib,signal,subprocess,sys,time;"
        "code='import signal,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);time.sleep(60)';"
        "p=subprocess.Popen([sys.executable,'-c',code],start_new_session=True);"
        f"pathlib.Path({str(guardian_fault_pids)!r}).write_text(str(os.getpid())+'\\n'+str(p.pid)+'\\n');"
        "time.sleep(60)"
    )
    guardian_fault_wrapper = subprocess.Popen(
        [
            sys.executable,
            str(Path(__file__).resolve()),
            "run",
            "--cwd",
            str(art_dir),
            "--metadata",
            str(guardian_fault_root / "stage.meta.json"),
            "--stdout",
            str(guardian_fault_root / "stage.out"),
            "--stderr",
            str(guardian_fault_root / "stage.err"),
            "--readiness",
            str(guardian_fault_ready),
            "--artifact-root",
            str(art_dir),
            "--capture-bytes",
            "4096",
            "--output-budget-bytes",
            "65536",
            "--timeout-ms",
            "30000",
            "--grace-ms",
            "500",
            "--stage-id",
            "guardian_pidfd_open_failure",
            "--test-fail-guardian-pidfd-open",
            "--test-guardian-child-ready",
            str(guardian_fault_pids),
            "--",
            sys.executable,
            "-c",
            guardian_fault_program,
        ],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    _fault_out, fault_err = guardian_fault_wrapper.communicate(timeout=30)
    require(
        guardian_fault_wrapper.returncode == SETUP_FAILURE,
        f"guardian pidfd-fault exit {guardian_fault_wrapper.returncode}: {fault_err!r}",
    )
    guardian_fault_readiness = read_json_object(guardian_fault_ready)
    require(
        guardian_fault_readiness.get("schema") == "fln.supervisor-readiness/1"
        and guardian_fault_readiness.get("status") == "ready"
        and guardian_fault_readiness.get("stage_id")
        == "guardian_pidfd_open_failure",
        "post-fork guardian setup fault lacked exact readiness",
    )
    fault_pids = [
        int(value)
        for value in guardian_fault_pids.read_text(encoding="utf-8").splitlines()
    ]
    require(len(fault_pids) == 2, "guardian fault PID handshake was malformed")
    require(
        guardian_fault_readiness.get("child_pid") == fault_pids[0],
        "guardian fault readiness did not bind its stage leader",
    )
    require(
        not any(process_alive(pid) for pid in fault_pids),
        "post-fork guardian setup failure left its detached tree alive",
    )
    cases.append(
        {
            "case": "guardian_pidfd_open_failure",
            "ok": True,
            "pids": fault_pids,
        }
    )

    pdeath_root = case_dir("stopped_exec_parent_death")
    pdeath_pid_file = pdeath_root / "pids.txt"
    pdeath_program = (
        "import os,pathlib,subprocess,sys,time;"
        "p=subprocess.Popen([sys.executable,"
        f"{str(Path(__file__).resolve())!r},'stopped-exec',"
        "'--expected-parent-pid',str(os.getpid()),'--',sys.executable,'-c',"
        "'import time;time.sleep(60)'],start_new_session=True,"
        "stdin=subprocess.DEVNULL,stdout=subprocess.DEVNULL,"
        "stderr=subprocess.DEVNULL);"
        f"pathlib.Path({str(pdeath_pid_file)!r}).write_text("
        "str(os.getpid())+'\\n'+str(p.pid)+'\\n');"
        "time.sleep(60)"
    )
    pdeath_launcher: subprocess.Popen[bytes] | None = None
    pdeath_handle: tuple[int, int] | None = None
    pdeath_child_pid = 0
    try:
        pdeath_launcher = subprocess.Popen(
            [sys.executable, "-c", pdeath_program],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        deadline = time.monotonic() + 15.0
        previous_payload: bytes | None = None
        stable_reads = 0
        published_pids: tuple[int, ...] = ()
        while time.monotonic() < deadline:
            try:
                payload, _size, _digest = stable_file_facts(
                    pdeath_pid_file, max_bytes=128
                )
                values = tuple(
                    int(value) for value in payload.decode("ascii").splitlines()
                )
                if (
                    len(values) == 2
                    and values[0] == pdeath_launcher.pid
                    and values[1] > 1
                    and values[0] != values[1]
                ):
                    stable_reads = (
                        stable_reads + 1 if payload == previous_payload else 1
                    )
                    previous_payload = payload
                    published_pids = values
                    if stable_reads >= 2:
                        break
                else:
                    stable_reads = 0
                    previous_payload = None
            except (EvidenceError, FileNotFoundError, UnicodeError, ValueError):
                stable_reads = 0
                previous_payload = None
            time.sleep(0.01)
        else:
            raise EvidenceError("stopped-exec parent-death handshake timed out")
        pdeath_child_pid = published_pids[1]
        pdeath_handle = open_process_handle(
            pdeath_child_pid, expected_parent_pid=pdeath_launcher.pid
        )
        require(pdeath_handle is not None, "stopped-exec child identity was unbound")
        retry_attempts = 0

        def delayed_identity_open() -> tuple[int, int] | None:
            nonlocal retry_attempts
            retry_attempts += 1
            if retry_attempts == 1:
                return None
            return open_process_handle(
                pdeath_child_pid, expected_parent_pid=pdeath_launcher.pid
            )

        retry_handle = bind_direct_child_until(
            pdeath_child_pid,
            pdeath_launcher.pid,
            time.monotonic() + 30.0,
            open_handle=delayed_identity_open,
        )
        try:
            require(
                retry_attempts == 2 and retry_handle[0] == pdeath_handle[0],
                "direct-child identity binding did not retry the same lifetime",
            )
        finally:
            os.close(retry_handle[1])
        deadline = time.monotonic() + 5.0
        while True:
            pdeath_facts = proc_stat_facts(pdeath_child_pid)
            if (
                pdeath_facts is None
                or pdeath_facts[0] == "Z"
                or pdeath_facts[2] != pdeath_handle[0]
            ):
                raise EvidenceError("stopped-exec child changed before becoming inert")
            if (
                pdeath_facts[0] in {"T", "t"}
                and pdeath_facts[1] == pdeath_child_pid
            ):
                break
            if time.monotonic() >= deadline:
                raise EvidenceError("stopped-exec child did not become inert in time")
            time.sleep(0.005)
        require(
            pdeath_facts[0] in {"T", "t"}
            and pdeath_facts[1] == pdeath_child_pid
            and pdeath_facts[2] == pdeath_handle[0],
            "stopped-exec child did not reach its inert session state",
        )
        identity_probe = subprocess.run(
            [
                sys.executable,
                str(Path(__file__).resolve()),
                "process-start-ticks",
                "--pid",
                str(pdeath_child_pid),
                "--expected-parent-pid",
                str(pdeath_launcher.pid),
                "--wait-ms",
                "30000",
                "--session-leader",
                "--stopped",
            ],
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=60,
        )
        require(
            identity_probe.returncode == PASS,
            "declared readiness budget was rejected by identity binding: "
            f"{identity_probe.stderr[-1000:]!r}",
        )
        require(
            identity_probe.stdout.decode("ascii").strip()
            == str(pdeath_handle[0]),
            "readiness-budget identity probe returned the wrong lifetime",
        )
        pdeath_launcher.kill()
        pdeath_launcher.communicate(timeout=10)
        deadline = time.monotonic() + 5.0
        while process_handle_alive(pdeath_child_pid, pdeath_handle):
            if time.monotonic() >= deadline:
                break
            time.sleep(0.01)
        require(
            not process_handle_alive(pdeath_child_pid, pdeath_handle),
            "stopped-exec child survived its launching parent",
        )
    finally:
        try:
            if pdeath_launcher is not None and pdeath_launcher.poll() is None:
                pdeath_launcher.kill()
                pdeath_launcher.communicate(timeout=10)
        finally:
            if pdeath_handle is not None:
                try:
                    if process_handle_alive(pdeath_child_pid, pdeath_handle):
                        signal_process_handle(
                            pdeath_child_pid, pdeath_handle, signal.SIGKILL
                        )
                finally:
                    os.close(pdeath_handle[1])
    cases.append(
        {
            "case": "stopped_exec_parent_death",
            "ok": True,
            "launcher_pid": published_pids[0],
            "child_pid": pdeath_child_pid,
            "identity_wait_budget_ms": 30_000,
            "identity_bind_attempts": retry_attempts,
        }
    )

    case_dir("direct_child_cleanup_identity")
    direct_child = subprocess.Popen(
        [sys.executable, "-c", "import time;time.sleep(60)"],
        stdin=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    direct_handle: tuple[int, int] | None = None
    try:
        direct_handle = open_process_handle(
            direct_child.pid, expected_parent_pid=os.getpid()
        )
        require(direct_handle is not None, "direct child identity was unbound")
        wrong_parent_pid = os.getppid()
        require(
            wrong_parent_pid > 1 and wrong_parent_pid != os.getpid(),
            "direct child self-test lacks a distinct wrong parent",
        )
        wrong_parent_rc = cmd_kill_direct_child(
            argparse.Namespace(
                pid=direct_child.pid,
                expected_parent_pid=wrong_parent_pid,
                wait_ms=100,
            )
        )
        require(wrong_parent_rc == PASS, "wrong-parent cleanup did not fail closed")
        require(
            process_handle_alive(direct_child.pid, direct_handle),
            "wrong-parent cleanup signalled the direct child",
        )
        exact_rc = cmd_kill_direct_child(
            argparse.Namespace(
                pid=direct_child.pid,
                expected_parent_pid=os.getpid(),
                wait_ms=5000,
            )
        )
        require(exact_rc == PASS, "exact direct-child cleanup failed")
        require(
            not process_handle_alive(direct_child.pid, direct_handle),
            "exact direct-child cleanup left its bound lifetime live",
        )
        direct_child.communicate(timeout=10)
    finally:
        try:
            if direct_child.poll() is None:
                if direct_handle is not None:
                    signal_process_handle(
                        direct_child.pid, direct_handle, signal.SIGKILL
                    )
                else:
                    direct_child.kill()
                direct_child.communicate(timeout=10)
        finally:
            if direct_handle is not None:
                os.close(direct_handle[1])
    cases.append(
        {
            "case": "direct_child_cleanup_identity",
            "ok": True,
            "child_pid": direct_child.pid,
        }
    )

    bound_group_root = case_dir("bound_group_stale_identity")
    bound_group_member_file = bound_group_root / "member.pid"
    bound_group_program = (
        "import pathlib,subprocess,sys,time;"
        "p=subprocess.Popen([sys.executable,'-c','import time;time.sleep(60)']);"
        f"pathlib.Path({str(bound_group_member_file)!r}).write_text(str(p.pid));"
        "time.sleep(60)"
    )
    bound_group_child = subprocess.Popen(
        [
            sys.executable,
            str(Path(__file__).resolve()),
            "stopped-exec",
            "--expected-parent-pid",
            str(os.getpid()),
            "--",
            sys.executable,
            "-c",
            bound_group_program,
        ],
        start_new_session=True,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    bound_group_sentinel = subprocess.Popen(
        [sys.executable, "-c", "import time;time.sleep(60)"],
        start_new_session=True,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    bound_group_handle: tuple[int, int] | None = None
    bound_group_member_handle: tuple[int, int] | None = None
    bound_group_sentinel_handle: tuple[int, int] | None = None
    bound_group_member_pid = 0
    try:
        bound_group_sentinel_handle = open_process_handle(
            bound_group_sentinel.pid, expected_parent_pid=os.getpid()
        )
        require(
            bound_group_sentinel_handle is not None,
            "unrelated process-group sentinel was not bindable",
        )
        deadline = time.monotonic() + 5.0
        while time.monotonic() < deadline:
            bound_group_handle = open_process_handle(
                bound_group_child.pid, expected_parent_pid=os.getpid()
            )
            bound_group_facts = proc_stat_facts(bound_group_child.pid)
            if (
                bound_group_handle is not None
                and bound_group_facts is not None
                and bound_group_facts[0] in {"T", "t"}
                and bound_group_facts[1] == bound_group_child.pid
                and bound_group_facts[2] == bound_group_handle[0]
            ):
                break
            if bound_group_handle is not None:
                os.close(bound_group_handle[1])
                bound_group_handle = None
            time.sleep(0.005)
        else:
            raise EvidenceError("bound-group child did not become inert in time")
        kill_bound_process_group(
            bound_group_child.pid,
            bound_group_handle[0] + 1,
            os.getpid(),
        )
        require(
            process_handle_alive(bound_group_child.pid, bound_group_handle),
            "stale start-time cleanup signalled the bound process group",
        )
        require(
            process_handle_alive(
                bound_group_sentinel.pid, bound_group_sentinel_handle
            ),
            "stale start-time cleanup signalled the unrelated sentinel",
        )
        require(
            signal_process_handle(
                bound_group_child.pid, bound_group_handle, signal.SIGCONT
            ),
            "bound-group child disappeared before descendant launch",
        )
        deadline = time.monotonic() + 10.0
        while time.monotonic() < deadline:
            try:
                member_data, _size, _digest = stable_file_facts(
                    bound_group_member_file, max_bytes=64
                )
                candidate_pid = int(member_data.decode("ascii"))
            except (EvidenceError, FileNotFoundError, UnicodeError, ValueError):
                time.sleep(0.005)
                continue
            candidate_handle = open_process_handle(
                candidate_pid, expected_parent_pid=bound_group_child.pid
            )
            candidate_facts = proc_stat_facts(candidate_pid)
            if (
                candidate_handle is not None
                and candidate_facts is not None
                and candidate_facts[0] != "Z"
                and candidate_facts[1] == bound_group_child.pid
                and candidate_facts[2] == candidate_handle[0]
            ):
                bound_group_member_pid = candidate_pid
                bound_group_member_handle = candidate_handle
                break
            if candidate_handle is not None:
                os.close(candidate_handle[1])
            time.sleep(0.005)
        else:
            raise EvidenceError("bound process-group descendant was not bindable")
        require(
            {bound_group_child.pid, bound_group_member_pid}.issubset(
                live_process_group_members(bound_group_child.pid)
            ),
            "bound process-group topology omitted its descendant",
        )
        kill_bound_process_group(
            bound_group_child.pid,
            bound_group_handle[0],
            os.getpid(),
        )
        require(
            not process_handle_alive(bound_group_child.pid, bound_group_handle),
            "exact process-group cleanup left its leader live",
        )
        require(
            not process_handle_alive(
                bound_group_member_pid, bound_group_member_handle
            ),
            "exact process-group cleanup left its descendant live",
        )
        require(
            process_handle_alive(
                bound_group_sentinel.pid, bound_group_sentinel_handle
            ),
            "exact process-group cleanup signalled the unrelated sentinel",
        )
        bound_group_child.communicate(timeout=10)
        deadline = time.monotonic() + 5.0
        while time.monotonic() < deadline:
            reap_adopted_children()
            member_facts = proc_stat_facts(bound_group_member_pid)
            if (
                member_facts is None
                or member_facts[2] != bound_group_member_handle[0]
            ):
                break
            time.sleep(0.005)
        require(
            (member_facts := proc_stat_facts(bound_group_member_pid)) is None
            or member_facts[2] != bound_group_member_handle[0],
            "exact process-group cleanup left its descendant unreaped",
        )
        exact_sentinel_rc = cmd_kill_direct_child(
            argparse.Namespace(
                pid=bound_group_sentinel.pid,
                expected_parent_pid=os.getpid(),
                wait_ms=5000,
            )
        )
        require(exact_sentinel_rc == PASS, "sentinel cleanup failed")
        bound_group_sentinel.communicate(timeout=10)
    finally:
        try:
            if (
                bound_group_member_handle is not None
                and process_handle_alive(
                    bound_group_member_pid, bound_group_member_handle
                )
            ):
                signal_process_handle(
                    bound_group_member_pid,
                    bound_group_member_handle,
                    signal.SIGKILL,
                )
            if bound_group_child.poll() is None:
                if bound_group_handle is not None:
                    signal_process_handle(
                        bound_group_child.pid, bound_group_handle, signal.SIGKILL
                    )
                else:
                    bound_group_child.kill()
                bound_group_child.communicate(timeout=10)
            if bound_group_sentinel.poll() is None:
                if bound_group_sentinel_handle is not None:
                    signal_process_handle(
                        bound_group_sentinel.pid,
                        bound_group_sentinel_handle,
                        signal.SIGKILL,
                    )
                else:
                    bound_group_sentinel.kill()
                bound_group_sentinel.communicate(timeout=10)
            reap_adopted_children()
        finally:
            if bound_group_member_handle is not None:
                os.close(bound_group_member_handle[1])
            if bound_group_sentinel_handle is not None:
                os.close(bound_group_sentinel_handle[1])
            if bound_group_handle is not None:
                os.close(bound_group_handle[1])
    cases.append(
        {
            "case": "bound_group_stale_identity",
            "ok": True,
            "leader_pid": bound_group_child.pid,
            "member_pid": bound_group_member_pid,
            "sentinel_pid": bound_group_sentinel.pid,
        }
    )

    cases.append(
        run_shell_finalizer_probe(
            "spawn_bind",
            signal.SIGHUP,
            129,
            expect_committed_bundle=False,
        )
    )
    cases.append(
        run_shell_finalizer_probe(
            "active_wait",
            signal.SIGINT,
            130,
            expect_committed_bundle=False,
        )
    )
    cases.append(
        run_shell_finalizer_probe(
            "helper_failure",
            signal.SIGTERM,
            SETUP_FAILURE,
            expect_committed_bundle=False,
        )
    )
    cases.append(
        run_shell_finalizer_probe(
            "post_decision",
            signal.SIGTERM,
            PASS,
            expect_committed_bundle=True,
        )
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
    relative_manifest_root = Path(os.path.relpath(manifest_root, Path.cwd()))
    try:
        complete_bundle(
            relative_manifest_root,
            relative_manifest_root / "manifest.json",
            relative_manifest_root / "manifest.digest",
            relative_manifest_root / "bundle.complete.json",
            governed_root=hash_root,
            governed_paths=["a", "b"],
            expected_root=first_hash,
            test_fail_after_link=True,
        )
    except EvidenceError as error:
        require(
            "injected failure after atomic link" in str(error),
            "bundle link fault produced the wrong failure",
        )
    else:
        raise EvidenceError("bundle link fault injection unexpectedly returned success")
    require(
        (manifest_root / "bundle.decision").exists()
        and not (manifest_root / "bundle.complete.json").exists(),
        "bundle link fault did not exercise the recovery window",
    )
    validate_bundle(
        manifest_root,
        manifest_root / "manifest.json",
        manifest_root / "manifest.digest",
        manifest_root / "bundle.complete.json",
    )
    require(
        (manifest_root / "bundle.complete.json").exists(),
        "bundle validation did not recover the winning decision",
    )
    validate_bundle(
        relative_manifest_root,
        relative_manifest_root / "manifest.json",
        relative_manifest_root / "manifest.digest",
        relative_manifest_root / "bundle.complete.json",
    )
    try:
        validate_bundle(
            manifest_root,
            manifest_root / "control" / "manifest.json",
            manifest_root / "control" / "manifest.digest",
            manifest_root / "bundle.complete.json",
        )
    except EvidenceError as error:
        require(
            "must be exactly" in str(error),
            "nested control path produced the wrong failure",
        )
    else:
        raise EvidenceError("nested bundle control paths were accepted")
    try:
        write_new(manifest_root / "bundle.complete.json", b"overwrite\n")
    except FileExistsError:
        pass
    else:
        raise EvidenceError("write-once bundle marker was overwritten")
    cases.append({"case": "write_once_manifest", "ok": True})

    relocated_root = case_dir("relocated_bundle_validation")
    source_manifest = read_json_object(manifest_root / "manifest.json")
    directory_entries = sorted(
        (
            entry
            for entry in source_manifest["artifacts"]
            if entry["role"] == "directory"
        ),
        key=lambda entry: (
            len(Path(entry["path"]).parts),
            entry["path"].encode("utf-8"),
        ),
    )
    for entry in directory_entries:
        (relocated_root / entry["path"]).mkdir()
    for entry in source_manifest["artifacts"]:
        if entry["role"] == "directory":
            continue
        source = manifest_root / entry["path"]
        data, _size, _digest = stable_file_facts(source)
        write_new(relocated_root / entry["path"], data)
    for control_name in (
        "manifest.json",
        "manifest.digest",
        "bundle.decision",
        "bundle.complete.json",
    ):
        data, _size, _digest = stable_file_facts(manifest_root / control_name)
        write_new(relocated_root / control_name, data)
    for identity_name in (
        "run.ndjson",
        "manifest.json",
        "bundle.complete.json",
    ):
        require(
            (manifest_root / identity_name).stat().st_ino
            != (relocated_root / identity_name).stat().st_ino,
            f"relocated bundle reused source inode: {identity_name}",
        )
    validate_bundle(
        relocated_root,
        relocated_root / "manifest.json",
        relocated_root / "manifest.digest",
        relocated_root / "bundle.complete.json",
    )
    cases.append({"case": "relocated_bundle_validation", "ok": True})

    cancellation_root = case_dir("bundle_decision_cancellation")
    cancellation_decision = cancellation_root / "bundle.decision"
    cancellation_marker = cancellation_root / "bundle.complete.json"
    write_new(cancellation_decision, b"")
    try:
        write_signal_committed_atomic_new(
            cancellation_marker,
            b'{"status":"committed"}\n',
            decision_path=cancellation_decision,
        )
    except EvidenceError as error:
        require(
            "cancellation won the bundle decision race" in str(error),
            "bundle cancellation produced the wrong failure",
        )
    else:
        raise EvidenceError("bundle commit ignored the cancellation decision")
    require(
        not cancellation_marker.exists(),
        "cancelled bundle decision still published a commit marker",
    )
    cases.append({"case": "bundle_decision_cancellation", "ok": True})

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
    run_parser.add_argument("--test-terminal-delay-ms", type=int, default=0)
    run_parser.add_argument("--test-terminal-ready")
    run_parser.add_argument("--launch-ready")
    run_parser.add_argument("--launch-release")
    run_parser.add_argument(
        "--test-fail-guardian-pidfd-open",
        action="store_true",
        help=argparse.SUPPRESS,
    )
    run_parser.add_argument("--test-guardian-child-ready", help=argparse.SUPPRESS)
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

    stopped_exec_parser = subparsers.add_parser(
        "stopped-exec", help="stop before exec for parent-side identity binding"
    )
    stopped_exec_parser.add_argument("--expected-parent-pid", type=int, required=True)
    stopped_exec_parser.add_argument("command", nargs=argparse.REMAINDER)
    stopped_exec_parser.set_defaults(func=cmd_stopped_exec)

    emergency_parser = subparsers.add_parser(
        "emergency-kill", help="validate readiness and SIGKILL its bound child group"
    )
    emergency_parser.add_argument("--readiness", required=True)
    emergency_parser.add_argument("--expected-wrapper-pid", type=int, required=True)
    emergency_parser.add_argument("--expected-stage-id", required=True)
    emergency_parser.set_defaults(func=cmd_emergency_kill)

    process_identity_parser = subparsers.add_parser(
        "process-start-ticks", help="bind one live session leader's Linux identity"
    )
    process_identity_parser.add_argument("--pid", type=int, required=True)
    process_identity_parser.add_argument(
        "--expected-parent-pid", type=int, required=True
    )
    process_identity_parser.add_argument("--wait-ms", type=int, default=0)
    process_identity_parser.add_argument("--session-leader", action="store_true")
    process_identity_parser.add_argument("--stopped", action="store_true")
    process_identity_parser.set_defaults(func=cmd_process_start_ticks)

    launch_release_parser = subparsers.add_parser(
        "release-process-launch",
        help="release one identity-bound guardian launch gate",
    )
    launch_release_parser.add_argument("--ready", required=True)
    launch_release_parser.add_argument("--output", required=True)
    launch_release_parser.add_argument("--artifact-root", required=True)
    launch_release_parser.add_argument("--stage-id", required=True)
    launch_release_parser.add_argument("--pid", type=int, required=True)
    launch_release_parser.add_argument(
        "--expected-start-ticks", type=int, required=True
    )
    launch_release_parser.add_argument(
        "--expected-parent-pid", type=int, required=True
    )
    launch_release_parser.add_argument("--wait-ms", type=int, default=5000)
    launch_release_parser.set_defaults(func=cmd_release_process_launch)

    bound_group_parser = subparsers.add_parser(
        "kill-bound-group", help="SIGKILL one start-time-bound process group"
    )
    bound_group_parser.add_argument("--pid", type=int, required=True)
    bound_group_parser.add_argument(
        "--expected-start-ticks", type=int, required=True
    )
    bound_group_parser.add_argument(
        "--expected-parent-pid", type=int, required=True
    )
    bound_group_parser.set_defaults(func=cmd_kill_bound_group)

    direct_child_parser = subparsers.add_parser(
        "kill-direct-child", help="pidfd-kill one current direct child"
    )
    direct_child_parser.add_argument("--pid", type=int, required=True)
    direct_child_parser.add_argument(
        "--expected-parent-pid", type=int, required=True
    )
    direct_child_parser.add_argument("--wait-ms", type=int, default=5000)
    direct_child_parser.set_defaults(func=cmd_kill_direct_child)

    bound_process_parser = subparsers.add_parser(
        "signal-bound-process", help="signal one start-time-bound process"
    )
    bound_process_parser.add_argument("--pid", type=int, required=True)
    bound_process_parser.add_argument(
        "--expected-start-ticks", type=int, required=True
    )
    bound_process_parser.add_argument(
        "--signal", choices=("HUP", "INT", "TERM"), required=True
    )
    bound_process_parser.set_defaults(func=cmd_signal_bound_process)

    resume_process_parser = subparsers.add_parser(
        "resume-bound-process",
        help="resume one exact stopped direct child after identity binding",
    )
    resume_process_parser.add_argument("--pid", type=int, required=True)
    resume_process_parser.add_argument(
        "--expected-start-ticks", type=int, required=True
    )
    resume_process_parser.add_argument(
        "--expected-parent-pid", type=int, required=True
    )
    resume_process_parser.set_defaults(func=cmd_resume_bound_process)

    empty_group_parser = subparsers.add_parser(
        "assert-process-group-empty",
        help="boundedly observe that a process group has no live members",
    )
    empty_group_parser.add_argument("--pgid", type=int, required=True)
    empty_group_parser.add_argument("--wait-ms", type=int, default=1000)
    empty_group_parser.set_defaults(func=cmd_assert_process_group_empty)

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
    complete_parser.add_argument("--test-fail-after-link", action="store_true")
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
