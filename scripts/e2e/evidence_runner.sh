#!/usr/bin/env bash
# External, no-mock stress lane for scripts/evidence.py's real supervisor CLI.
#
# The authoritative run executes 100 independent invocations for each core
# outcome. Lower --iterations values exist only for local syntax/smoke checks and
# are labeled diagnostic in the retained summary. Every supervisor envelope is
# validated by evidence.py and then checked again for the exact process facts
# this lane is intended to protect.

set -Eeuo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/e2e/evidence_runner.sh [--iterations N] [--artifact-root PATH]
       scripts/e2e/evidence_runner.sh [--iterations N] [PATH]

Defaults:
  --iterations 100
  --artifact-root /tmp/franken-lean-evidence-runner-<UTC>-<pid>

An artifact root must not already exist, and its non-symlink parent must exist.
Runs with fewer than 100 iterations are diagnostic smoke runs and do not satisfy
the authoritative stress obligation.
EOF
}

die_before_artifacts() {
  printf '[evidence_runner] setup failure: %s\n' "$*" >&2
  exit 2
}

ITERATIONS=100
ARTIFACT_ARGUMENT=""
while (($# > 0)); do
  case "$1" in
    --iterations)
      (($# >= 2)) || die_before_artifacts "--iterations requires a value"
      ITERATIONS="$2"
      shift 2
      ;;
    --artifact-root)
      (($# >= 2)) || die_before_artifacts "--artifact-root requires a path"
      [[ -z "$ARTIFACT_ARGUMENT" ]] \
        || die_before_artifacts "artifact root was supplied more than once"
      ARTIFACT_ARGUMENT="$2"
      shift 2
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    --)
      shift
      (($# == 0)) || die_before_artifacts "unexpected positional arguments"
      ;;
    -*)
      die_before_artifacts "unknown option: $1"
      ;;
    *)
      [[ -z "$ARTIFACT_ARGUMENT" ]] \
        || die_before_artifacts "artifact root was supplied more than once"
      ARTIFACT_ARGUMENT="$1"
      shift
      ;;
  esac
done

[[ "$ITERATIONS" =~ ^[0-9]+$ ]] \
  || die_before_artifacts "--iterations must be a positive integer"
ITERATIONS=$((10#$ITERATIONS))
((ITERATIONS >= 1 && ITERATIONS <= 100)) \
  || die_before_artifacts "--iterations must be between 1 and 100"

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
SELF="$ROOT/scripts/e2e/evidence_runner.sh"
EXECUTED_RUNNER_SOURCE="/proc/$$/fd/255"
EVIDENCE_SOURCE="$ROOT/scripts/evidence.py"
EVIDENCE="$EVIDENCE_SOURCE"
PYTHON_BIN="$(command -v python3 || true)"
SHA256SUM_BIN="$(command -v sha256sum || true)"
CMP_BIN="$(command -v cmp || true)"
SETSID_BIN="$(command -v setsid || true)"
SLEEP_BIN="$(command -v sleep || true)"

[[ -n "$PYTHON_BIN" ]] || die_before_artifacts "python3 is required"
[[ -n "$SHA256SUM_BIN" ]] || die_before_artifacts "sha256sum is required"
[[ -n "$CMP_BIN" ]] || die_before_artifacts "cmp is required"
[[ -n "$SETSID_BIN" ]] || die_before_artifacts "setsid is required"
[[ -n "$SLEEP_BIN" ]] || die_before_artifacts "sleep is required"
[[ -f "$EVIDENCE_SOURCE" && ! -L "$EVIDENCE_SOURCE" ]] \
  || die_before_artifacts "scripts/evidence.py must be a regular non-symlink file"
[[ -r "$EXECUTED_RUNNER_SOURCE" ]] \
  || die_before_artifacts "cannot bind the runner inode held open by Bash"
[[ -x /usr/bin/true ]] || die_before_artifacts "/usr/bin/true is required"
[[ -x /usr/bin/false ]] || die_before_artifacts "/usr/bin/false is required"

RUN_ID="evidence-runner-$(date -u +%Y%m%dT%H%M%SZ)-$$"
if [[ -n "$ARTIFACT_ARGUMENT" ]]; then
  ART_DIR_RAW="$ARTIFACT_ARGUMENT"
else
  ART_DIR_RAW="/tmp/franken-lean-$RUN_ID"
fi
ART_DIR="$(
  "$PYTHON_BIN" -I -S - "$ART_DIR_RAW" <<'PY'
import os
import stat
import sys
from pathlib import Path

target = Path(os.path.abspath(sys.argv[1]))
parent = target.parent
if target.name in {"", ".", ".."}:
    raise SystemExit("artifact root has no claimable leaf")

probe = Path(parent.anchor)
for component in parent.parts[1:]:
    probe /= component
    try:
        mode = os.lstat(probe).st_mode
    except FileNotFoundError:
        raise SystemExit(f"artifact parent does not exist: {probe}") from None
    if stat.S_ISLNK(mode):
        raise SystemExit(f"artifact parent traverses a symlink: {probe}")
    if not stat.S_ISDIR(mode):
        raise SystemExit(f"artifact parent component is not a directory: {probe}")

try:
    os.lstat(target)
except FileNotFoundError:
    pass
else:
    raise SystemExit(f"artifact root is not fresh: {target}")
print(target)
PY
)" || die_before_artifacts "artifact root preflight failed"
LOG="$ART_DIR/run.ndjson"
HUMAN_LOG="$ART_DIR/human.log"
SOURCE_BEFORE="$ART_DIR/source.before.sha256"
SOURCE_AFTER="$ART_DIR/source.after.sha256"
SCHEMA="fln.evidence-runner-stress/1"
DATA_GRADE="diagnostic"
if ((ITERATIONS == 100)); then
  DATA_GRADE="verified"
fi

SEQ=0
FINALIZED=0
PASS_TERMINAL_PUBLISHED=0
ACTIVE_PID=""
ACTIVE_START_TICKS=""
ACTIVE_STAGE=""
ACTIVE_READINESS=""
ACTIVE_RELEASED=0
ACTIVE_TIMER_PID=""
RUN_STARTED=0
CLAIMED=0

snapshot_live_sources() {
  local output="$1"
  "$PYTHON_BIN" -I -S - \
    "$EVIDENCE_SOURCE" "$SELF" "$output" <<'PY'
import hashlib
import os
import stat
import sys
from pathlib import Path


def stable_bytes(path: Path) -> bytes:
    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(path, flags)
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise RuntimeError(f"source is not regular: {path}")
        chunks = []
        while True:
            block = os.read(descriptor, 1024 * 1024)
            if not block:
                break
            chunks.append(block)
        after = os.fstat(descriptor)
        if (
            before.st_dev,
            before.st_ino,
            before.st_size,
            before.st_mtime_ns,
            before.st_ctime_ns,
        ) != (
            after.st_dev,
            after.st_ino,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        ):
            raise RuntimeError(f"source changed while sampled: {path}")
        return b"".join(chunks)
    finally:
        os.close(descriptor)


rows = []
for raw in sys.argv[1:3]:
    path = Path(raw)
    data = stable_bytes(path)
    rows.append(f"{hashlib.sha256(data).hexdigest()}  {path}\n")
payload = "".join(rows).encode()
flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
if hasattr(os, "O_NOFOLLOW"):
    flags |= os.O_NOFOLLOW
descriptor = os.open(sys.argv[3], flags, 0o600)
try:
    offset = 0
    while offset < len(payload):
        written = os.write(descriptor, payload[offset:])
        if written <= 0:
            raise RuntimeError("source snapshot write made no progress")
        offset += written
    os.fsync(descriptor)
finally:
    os.close(descriptor)
PY
}

finalize_failure() {
  local status=$?
  local source_stable=null
  if ((status != 0 && FINALIZED == 0 && CLAIMED == 1)); then
    set +e
    FINALIZED=1
    if declare -F cleanup_active_child >/dev/null 2>&1 \
        && [[ -n "${ACTIVE_PID:-}" ]]; then
      cleanup_active_child
    fi
    if [[ ! -e "$SOURCE_AFTER" && ! -L "$SOURCE_AFTER" ]]; then
      snapshot_live_sources "$SOURCE_AFTER" || true
    fi
    if [[ -f "$SOURCE_BEFORE" && -f "$SOURCE_AFTER" ]] \
        && "$CMP_BIN" -s -- "$SOURCE_BEFORE" "$SOURCE_AFTER"; then
      source_stable=true
    elif [[ -f "$SOURCE_BEFORE" && -f "$SOURCE_AFTER" ]]; then
      source_stable=false
    fi
    "$PYTHON_BIN" -I -S - \
      "$LOG" \
      "$SCHEMA" \
      "$RUN_ID" \
      "$DATA_GRADE" \
      "$SEQ" \
      "$status" \
      "$ART_DIR" \
      "$source_stable" \
      "$RUN_STARTED" \
      "$PASS_TERMINAL_PUBLISHED" \
      "${CLEANUP_ACTIVE_PROVEN:-true}" <<'PY'
import json
import os
import sys
import time

(
    path,
    schema,
    run_id,
    data_grade,
    sequence_raw,
    status_raw,
    artifact_root,
    source_stable_raw,
    run_started_raw,
    pass_terminal_published_raw,
    cleanup_proven_raw,
) = sys.argv[1:]
source_stable = {
    "null": None,
    "false": False,
    "true": True,
}[source_stable_raw]
pass_terminal_published = pass_terminal_published_raw == "1"
if pass_terminal_published:
    path = os.path.join(artifact_root, "bundle.failure.json")
    record = {
        "schema": "fln.evidence-runner-bundle-failure/1",
        "run_id": run_id,
        "status": "failed",
        "process_exit": int(status_raw),
        "artifact_root": artifact_root,
        "source_stable": source_stable,
        "pass_terminal_published": True,
        "bundle_committed": False,
        "cleanup_proven": cleanup_proven_raw == "true",
    }
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    payload = json.dumps(record, sort_keys=True, separators=(",", ":")).encode()
else:
    record = {
        "schema": schema,
        "run_id": run_id,
        "event": "run_end",
        "status": "failed",
        "data_grade": data_grade,
        "sequence": int(sequence_raw),
        "monotonic_ns": time.monotonic_ns(),
        "process_exit": int(status_raw),
        "artifact_root": artifact_root,
        "source_stable": source_stable,
        "run_started": run_started_raw == "1",
        "cleanup_proven": cleanup_proven_raw == "true",
    }
    payload = (
        json.dumps(record, sort_keys=True, separators=(",", ":")).encode()
        + b"\n"
    )
    flags = os.O_WRONLY | os.O_CREAT | os.O_APPEND | os.O_CLOEXEC
if hasattr(os, "O_NOFOLLOW"):
    flags |= os.O_NOFOLLOW
descriptor = os.open(path, flags, 0o600)
try:
    offset = 0
    while offset < len(payload):
        written = os.write(descriptor, payload[offset:])
        if written <= 0:
            raise RuntimeError("failure terminal write made no progress")
        offset += written
    os.fsync(descriptor)
finally:
    os.close(descriptor)
PY
    printf '[evidence_runner] FAIL (exit %s); retained artifacts: %s\n' \
      "$status" "$ART_DIR" | tee -a "$HUMAN_LOG" >&2
  fi
}

umask 077
if ! mkdir -- "$ART_DIR"; then
  die_before_artifacts "could not atomically claim fresh artifact root: $ART_DIR"
fi
CLAIMED=1
trap finalize_failure EXIT
"$PYTHON_BIN" -I -S - "$ART_DIR" <<'PY'
import os
import stat
import sys
from pathlib import Path

target = Path(sys.argv[1])
probe = Path(target.anchor)
for component in target.parts[1:]:
    probe /= component
    mode = os.lstat(probe).st_mode
    if stat.S_ISLNK(mode):
        raise SystemExit(f"claimed artifact path traverses a symlink: {probe}")
    if not stat.S_ISDIR(mode):
        raise SystemExit(f"claimed artifact component is not a directory: {probe}")
PY

note() {
  printf '[evidence_runner] %s\n' "$*" | tee -a "$HUMAN_LOG" >&2
}

monotonic_ns() {
  "$PYTHON_BIN" -I -S -c 'import time; print(time.monotonic_ns())'
}

emit_event() {
  local event="$1"
  local sequence="$SEQ"
  local -a new_log=()
  shift
  if ((sequence == 0)); then
    new_log=(--new-log)
  fi
  "$PYTHON_BIN" -I -S "$EVIDENCE" emit \
    --file "$LOG" \
    --artifact-root "$ART_DIR" \
    "${new_log[@]}" \
    --string schema "$SCHEMA" \
    --string run_id "$RUN_ID" \
    --string event "$event" \
    --string data_grade "$DATA_GRADE" \
    --integer sequence "$sequence" \
    --integer monotonic_ns "$(monotonic_ns)" \
    "$@"
  SEQ=$((SEQ + 1))
}

FROZEN_SOURCE_DIR="$ART_DIR/frozen-source"
FROZEN_EVIDENCE="$FROZEN_SOURCE_DIR/evidence.py"
FROZEN_RUNNER="$FROZEN_SOURCE_DIR/evidence_runner.sh"
mkdir -- "$FROZEN_SOURCE_DIR"
"$PYTHON_BIN" -I -S - \
  "$EVIDENCE_SOURCE" "$EVIDENCE_SOURCE" "$FROZEN_EVIDENCE" \
  "$EXECUTED_RUNNER_SOURCE" "$SELF" "$FROZEN_RUNNER" \
  "$SELF" "$SOURCE_BEFORE" <<'PY'
import hashlib
import os
import stat
import sys
from pathlib import Path

rows = []
frozen_data = []
for source_raw, label_raw, destination_raw, allow_proc_fd in (
    (sys.argv[1], sys.argv[2], sys.argv[3], False),
    (sys.argv[4], sys.argv[5], sys.argv[6], True),
):
    source = Path(source_raw)
    label = Path(label_raw)
    destination = Path(destination_raw)
    read_flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW") and not allow_proc_fd:
        read_flags |= os.O_NOFOLLOW
    source_descriptor = os.open(source, read_flags)
    try:
        before = os.fstat(source_descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise RuntimeError(f"source is not regular: {source}")
        chunks = []
        while True:
            block = os.read(source_descriptor, 1024 * 1024)
            if not block:
                break
            chunks.append(block)
        after = os.fstat(source_descriptor)
        if (
            before.st_dev,
            before.st_ino,
            before.st_size,
            before.st_mtime_ns,
            before.st_ctime_ns,
        ) != (
            after.st_dev,
            after.st_ino,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        ):
            raise RuntimeError(f"source changed while frozen: {source}")
        data = b"".join(chunks)
    finally:
        os.close(source_descriptor)

    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(destination, flags, 0o500)
    try:
        offset = 0
        while offset < len(data):
            written = os.write(descriptor, data[offset:])
            if written <= 0:
                raise RuntimeError("frozen source copy made no progress")
            offset += written
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    copied = destination.read_bytes()
    if copied != data:
        raise RuntimeError(f"frozen source copy disagrees: {destination}")
    frozen_data.append(data)
    rows.append(f"{hashlib.sha256(data).hexdigest()}  {label}\n")

runner_path = Path(sys.argv[7])
runner_flags = os.O_RDONLY | os.O_CLOEXEC
if hasattr(os, "O_NOFOLLOW"):
    runner_flags |= os.O_NOFOLLOW
runner_descriptor = os.open(runner_path, runner_flags)
try:
    runner_before = os.fstat(runner_descriptor)
    runner_bytes = b""
    while True:
        block = os.read(runner_descriptor, 1024 * 1024)
        if not block:
            break
        runner_bytes += block
    runner_after = os.fstat(runner_descriptor)
finally:
    os.close(runner_descriptor)
if (
    not stat.S_ISREG(runner_before.st_mode)
    or (
        runner_before.st_dev,
        runner_before.st_ino,
        runner_before.st_size,
        runner_before.st_mtime_ns,
        runner_before.st_ctime_ns,
    )
    != (
        runner_after.st_dev,
        runner_after.st_ino,
        runner_after.st_size,
        runner_after.st_mtime_ns,
        runner_after.st_ctime_ns,
    )
    or runner_bytes != frozen_data[1]
):
    raise RuntimeError("runner pathname does not match Bash's executed inode")

manifest_data = "".join(rows).encode()
manifest_descriptor = os.open(
    sys.argv[8],
    os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC,
    0o600,
)
try:
    offset = 0
    while offset < len(manifest_data):
        written = os.write(manifest_descriptor, manifest_data[offset:])
        if written <= 0:
            raise RuntimeError("source manifest write made no progress")
        offset += written
    os.fsync(manifest_descriptor)
finally:
    os.close(manifest_descriptor)
PY
SOURCE_SET_SHA256="$(
  "$SHA256SUM_BIN" -- "$SOURCE_BEFORE" | {
    read -r digest _
    printf '%s' "$digest"
  }
)"
EVIDENCE="$FROZEN_EVIDENCE"

BOUNDED_WAIT_EXIT=2
bounded_wait_child() {
  local pid="$1"
  local seconds="$2"
  local completed=""
  local had_errexit=0
  local timer_pid
  local wait_status

  if [[ $- == *e* ]]; then
    had_errexit=1
  fi
  "$SLEEP_BIN" "$seconds" &
  timer_pid=$!
  ACTIVE_TIMER_PID="$timer_pid"
  set +e
  wait -n -p completed "$pid" "$timer_pid"
  wait_status=$?
  if ((had_errexit == 1)); then
    set -e
  fi
  if [[ "$completed" == "$pid" ]]; then
    kill "$timer_pid" 2>/dev/null || true
    wait "$timer_pid" 2>/dev/null || true
    ACTIVE_TIMER_PID=""
    BOUNDED_WAIT_EXIT="$wait_status"
    return 0
  fi
  if [[ "$completed" != "$timer_pid" ]]; then
    kill "$timer_pid" 2>/dev/null || true
    wait "$timer_pid" 2>/dev/null || true
  fi
  ACTIVE_TIMER_PID=""
  return 1
}

CLEANUP_ACTIVE_PROVEN=true
cleanup_active_child() {
  local pid="$ACTIVE_PID"
  local child_pgid=""
  local cleanup_prefix
  local reaped=false
  local guardian_group_empty=false
  local child_group_empty=true
  local action_errors=0
  [[ -n "$pid" ]] || return 0
  CLEANUP_ACTIVE_PROVEN=false
  cleanup_prefix="$ART_DIR/cleanup-${ACTIVE_STAGE:-unknown}"
  if [[ -n "$ACTIVE_TIMER_PID" ]]; then
    if ! kill "$ACTIVE_TIMER_PID" 2>/dev/null; then
      action_errors=$((action_errors + 1))
    fi
    if wait "$ACTIVE_TIMER_PID" 2>/dev/null; then
      :
    fi
    ACTIVE_TIMER_PID=""
  fi
  if [[ -s "$ACTIVE_READINESS" ]]; then
    if ! child_pgid="$(
      "$PYTHON_BIN" -I -S - "$ACTIVE_READINESS" \
        2>"$cleanup_prefix-readiness.stderr" <<'PY'
import json
import sys
from pathlib import Path

value = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
pid = value.get("child_pgid")
if isinstance(pid, int) and not isinstance(pid, bool) and pid > 1:
    print(pid)
PY
    )"; then
      action_errors=$((action_errors + 1))
      child_group_empty=false
    fi
  fi
  if ((ACTIVE_RELEASED == 1)) && [[ -n "$ACTIVE_START_TICKS" ]]; then
    if ! "$PYTHON_BIN" -I -S "$EVIDENCE" signal-bound-process \
        --pid "$pid" \
        --expected-start-ticks "$ACTIVE_START_TICKS" \
        --signal TERM \
        >"$cleanup_prefix-term.stdout" \
        2>"$cleanup_prefix-term.stderr"; then
      action_errors=$((action_errors + 1))
    fi
    if [[ -s "$ACTIVE_READINESS" ]]; then
      if ! "$PYTHON_BIN" -I -S "$EVIDENCE" emergency-kill \
          --readiness "$ACTIVE_READINESS" \
          --expected-wrapper-pid "$pid" \
          --expected-stage-id "$ACTIVE_STAGE" \
          >"$cleanup_prefix-emergency.stdout" \
          2>"$cleanup_prefix-emergency.stderr"; then
        action_errors=$((action_errors + 1))
      fi
    fi
    if ! "$PYTHON_BIN" -I -S "$EVIDENCE" kill-bound-group \
        --pid "$pid" \
        --expected-start-ticks "$ACTIVE_START_TICKS" \
        --expected-parent-pid "$$" \
        >"$cleanup_prefix-group-kill.stdout" \
        2>"$cleanup_prefix-group-kill.stderr"; then
      action_errors=$((action_errors + 1))
    fi
  else
    if ! "$PYTHON_BIN" -I -S "$EVIDENCE" kill-direct-child \
        --pid "$pid" \
        --expected-parent-pid "$$" \
        --wait-ms 5000 \
        >"$cleanup_prefix-direct.stdout" \
        2>"$cleanup_prefix-direct.stderr"; then
      action_errors=$((action_errors + 1))
    fi
  fi
  if bounded_wait_child "$pid" 5; then
    reaped=true
  else
    action_errors=$((action_errors + 1))
    if ! "$PYTHON_BIN" -I -S "$EVIDENCE" kill-direct-child \
        --pid "$pid" \
        --expected-parent-pid "$$" \
        --wait-ms 5000 \
        >"$cleanup_prefix-direct-retry.stdout" \
        2>"$cleanup_prefix-direct-retry.stderr"; then
      action_errors=$((action_errors + 1))
    fi
    if bounded_wait_child "$pid" 5; then
      reaped=true
    else
      action_errors=$((action_errors + 1))
    fi
  fi
  if [[ -n "$ACTIVE_TIMER_PID" ]]; then
    if ! kill "$ACTIVE_TIMER_PID" 2>/dev/null; then
      action_errors=$((action_errors + 1))
    fi
    if ! wait "$ACTIVE_TIMER_PID" 2>/dev/null; then
      action_errors=$((action_errors + 1))
    fi
    ACTIVE_TIMER_PID=""
  fi
  if "$PYTHON_BIN" -I -S "$EVIDENCE" assert-process-group-empty \
      --pgid "$pid" \
      --wait-ms 5000 \
      >"$cleanup_prefix-group-empty.stdout" \
      2>"$cleanup_prefix-group-empty.stderr"; then
    guardian_group_empty=true
  else
    action_errors=$((action_errors + 1))
  fi
  if [[ -n "$child_pgid" ]]; then
    if "$PYTHON_BIN" -I -S "$EVIDENCE" assert-process-group-empty \
        --pgid "$child_pgid" \
        --wait-ms 5000 \
        >"$cleanup_prefix-child-group-empty.stdout" \
        2>"$cleanup_prefix-child-group-empty.stderr"; then
      child_group_empty=true
    else
      child_group_empty=false
      action_errors=$((action_errors + 1))
    fi
  fi
  if [[ "$reaped" == true \
      && "$guardian_group_empty" == true \
      && "$child_group_empty" == true ]]; then
    CLEANUP_ACTIVE_PROVEN=true
    ACTIVE_PID=""
    ACTIVE_START_TICKS=""
    ACTIVE_STAGE=""
    ACTIVE_READINESS=""
    ACTIVE_RELEASED=0
  else
    printf '[evidence_runner] cleanup proof failed for %s (%s action errors)\n' \
      "${ACTIVE_STAGE:-unknown}" "$action_errors" >&2
  fi
}

on_signal() {
  local signal_name="$1"
  local exit_code="$2"
  trap '' HUP INT TERM
  cleanup_active_child
  if [[ "$CLEANUP_ACTIVE_PROVEN" != true ]]; then
    note "received $signal_name; cleanup proof failed"
    exit 2
  fi
  note "received $signal_name"
  exit "$exit_code"
}
trap 'on_signal HUP 129' HUP
trap 'on_signal INT 130' INT
trap 'on_signal TERM 143' TERM

fail_case() {
  local case_name="$1"
  local detail="$2"
  note "FAIL $case_name: $detail"
  exit 1
}

guardian_start_ticks() {
  local pid="$1"
  local stderr_path="$2"
  local wait_ms="$3"
  "$PYTHON_BIN" -I -S "$EVIDENCE" process-start-ticks \
    --pid "$pid" \
    --expected-parent-pid "$$" \
    --wait-ms "$wait_ms" \
    --session-leader \
    2>"$stderr_path"
}

remaining_budget_ms() {
  local started_ns="$1"
  local budget_ms="$2"
  local now_ns
  local remaining_ns
  now_ns="$(monotonic_ns)"
  remaining_ns=$((started_ns + budget_ms * 1000000 - now_ns))
  if ((remaining_ns <= 0)); then
    printf '0'
  else
    printf '%d' "$(((remaining_ns + 999999) / 1000000))"
  fi
}

release_guardian_launch() {
  local pid="$1"
  local start_ticks="$2"
  local stage_id="$3"
  local ready_path="$4"
  local release_path="$5"
  local case_dir="$6"
  local wait_ms="$7"
  "$PYTHON_BIN" -I -S "$EVIDENCE" release-process-launch \
    --ready "$ready_path" \
    --output "$release_path" \
    --artifact-root "$ART_DIR" \
    --stage-id "$stage_id" \
    --pid "$pid" \
    --expected-start-ticks "$start_ticks" \
    --expected-parent-pid "$$" \
    --wait-ms "$wait_ms" \
    >"$case_dir/release.stdout" \
    2>"$case_dir/release.stderr"
}

write_watchdog_facts() {
  local output="$1"
  local stage_id="$2"
  local guardian_pid="$3"
  local guardian_ticks="$4"
  local timeout_ms="$5"
  local started_ns="$6"
  local ended_ns="$7"
  local timed_out="$8"
  local term_sent="$9"
  local forced_group_kill="${10}"
  local cleanup_proven="${11}"
  local wrapper_exit="${12}"
  "$PYTHON_BIN" -I -S - \
    "$output" \
    "$stage_id" \
    "$guardian_pid" \
    "$guardian_ticks" \
    "$timeout_ms" \
    "$started_ns" \
    "$ended_ns" \
    "$timed_out" \
    "$term_sent" \
    "$forced_group_kill" \
    "$cleanup_proven" \
    "$wrapper_exit" <<'PY'
import json
import os
import sys

(
    path,
    stage_id,
    guardian_pid,
    guardian_ticks,
    timeout_ms,
    started_ns,
    ended_ns,
    timed_out,
    term_sent,
    forced_group_kill,
    cleanup_proven,
    wrapper_exit,
) = sys.argv[1:]
record = {
    "schema": "fln.evidence-runner-watchdog/1",
    "stage_id": stage_id,
    "guardian_pid": int(guardian_pid),
    "guardian_start_ticks": int(guardian_ticks),
    "timeout_ms": int(timeout_ms),
    "monotonic_start_ns": int(started_ns),
    "monotonic_end_ns": int(ended_ns),
    "duration_ns": int(ended_ns) - int(started_ns),
    "timed_out": timed_out == "true",
    "term_sent": term_sent == "true",
    "forced_group_kill": forced_group_kill == "true",
    "cleanup_proven": cleanup_proven == "true",
    "wrapper_exit": int(wrapper_exit),
}
payload = json.dumps(record, sort_keys=True, separators=(",", ":")).encode()
flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
if hasattr(os, "O_NOFOLLOW"):
    flags |= os.O_NOFOLLOW
descriptor = os.open(path, flags, 0o600)
try:
    os.write(descriptor, payload)
    os.fsync(descriptor)
finally:
    os.close(descriptor)
PY
}

WATCHDOG_EXIT=2
WATCHDOG_TIMED_OUT=false
WATCHDOG_CLEANUP_PROVEN=true
wait_with_outer_watchdog() {
  local guardian_pid="$1"
  local guardian_ticks="$2"
  local timeout_ms="$3"
  local stage_id="$4"
  local readiness_path="$5"
  local case_dir="$6"
  local started_ns="$7"
  local timeout_seconds
  local now_ns
  local remaining_ns
  local remaining_ms
  local completed=""
  local observed_exit=2
  local timer_pid
  local wait_status
  local grace_timer_pid
  local term_sent=false
  local forced_group_kill=false
  local cleanup_proven=true
  local timed_out=false
  local guardian_reaped=false
  local child_pgid=""
  local readiness_status=0
  local ended_ns

  now_ns="$(monotonic_ns)"
  remaining_ns=$((started_ns + timeout_ms * 1000000 - now_ns))
  if ((remaining_ns <= 0)); then
    remaining_ms=0
  else
    remaining_ms=$(((remaining_ns + 999999) / 1000000))
  fi
  printf -v timeout_seconds '%d.%03d' \
    "$((remaining_ms / 1000))" "$((remaining_ms % 1000))"
  "$SLEEP_BIN" "$timeout_seconds" &
  timer_pid=$!
  ACTIVE_TIMER_PID="$timer_pid"
  set +e
  wait -n -p completed "$guardian_pid" "$timer_pid"
  wait_status=$?
  set -e
  if [[ "$completed" == "$guardian_pid" ]]; then
    observed_exit="$wait_status"
    guardian_reaped=true
    kill "$timer_pid" 2>/dev/null || true
    wait "$timer_pid" 2>/dev/null || true
    ACTIVE_TIMER_PID=""
  else
    ACTIVE_TIMER_PID=""
    timed_out=true
    term_sent=true
    "$PYTHON_BIN" -I -S "$EVIDENCE" signal-bound-process \
      --pid "$guardian_pid" \
      --expected-start-ticks "$guardian_ticks" \
      --signal TERM \
      >"$case_dir/watchdog-term.stdout" \
      2>"$case_dir/watchdog-term.stderr" || cleanup_proven=false

    completed=""
    "$SLEEP_BIN" 2 &
    grace_timer_pid=$!
    ACTIVE_TIMER_PID="$grace_timer_pid"
    set +e
    wait -n -p completed "$guardian_pid" "$grace_timer_pid"
    wait_status=$?
    set -e
    if [[ "$completed" == "$guardian_pid" ]]; then
      observed_exit="$wait_status"
      guardian_reaped=true
      kill "$grace_timer_pid" 2>/dev/null || true
      wait "$grace_timer_pid" 2>/dev/null || true
      ACTIVE_TIMER_PID=""
    else
      ACTIVE_TIMER_PID=""
      forced_group_kill=true
      if [[ -s "$readiness_path" ]]; then
        "$PYTHON_BIN" -I -S "$EVIDENCE" emergency-kill \
          --readiness "$readiness_path" \
          --expected-wrapper-pid "$guardian_pid" \
          --expected-stage-id "$stage_id" \
          >"$case_dir/watchdog-emergency.stdout" \
          2>"$case_dir/watchdog-emergency.stderr" || cleanup_proven=false
      fi
      "$PYTHON_BIN" -I -S "$EVIDENCE" kill-bound-group \
        --pid "$guardian_pid" \
        --expected-start-ticks "$guardian_ticks" \
        --expected-parent-pid "$$" \
        >"$case_dir/watchdog-kill.stdout" \
        2>"$case_dir/watchdog-kill.stderr" || cleanup_proven=false
      if bounded_wait_child "$guardian_pid" 5; then
        observed_exit="$BOUNDED_WAIT_EXIT"
        guardian_reaped=true
      else
        cleanup_proven=false
        "$PYTHON_BIN" -I -S "$EVIDENCE" kill-direct-child \
          --pid "$guardian_pid" \
          --expected-parent-pid "$$" \
          --wait-ms 5000 \
          >"$case_dir/watchdog-direct-kill.stdout" \
          2>"$case_dir/watchdog-direct-kill.stderr" || cleanup_proven=false
        if bounded_wait_child "$guardian_pid" 5; then
          observed_exit="$BOUNDED_WAIT_EXIT"
          guardian_reaped=true
        else
          cleanup_proven=false
        fi
      fi
    fi
    if [[ -z "$child_pgid" && -s "$readiness_path" ]]; then
      set +e
      child_pgid="$(
        "$PYTHON_BIN" -I -S - "$readiness_path" <<'PY' 2>/dev/null
import json
import sys
from pathlib import Path

value = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
pid = value.get("child_pgid")
if isinstance(pid, int) and not isinstance(pid, bool) and pid > 1:
    print(pid)
PY
      )"
      readiness_status=$?
      set -e
      if ((readiness_status != 0)); then
        cleanup_proven=false
      fi
    fi
    if ! "$PYTHON_BIN" -I -S "$EVIDENCE" assert-process-group-empty \
        --pgid "$guardian_pid" \
        --wait-ms 5000 \
        >"$case_dir/watchdog-group.stdout" \
        2>"$case_dir/watchdog-group.stderr"; then
      cleanup_proven=false
    fi
    if [[ -n "$child_pgid" ]] \
        && ! "$PYTHON_BIN" -I -S "$EVIDENCE" assert-process-group-empty \
          --pgid "$child_pgid" \
          --wait-ms 5000 \
          >"$case_dir/watchdog-child-group.stdout" \
          2>"$case_dir/watchdog-child-group.stderr"; then
      cleanup_proven=false
    fi
  fi

  if [[ "$guardian_reaped" == true ]]; then
    ACTIVE_PID=""
    ACTIVE_START_TICKS=""
    ACTIVE_STAGE=""
    ACTIVE_READINESS=""
    ACTIVE_RELEASED=0
  fi
  ACTIVE_TIMER_PID=""
  ended_ns="$(monotonic_ns)"
  write_watchdog_facts \
    "$case_dir/watchdog.json" \
    "$stage_id" \
    "$guardian_pid" \
    "$guardian_ticks" \
    "$timeout_ms" \
    "$started_ns" \
    "$ended_ns" \
    "$timed_out" \
    "$term_sent" \
    "$forced_group_kill" \
    "$cleanup_proven" \
    "$observed_exit"
  WATCHDOG_EXIT="$observed_exit"
  WATCHDOG_TIMED_OUT="$timed_out"
  WATCHDOG_CLEANUP_PROVEN="$cleanup_proven"
}

# run_case <case-dir> <stage> <setup-ms> <execution-ms> <exit> <class>
#          <reason> <child-exit|null> <child-signal|null> <exec-status>
#          <readiness-status> <semantic-exits-csv> <exec-errno-name|null>
#          <cancel-signal|null> <errors:empty|nonempty> <argv0> <relation>
#          <planted:true|false> <before-stop-delay-ms> <gate-mode>
#          [supervisor options] -- <target argv...>
run_case() {
  local case_dir="$1"
  local stage_id="$2"
  local setup_timeout_ms="$3"
  local execution_timeout_ms="$4"
  local expected_exit="$5"
  local expected_classification="$6"
  local expected_reason="$7"
  local expected_child_exit="$8"
  local expected_child_signal="$9"
  local expected_exec_status="${10}"
  local expected_readiness_status="${11}"
  local expected_semantic_exits="${12}"
  local expected_exec_errno="${13}"
  local expected_cancel_signal="${14}"
  local expected_errors="${15}"
  local expected_argv0="${16}"
  local expected_relation="${17}"
  local expected_planted="${18}"
  local expected_before_stop_delay_ms="${19}"
  local expected_gate_mode="${20}"
  shift 20

  local metadata="$case_dir/supervisor.json"
  local stdout_artifact="$case_dir/target.stdout"
  local stderr_artifact="$case_dir/target.stderr"
  local readiness="$case_dir/readiness.json"
  local validation="$case_dir/validation.json"
  local launch_ready="$case_dir/launch.ready.json"
  local launch_release="$case_dir/launch.release.json"
  local outer_timeout_ms=$((setup_timeout_ms + execution_timeout_ms + 5000))
  local watchdog_started_ns
  local remaining_ms
  local guardian_pid
  local guardian_ticks
  local actual_exit

  mkdir -p -- "$(dirname "$case_dir")"
  if [[ -e "$case_dir" || -L "$case_dir" ]]; then
    fail_case "$stage_id" "case artifact directory was not fresh"
  fi
  mkdir -- "$case_dir"

  watchdog_started_ns="$(monotonic_ns)"
  "$SETSID_BIN" -- "$PYTHON_BIN" -I -S "$EVIDENCE" run \
    --cwd "$ROOT" \
    --metadata "$metadata" \
    --stdout "$stdout_artifact" \
    --stderr "$stderr_artifact" \
    --readiness "$readiness" \
    --artifact-root "$ART_DIR" \
    --capture-bytes 4096 \
    --output-budget-bytes 65536 \
    --setup-timeout-ms "$setup_timeout_ms" \
    --timeout-ms "$execution_timeout_ms" \
    --grace-ms 250 \
    --stage-id "$stage_id" \
    --launch-ready "$launch_ready" \
    --launch-release "$launch_release" \
    "$@" \
    >"$case_dir/wrapper.stdout" \
    2>"$case_dir/wrapper.stderr" &
  guardian_pid=$!
  ACTIVE_PID="$guardian_pid"
  ACTIVE_STAGE="$stage_id"
  ACTIVE_READINESS="$readiness"
  remaining_ms="$(remaining_budget_ms "$watchdog_started_ns" "$outer_timeout_ms")"
  if ((remaining_ms == 0)); then
    cleanup_active_child
    fail_case "$stage_id" "outer deadline expired before guardian identity binding"
  fi
  if ! guardian_ticks="$(
    guardian_start_ticks \
      "$guardian_pid" "$case_dir/identity.stderr" "$remaining_ms"
  )"; then
    cleanup_active_child
    fail_case "$stage_id" "could not bind the session-leader guardian identity"
  fi
  ACTIVE_START_TICKS="$guardian_ticks"
  remaining_ms="$(remaining_budget_ms "$watchdog_started_ns" "$outer_timeout_ms")"
  if ((remaining_ms == 0)); then
    cleanup_active_child
    fail_case "$stage_id" "outer deadline expired before guardian release"
  fi
  ACTIVE_RELEASED=1
  if ! release_guardian_launch \
      "$guardian_pid" \
      "$guardian_ticks" \
      "$stage_id" \
      "$launch_ready" \
      "$launch_release" \
      "$case_dir" \
      "$remaining_ms"; then
    cleanup_active_child
    fail_case "$stage_id" "could not release the identity-bound guardian"
  fi
  wait_with_outer_watchdog \
    "$guardian_pid" \
    "$guardian_ticks" \
    "$outer_timeout_ms" \
    "$stage_id" \
    "$readiness" \
    "$case_dir" \
    "$watchdog_started_ns"
  actual_exit="$WATCHDOG_EXIT"

  if [[ -s "$metadata" ]] \
      && ! "$PYTHON_BIN" -I -S "$EVIDENCE" validate-supervisor \
      --file "$metadata" \
      --expected-stage-id "$stage_id" \
      --artifact-root "$ART_DIR" \
      --output "$validation" \
      >"$case_dir/validator.stdout" \
      2>"$case_dir/validator.stderr"; then
    fail_case "$stage_id" "validate-supervisor rejected the envelope"
  fi
  if [[ "$WATCHDOG_TIMED_OUT" == true ]]; then
    fail_case "$stage_id" "outer watchdog expired after ${outer_timeout_ms}ms"
  fi
  if [[ "$WATCHDOG_CLEANUP_PROVEN" != true ]]; then
    fail_case "$stage_id" "outer watchdog could not prove process-tree cleanup"
  fi
  [[ -s "$metadata" ]] \
    || fail_case "$stage_id" "real CLI did not publish a supervisor envelope"

  if ! "$PYTHON_BIN" -I -S - \
      "$metadata" \
      "$readiness" \
      "$validation" \
      "$stage_id" \
      "$actual_exit" \
      "$expected_exit" \
      "$expected_classification" \
      "$expected_reason" \
      "$expected_child_exit" \
      "$expected_child_signal" \
      "$expected_exec_status" \
      "$expected_readiness_status" \
      "$expected_semantic_exits" \
      "$expected_exec_errno" \
      "$expected_cancel_signal" \
      "$expected_errors" \
      "$expected_argv0" \
      "$expected_relation" \
      "$expected_planted" \
      "$expected_before_stop_delay_ms" \
      "$expected_gate_mode" \
      >"$case_dir/assertion.json" \
      2>"$case_dir/assertion.stderr" <<'PY'
import json
import sys
from pathlib import Path

(
    metadata_path,
    readiness_path,
    validation_path,
    stage_id,
    actual_exit_raw,
    expected_exit_raw,
    expected_classification,
    expected_reason,
    expected_child_exit_raw,
    expected_child_signal_raw,
    expected_exec_status,
    expected_readiness_status,
    expected_semantic_exits_raw,
    expected_exec_errno,
    expected_cancel_signal_raw,
    expected_errors,
    expected_argv0,
    expected_relation,
    expected_planted_raw,
    expected_before_stop_delay_ms_raw,
    expected_gate_mode,
) = sys.argv[1:]


def load(path: str) -> dict:
    with Path(path).open("r", encoding="utf-8") as handle:
        value = json.load(handle)
    if not isinstance(value, dict):
        raise AssertionError(f"{path}: expected JSON object")
    return value


def optional_int(raw: str) -> int | None:
    return None if raw == "null" else int(raw)


def optional_string(raw: str) -> str | None:
    return None if raw == "null" else raw


def exact(label: str, actual: object, expected: object) -> None:
    if actual != expected:
        raise AssertionError(f"{label}: expected {expected!r}, got {actual!r}")


metadata = load(metadata_path)
readiness = load(readiness_path)
validation = load(validation_path)
watchdog = load(str(Path(metadata_path).parent / "watchdog.json"))
actual_exit = int(actual_exit_raw)
expected_exit = int(expected_exit_raw)
expected_child_exit = optional_int(expected_child_exit_raw)
expected_child_signal = optional_string(expected_child_signal_raw)
expected_cancel_signal = optional_string(expected_cancel_signal_raw)
semantic_exits = (
    [] if not expected_semantic_exits_raw
    else [int(item) for item in expected_semantic_exits_raw.split(",")]
)

exact("shell exit", actual_exit, expected_exit)
exact("metadata schema", metadata.get("schema"), "fln.supervisor/5")
exact("stage", metadata.get("stage_id"), stage_id)
exact("wrapper exit", metadata.get("wrapper_exit"), expected_exit)
exact(
    "classification",
    metadata.get("classification"),
    expected_classification,
)
exact("reason", metadata.get("reason_code"), expected_reason)
exact("child exit", metadata.get("child_exit"), expected_child_exit)
exact("child signal", metadata.get("child_signal"), expected_child_signal)
exact("cancel signal", metadata.get("cancel_signal"), expected_cancel_signal)
exact("semantic exits", metadata.get("semantic_failure_exits"), semantic_exits)
exact("argv[0]", metadata.get("argv", [None])[0], expected_argv0)
exact("argv redaction", metadata.get("argv_redacted"), False)
expected_planted = expected_planted_raw == "true"
if expected_planted_raw not in {"true", "false"}:
    raise AssertionError("expected planted value is not boolean text")
exact("planted", metadata.get("planted"), expected_planted)
sealed_interpreter = metadata.get("sealed_interpreter")
if not isinstance(sealed_interpreter, dict):
    raise AssertionError("sealed_interpreter is not an object")
exact(
    "sealed interpreter flags",
    sealed_interpreter.get("flags"),
    {
        "isolated": True,
        "ignore_environment": True,
        "no_site": True,
        "no_user_site": True,
        "safe_path": True,
    },
)
configuration_names = sealed_interpreter.get("overridden_env")
if expected_reason == "sealed_interpreter_hostile_environment":
    if (
        not isinstance(configuration_names, list)
        or not configuration_names
        or configuration_names != sorted(set(configuration_names))
        or not all(
            isinstance(name, str) and name.startswith("PYTHON")
            for name in configuration_names
        )
    ):
        raise AssertionError(
            "hostile interpreter setup fault lacks exact Python variable names"
        )
else:
    exact("sealed interpreter environment", configuration_names, [])
expected_test_control = {
    "before_stop_delay_ms": int(expected_before_stop_delay_ms_raw),
    "before_release_delay_ms": 0,
    "gate_mode": expected_gate_mode,
    "terminal_delay_ms": 0,
    "terminal_ready_enabled": False,
    "fault_point": "none",
}
exact("test control", metadata.get("test_control"), expected_test_control)
if expected_test_control != {
    "before_stop_delay_ms": 0,
    "before_release_delay_ms": 0,
    "gate_mode": "normal",
    "terminal_delay_ms": 0,
    "terminal_ready_enabled": False,
    "fault_point": "none",
} and not expected_planted:
    raise AssertionError("non-default test control was not planted")

errors = metadata.get("errors")
if not isinstance(errors, list):
    raise AssertionError("metadata errors are not a list")
if expected_errors == "empty":
    exact("errors", errors, [])
elif expected_errors == "nonempty":
    if not errors or not all(isinstance(item, str) and item for item in errors):
        raise AssertionError("expected non-empty structured supervisor errors")
else:
    raise AssertionError(f"unknown expected error mode: {expected_errors}")

phase = metadata.get("phase_timing")
if not isinstance(phase, dict):
    raise AssertionError("phase_timing is not an object")
exact(
    "admission protocol",
    phase.get("admission_protocol"),
    "same_pid_stopped_private_gate_pidfd/1",
)
exact("setup start", phase.get("setup_start_ns"), metadata.get("monotonic_start_ns"))
if phase.get("setup_end_ns") != phase.get("execution_start_ns") \
        and phase.get("execution_start_ns") is not None:
    raise AssertionError("execution did not start at the setup boundary")

target_exec = metadata.get("target_exec")
if not isinstance(target_exec, dict):
    raise AssertionError("target_exec is not an object")
if expected_exec_status == "succeeded_or_unknown":
    if target_exec.get("status") not in {"succeeded", "unknown"}:
        raise AssertionError(
            "target exec status is outside the honest SIGKILL race set"
        )
else:
    exact("target exec status", target_exec.get("status"), expected_exec_status)
if expected_exec_errno == "null":
    exact("target exec failure", target_exec.get("failure"), None)
else:
    failure = target_exec.get("failure")
    if not isinstance(failure, dict):
        raise AssertionError("target exec failure facts are missing")
    exact("exec failure schema", failure.get("schema"), "fln.exec-status/1")
    exact("exec failure status", failure.get("status"), "failed")
    exact("exec failure type", failure.get("error_type"), "FileNotFoundError")
    exact("exec failure errno", failure.get("errno"), 2)
    exact("exec failure errno name", failure.get("errno_name"), expected_exec_errno)

resource = metadata.get("resource")
if not isinstance(resource, dict):
    raise AssertionError("resource facts are not an object")
exact("survivors", resource.get("surviving_pids"), [])
exact(
    "process tree scope",
    resource.get("process_tree_scope"),
    "linux_nested_subreapers_pidfd_procfs_best_effort",
)

exact("watchdog schema", watchdog.get("schema"), "fln.evidence-runner-watchdog/1")
exact("watchdog stage", watchdog.get("stage_id"), stage_id)
exact("watchdog timed out", watchdog.get("timed_out"), False)
exact("watchdog TERM", watchdog.get("term_sent"), False)
exact("watchdog forced kill", watchdog.get("forced_group_kill"), False)
exact("watchdog cleanup", watchdog.get("cleanup_proven"), True)
exact("watchdog wrapper exit", watchdog.get("wrapper_exit"), actual_exit)
if (
    not isinstance(watchdog.get("timeout_ms"), int)
    or isinstance(watchdog.get("timeout_ms"), bool)
    or watchdog["timeout_ms"] <= 0
    or not isinstance(watchdog.get("duration_ns"), int)
    or isinstance(watchdog.get("duration_ns"), bool)
    or watchdog["duration_ns"] < 0
):
    raise AssertionError("watchdog timing facts are malformed")
if watchdog["duration_ns"] > watchdog["timeout_ms"] * 1_000_000 + 250_000_000:
    raise AssertionError("watchdog exceeded its absolute deadline tolerance")

exact("readiness schema", readiness.get("schema"), "fln.supervisor-readiness/3")
exact("readiness stage", readiness.get("stage_id"), stage_id)
exact("readiness status", readiness.get("status"), expected_readiness_status)
for key in (
    "wrapper_pid",
    "wrapper_start_ticks",
    "supervisor_pid",
    "supervisor_start_ticks",
    "monotonic_ns",
):
    value = readiness.get(key)
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise AssertionError(f"readiness {key} is not a positive integer")
if readiness["wrapper_pid"] == readiness["supervisor_pid"]:
    raise AssertionError("real CLI did not retain its outer guardian identity")
exact("watchdog guardian PID", watchdog.get("guardian_pid"), readiness["wrapper_pid"])
exact(
    "watchdog guardian ticks",
    watchdog.get("guardian_start_ticks"),
    readiness["wrapper_start_ticks"],
)

if expected_readiness_status == "ready":
    child_pid = readiness.get("child_pid")
    if (
        not isinstance(child_pid, int)
        or isinstance(child_pid, bool)
        or child_pid <= 1
        or child_pid != readiness.get("child_pgid")
        or child_pid != readiness.get("child_sid")
        or child_pid in {
            readiness.get("wrapper_pid"),
            readiness.get("supervisor_pid"),
        }
    ):
        raise AssertionError("child PID/PGID/SID identity is not exact")
    child_ticks = readiness.get("child_start_ticks")
    if not isinstance(child_ticks, int) or isinstance(child_ticks, bool) \
            or child_ticks <= 0:
        raise AssertionError("child start ticks are not positive")
    exact("readiness timing", readiness["monotonic_ns"], phase.get("readiness_ns"))
    if phase.get("release_decision_ns") is None \
            or phase.get("execution_start_ns") is None:
        raise AssertionError("ready target lacks release/execution timing")
else:
    for key in ("child_pid", "child_pgid", "child_sid", "child_start_ticks"):
        exact(f"failed readiness {key}", readiness.get(key), None)
    exact("failed readiness timing", phase.get("readiness_ns"), None)
    exact("failed readiness release", phase.get("release_decision_ns"), None)
    exact("failed readiness execution", phase.get("execution_start_ns"), None)
    exact("unreleased target", expected_exec_status, "not_released")

if expected_relation == "none":
    pass
elif expected_relation == "setup_exceeds_execution_timeout":
    execution_budget_ns = resource.get("execution_timeout_ms", 0) * 1_000_000
    if phase.get("setup_duration_ns", 0) <= execution_budget_ns:
        raise AssertionError("delayed setup did not exceed the execution timeout")
elif expected_relation == "unreleased":
    exact("unreleased execution", phase.get("execution_start_ns"), None)
    exact("unreleased target status", target_exec.get("status"), "not_released")
else:
    raise AssertionError(f"unknown expected relation: {expected_relation}")

exact("validation schema", validation.get("schema"), "fln.supervisor-validation/1")
exact("validation valid", validation.get("valid"), True)
exact("validation stage", validation.get("stage_id"), stage_id)
print(
    json.dumps(
        {
            "schema": "fln.evidence-runner-assertion/1",
            "stage_id": stage_id,
            "valid": True,
            "wrapper_exit": actual_exit,
            "classification": expected_classification,
            "reason_code": expected_reason,
            "target_exec_status": target_exec.get("status"),
            "readiness_status": expected_readiness_status,
            "surviving_pids": [],
        },
        sort_keys=True,
        separators=(",", ":"),
    )
)
PY
  then
    fail_case "$stage_id" "exact retained-fact assertion failed"
  fi
}

run_family() {
  local family="$1"
  local expected_exit="$2"
  local expected_classification="$3"
  local expected_reason="$4"
  local expected_child_exit="$5"
  local expected_child_signal="$6"
  local expected_exec_status="$7"
  local expected_semantic_exits="$8"
  local expected_argv0="$9"
  shift 9

  local family_root="$ART_DIR/core/$family"
  local family_start_ns
  local family_end_ns
  local iteration
  local stage_id

  note "core $family: $ITERATIONS real CLI iterations"
  family_start_ns="$(monotonic_ns)"
  mkdir -p -- "$family_root"
  for ((iteration = 1; iteration <= ITERATIONS; iteration += 1)); do
    stage_id="stress-$family-$(printf '%03d' "$iteration")"
    run_case \
      "$family_root/$(printf '%03d' "$iteration")" \
      "$stage_id" \
      3000 \
      1000 \
      "$expected_exit" \
      "$expected_classification" \
      "$expected_reason" \
      "$expected_child_exit" \
      "$expected_child_signal" \
      "$expected_exec_status" \
      ready \
      "$expected_semantic_exits" \
      null \
      null \
      empty \
      "$expected_argv0" \
      none \
      false \
      0 \
      normal \
      "$@"
  done
  family_end_ns="$(monotonic_ns)"
  emit_event family_summary \
    --string family "$family" \
    --string status passed \
    --integer expected_exit "$expected_exit" \
    --string expected_classification "$expected_classification" \
    --string expected_reason_code "$expected_reason" \
    --string expected_target_exec_status "$expected_exec_status" \
    --string expected_readiness_status ready \
    --integer iterations "$ITERATIONS" \
    --integer validated_envelopes "$ITERATIONS" \
    --integer elapsed_ms "$(((family_end_ns - family_start_ns) / 1000000))" \
    --string artifact_dir "core/$family"
  note "PASS core $family ($ITERATIONS/$ITERATIONS)"
}

run_focused_case() {
  local focus_name="$1"
  shift
  local expected_exit="$5"
  local expected_classification="$6"
  local expected_reason="$7"
  local expected_exec_status="${10}"
  local expected_readiness_status="${11}"
  local started_ns
  local ended_ns
  note "focused $focus_name"
  started_ns="$(monotonic_ns)"
  run_case "$@"
  ended_ns="$(monotonic_ns)"
  emit_event focused_summary \
    --string focus "$focus_name" \
    --string status passed \
    --integer expected_exit "$expected_exit" \
    --string expected_classification "$expected_classification" \
    --string expected_reason_code "$expected_reason" \
    --string expected_target_exec_status "$expected_exec_status" \
    --string expected_readiness_status "$expected_readiness_status" \
    --integer validated_envelopes 1 \
    --integer elapsed_ms "$(((ended_ns - started_ns) / 1000000))" \
    --string artifact_dir "focused/$focus_name"
  note "PASS focused $focus_name"
}

emit_event run_start \
  --string status started \
  --integer iterations_per_core_family "$ITERATIONS" \
  --integer expected_core_envelopes "$((4 * ITERATIONS))" \
  --integer expected_focused_envelopes 7 \
  --string artifact_root "$ART_DIR" \
  --string source_scope "scripts/evidence.py,scripts/e2e/evidence_runner.sh" \
  --string source_set_sha256 "$SOURCE_SET_SHA256"
RUN_STARTED=1
note "start ($DATA_GRADE): artifacts in $ART_DIR"

SEMANTIC_SEVEN_CODE='raise SystemExit(7)'
SELF_SIGKILL_CODE='import os, signal, time; time.sleep(0.1); os.kill(os.getpid(), signal.SIGKILL)'
SEMANTIC_TWO_CODE='raise SystemExit(2)'

HOSTILE_PYTHON_CONFIGURATION=()
while IFS= read -r environment_name; do
  if [[ "$environment_name" == PYTHON* ]]; then
    HOSTILE_PYTHON_CONFIGURATION+=("$environment_name")
  fi
done < <(compgen -e)
if ((${#HOSTILE_PYTHON_CONFIGURATION[@]} > 0)); then
  run_case \
    "$ART_DIR/setup/hostile-python-configuration" \
    setup-hostile-python-configuration \
    3000 \
    1000 \
    2 \
    internal_fault \
    sealed_interpreter_hostile_environment \
    null \
    null \
    not_released \
    setup_failed \
    "" \
    null \
    null \
    nonempty \
    /usr/bin/true \
    unreleased \
    false \
    0 \
    normal \
    -- \
    /usr/bin/true
  emit_event setup_fault \
    --string classification internal_fault \
    --string reason_code sealed_interpreter_hostile_environment \
    --integer wrapper_exit 2 \
    --integer rejected_channel_count "${#HOSTILE_PYTHON_CONFIGURATION[@]}" \
    --string artifact_dir setup/hostile-python-configuration
  note "SETUP FAULT: hostile Python configuration was refused before target execution"
  exit 2
fi

run_family \
  immediate-true \
  0 \
  pass \
  exit_zero \
  0 \
  null \
  succeeded \
  "" \
  /usr/bin/true \
  -- \
  /usr/bin/true

run_family \
  semantic-exit-7 \
  1 \
  fail \
  child_exit_semantic_failure \
  7 \
  null \
  succeeded \
  7 \
  "$PYTHON_BIN" \
  --semantic-failure-exit 7 \
  -- \
  "$PYTHON_BIN" -I -S -c "$SEMANTIC_SEVEN_CODE"

run_family \
  unexpected-false \
  2 \
  internal_fault \
  unexpected_child_exit \
  1 \
  null \
  succeeded \
  "" \
  /usr/bin/false \
  -- \
  /usr/bin/false

run_family \
  self-sigkill \
  3 \
  inconclusive \
  child_signal_SIGKILL \
  null \
  SIGKILL \
  succeeded_or_unknown \
  "" \
  "$PYTHON_BIN" \
  -- \
  "$PYTHON_BIN" -I -S -c "$SELF_SIGKILL_CODE"

run_focused_case delayed-admission \
  "$ART_DIR/focused/delayed-admission" \
  focused-delayed-admission \
  5000 \
  500 \
  0 \
  pass \
  exit_zero \
  0 \
  null \
  succeeded \
  ready \
  "" \
  null \
  null \
  empty \
  /usr/bin/true \
  setup_exceeds_execution_timeout \
  true \
  1000 \
  normal \
  --planted \
  --test-before-stop-delay-ms 1000 \
  -- \
  /usr/bin/true

run_focused_case never-stop-setup-timeout \
  "$ART_DIR/focused/never-stop-setup-timeout" \
  focused-never-stop-setup-timeout \
  100 \
  50 \
  3 \
  inconclusive \
  setup_timeout \
  null \
  SIGKILL \
  not_released \
  setup_timeout \
  "" \
  null \
  null \
  empty \
  "$PYTHON_BIN" \
  unreleased \
  true \
  0 \
  never_stop \
  --planted \
  --test-gate-mode never_stop \
  -- \
  "$PYTHON_BIN" -I -S -c "$SEMANTIC_SEVEN_CODE"

run_focused_case exit-before-stop \
  "$ART_DIR/focused/exit-before-stop" \
  focused-exit-before-stop \
  500 \
  50 \
  2 \
  internal_fault \
  supervisor_or_capture_failure \
  2 \
  null \
  not_released \
  setup_failed \
  "" \
  null \
  null \
  nonempty \
  /usr/bin/true \
  unreleased \
  true \
  0 \
  exit_before_stop \
  --planted \
  --test-gate-mode exit_before_stop \
  -- \
  /usr/bin/true

run_focused_case die-after-stop \
  "$ART_DIR/focused/die-after-stop" \
  focused-die-after-stop \
  500 \
  500 \
  3 \
  inconclusive \
  child_signal_SIGKILL \
  null \
  SIGKILL \
  unknown \
  ready \
  "" \
  null \
  null \
  empty \
  /usr/bin/true \
  none \
  true \
  0 \
  die_after_stop \
  --planted \
  --test-gate-mode die_after_stop \
  -- \
  /usr/bin/true

MISSING_EXECUTABLE="$ART_DIR/focused/missing-executable/absent-target"
run_focused_case missing-executable \
  "$ART_DIR/focused/missing-executable" \
  focused-missing-executable \
  500 \
  500 \
  2 \
  internal_fault \
  target_exec_failure \
  2 \
  null \
  failed \
  ready \
  2 \
  ENOENT \
  null \
  empty \
  "$MISSING_EXECUTABLE" \
  none \
  false \
  0 \
  normal \
  --semantic-failure-exit 2 \
  -- \
  "$MISSING_EXECUTABLE"

run_focused_case actual-semantic-exit-2 \
  "$ART_DIR/focused/actual-semantic-exit-2" \
  focused-actual-semantic-exit-2 \
  500 \
  500 \
  1 \
  fail \
  child_exit_semantic_failure \
  2 \
  null \
  succeeded \
  ready \
  2 \
  null \
  null \
  empty \
  "$PYTHON_BIN" \
  none \
  false \
  0 \
  normal \
  --semantic-failure-exit 2 \
  -- \
  "$PYTHON_BIN" -I -S -c "$SEMANTIC_TWO_CODE"

run_prerelease_cancellation() {
  local focus_name="pre-release-cancellation"
  local case_dir="$ART_DIR/focused/$focus_name"
  local stage_id="focused-pre-release-cancellation"
  local launch_ready="$case_dir/launch.ready.json"
  local launch_release="$case_dir/launch.release.json"
  local target_marker="$case_dir/target-executed.marker"
  local metadata="$case_dir/supervisor.json"
  local readiness="$case_dir/readiness.json"
  local guardian_pid
  local guardian_ticks
  local ready_ticks
  local remaining_ms
  local actual_exit
  local started_ns
  local ended_ns
  local outer_timeout_ms=10500

  note "focused $focus_name"
  started_ns="$(monotonic_ns)"
  mkdir -p -- "$(dirname "$case_dir")"
  if [[ -e "$case_dir" || -L "$case_dir" ]]; then
    fail_case "$stage_id" "case artifact directory was not fresh"
  fi
  mkdir -- "$case_dir"

  set +e
  "$SETSID_BIN" -- "$PYTHON_BIN" -I -S "$EVIDENCE" run \
    --cwd "$ROOT" \
    --metadata "$metadata" \
    --stdout "$case_dir/target.stdout" \
    --stderr "$case_dir/target.stderr" \
    --readiness "$readiness" \
    --artifact-root "$ART_DIR" \
    --capture-bytes 4096 \
    --output-budget-bytes 65536 \
    --setup-timeout-ms 5000 \
    --timeout-ms 500 \
    --grace-ms 250 \
    --stage-id "$stage_id" \
    --planted \
    --launch-ready "$launch_ready" \
    --launch-release "$launch_release" \
    --test-before-stop-delay-ms 1500 \
    -- \
    "$PYTHON_BIN" -I -S -c \
      'from pathlib import Path; import sys; Path(sys.argv[1]).write_text("released\n", encoding="utf-8")' \
      "$target_marker" \
    >"$case_dir/wrapper.stdout" \
    2>"$case_dir/wrapper.stderr" &
  guardian_pid=$!
  set -e
  ACTIVE_PID="$guardian_pid"
  ACTIVE_STAGE="$stage_id"
  ACTIVE_READINESS="$readiness"

  remaining_ms="$(remaining_budget_ms "$started_ns" "$outer_timeout_ms")"
  if ((remaining_ms == 0)); then
    cleanup_active_child
    fail_case "$stage_id" "outer deadline expired before guardian identity binding"
  fi
  if ! guardian_ticks="$(
    guardian_start_ticks \
      "$guardian_pid" "$case_dir/identity.stderr" "$remaining_ms"
  )"; then
    cleanup_active_child
    fail_case "$stage_id" "could not bind the session-leader guardian identity"
  fi
  ACTIVE_START_TICKS="$guardian_ticks"
  remaining_ms="$(remaining_budget_ms "$started_ns" "$outer_timeout_ms")"
  if ((remaining_ms == 0)); then
    cleanup_active_child
    fail_case "$stage_id" "outer deadline expired before launch readiness"
  fi
  if ! ready_ticks="$(
    "$PYTHON_BIN" -I -S - \
      "$launch_ready" "$guardian_pid" "$stage_id" "$remaining_ms" <<'PY'
import json
import sys
import time
from pathlib import Path

path = Path(sys.argv[1])
expected_pid = int(sys.argv[2])
expected_stage = sys.argv[3]
deadline = time.monotonic() + int(sys.argv[4]) / 1000
while True:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        if time.monotonic() >= deadline:
            raise SystemExit("guardian launch readiness timed out")
        time.sleep(0.005)
        continue
    expected = {
        "schema": "fln.guardian-launch/1",
        "status": "awaiting_release",
        "stage_id": expected_stage,
        "guardian_pid": expected_pid,
    }
    if any(value.get(key) != item for key, item in expected.items()):
        raise SystemExit("guardian launch readiness identity mismatch")
    ticks = value.get("guardian_start_ticks")
    if not isinstance(ticks, int) or isinstance(ticks, bool) or ticks <= 0:
        raise SystemExit("guardian launch start ticks are malformed")
    print(ticks)
    break
PY
  )"; then
    cleanup_active_child
    fail_case "$stage_id" "could not bind the closed guardian launch gate"
  fi
  if [[ "$ready_ticks" != "$guardian_ticks" ]]; then
    cleanup_active_child
    fail_case "$stage_id" "launch readiness disagreed with bound guardian lifetime"
  fi

  if ! "$PYTHON_BIN" -I -S "$EVIDENCE" signal-bound-process \
      --pid "$guardian_pid" \
      --expected-start-ticks "$guardian_ticks" \
      --signal TERM \
      >"$case_dir/signal.stdout" \
      2>"$case_dir/signal.stderr"; then
    cleanup_active_child
    fail_case "$stage_id" "could not queue identity-bound pre-release SIGTERM"
  fi
  remaining_ms="$(remaining_budget_ms "$started_ns" "$outer_timeout_ms")"
  if ((remaining_ms == 0)); then
    cleanup_active_child
    fail_case "$stage_id" "outer deadline expired before signalled guardian release"
  fi
  ACTIVE_RELEASED=1
  if ! release_guardian_launch \
      "$guardian_pid" \
      "$guardian_ticks" \
      "$stage_id" \
      "$launch_ready" \
      "$launch_release" \
      "$case_dir" \
      "$remaining_ms"; then
    cleanup_active_child
    fail_case "$stage_id" "could not release the signalled guardian"
  fi

  wait_with_outer_watchdog \
    "$guardian_pid" \
    "$guardian_ticks" \
    "$outer_timeout_ms" \
    "$stage_id" \
    "$readiness" \
    "$case_dir" \
    "$started_ns"
  actual_exit="$WATCHDOG_EXIT"
  if [[ -e "$target_marker" || -L "$target_marker" ]]; then
    fail_case "$stage_id" "target marker proves pre-release execution"
  fi

  if [[ -s "$metadata" ]] \
      && ! "$PYTHON_BIN" -I -S "$EVIDENCE" validate-supervisor \
      --file "$metadata" \
      --expected-stage-id "$stage_id" \
      --artifact-root "$ART_DIR" \
      --output "$case_dir/validation.json" \
      >"$case_dir/validator.stdout" \
      2>"$case_dir/validator.stderr"; then
    fail_case "$stage_id" "validate-supervisor rejected cancellation"
  fi
  if [[ "$WATCHDOG_TIMED_OUT" == true ]]; then
    fail_case "$stage_id" "outer watchdog expired after ${outer_timeout_ms}ms"
  fi
  if [[ "$WATCHDOG_CLEANUP_PROVEN" != true ]]; then
    fail_case "$stage_id" "outer watchdog could not prove process-tree cleanup"
  fi
  [[ -s "$metadata" ]] \
    || fail_case "$stage_id" "real CLI did not publish a cancellation envelope"

  if ! "$PYTHON_BIN" -I -S - \
      "$metadata" \
      "$readiness" \
      "$case_dir/validation.json" \
      "$stage_id" \
      "$actual_exit" \
      4 \
      cancelled \
      signal_SIGTERM \
      null \
      SIGKILL \
      not_released \
      setup_cancelled \
      "" \
      null \
      SIGTERM \
      empty \
      "$PYTHON_BIN" \
      unreleased \
      >"$case_dir/assertion.json" \
      2>"$case_dir/assertion.stderr" <<'PY'
import json
import sys
from pathlib import Path

(
    metadata_path,
    readiness_path,
    validation_path,
    stage_id,
    actual_exit_raw,
    expected_exit_raw,
    expected_classification,
    expected_reason,
    expected_child_exit_raw,
    expected_child_signal_raw,
    expected_exec_status,
    expected_readiness_status,
    expected_semantic_exits_raw,
    expected_exec_errno,
    expected_cancel_signal_raw,
    expected_errors,
    expected_argv0,
    expected_relation,
) = sys.argv[1:]


def load(path: str) -> dict:
    with Path(path).open("r", encoding="utf-8") as handle:
        value = json.load(handle)
    if not isinstance(value, dict):
        raise AssertionError(f"{path}: expected JSON object")
    return value


metadata = load(metadata_path)
readiness = load(readiness_path)
validation = load(validation_path)
watchdog = load(str(Path(metadata_path).parent / "watchdog.json"))
expected_exit = int(expected_exit_raw)
checks = {
    "shell exit": (int(actual_exit_raw), expected_exit),
    "metadata schema": (metadata.get("schema"), "fln.supervisor/5"),
    "stage": (metadata.get("stage_id"), stage_id),
    "wrapper exit": (metadata.get("wrapper_exit"), expected_exit),
    "classification": (metadata.get("classification"), expected_classification),
    "reason": (metadata.get("reason_code"), expected_reason),
    "child exit": (metadata.get("child_exit"), None),
    "child signal": (metadata.get("child_signal"), expected_child_signal_raw),
    "cancel signal": (metadata.get("cancel_signal"), expected_cancel_signal_raw),
    "semantic exits": (metadata.get("semantic_failure_exits"), []),
    "argv[0]": (metadata.get("argv", [None])[0], expected_argv0),
    "planted": (metadata.get("planted"), True),
    "test control": (
        metadata.get("test_control"),
        {
            "before_stop_delay_ms": 1500,
            "before_release_delay_ms": 0,
            "gate_mode": "normal",
            "terminal_delay_ms": 0,
            "terminal_ready_enabled": False,
            "fault_point": "none",
        },
    ),
    "errors": (metadata.get("errors"), []),
    "target exec": (metadata.get("target_exec", {}).get("status"), expected_exec_status),
    "target exec failure": (metadata.get("target_exec", {}).get("failure"), None),
    "survivors": (metadata.get("resource", {}).get("surviving_pids"), []),
    "scope": (
        metadata.get("resource", {}).get("process_tree_scope"),
        "linux_nested_subreapers_pidfd_procfs_best_effort",
    ),
    "readiness schema": (readiness.get("schema"), "fln.supervisor-readiness/3"),
    "readiness stage": (readiness.get("stage_id"), stage_id),
    "readiness status": (readiness.get("status"), expected_readiness_status),
    "validation schema": (
        validation.get("schema"),
        "fln.supervisor-validation/1",
    ),
    "validation valid": (validation.get("valid"), True),
    "watchdog schema": (
        watchdog.get("schema"),
        "fln.evidence-runner-watchdog/1",
    ),
    "watchdog stage": (watchdog.get("stage_id"), stage_id),
    "watchdog timed out": (watchdog.get("timed_out"), False),
    "watchdog TERM": (watchdog.get("term_sent"), False),
    "watchdog forced kill": (watchdog.get("forced_group_kill"), False),
    "watchdog cleanup": (watchdog.get("cleanup_proven"), True),
    "watchdog wrapper exit": (watchdog.get("wrapper_exit"), expected_exit),
}
for label, (actual, expected) in checks.items():
    if actual != expected:
        raise AssertionError(f"{label}: expected {expected!r}, got {actual!r}")
sealed_interpreter = metadata.get("sealed_interpreter")
if not isinstance(sealed_interpreter, dict):
    raise AssertionError("sealed_interpreter is not an object")
if sealed_interpreter.get("flags") != {
    "isolated": True,
    "ignore_environment": True,
    "no_site": True,
    "no_user_site": True,
    "safe_path": True,
} or sealed_interpreter.get("overridden_env") != []:
    raise AssertionError("pre-release cancellation lacks sealed interpreter facts")
if (
    not isinstance(watchdog.get("timeout_ms"), int)
    or isinstance(watchdog.get("timeout_ms"), bool)
    or watchdog["timeout_ms"] <= 0
    or not isinstance(watchdog.get("duration_ns"), int)
    or isinstance(watchdog.get("duration_ns"), bool)
    or watchdog["duration_ns"] < 0
    or watchdog["duration_ns"]
    > watchdog["timeout_ms"] * 1_000_000 + 250_000_000
):
    raise AssertionError("pre-release watchdog timing facts are malformed")

phase = metadata.get("phase_timing", {})
if phase.get("admission_protocol") != "same_pid_stopped_private_gate_pidfd/1":
    raise AssertionError("admission protocol mismatch")
for key in ("readiness_ns", "release_decision_ns", "execution_start_ns"):
    if phase.get(key) is not None:
        raise AssertionError(f"pre-release cancellation populated {key}")
for key in ("child_pid", "child_pgid", "child_sid", "child_start_ticks"):
    if readiness.get(key) is not None:
        raise AssertionError(f"pre-release readiness populated {key}")
for key in (
    "wrapper_pid",
    "wrapper_start_ticks",
    "supervisor_pid",
    "supervisor_start_ticks",
    "monotonic_ns",
):
    value = readiness.get(key)
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise AssertionError(f"readiness {key} is not positive")
if readiness["wrapper_pid"] == readiness["supervisor_pid"]:
    raise AssertionError("guardian/supervisor identities collapsed")
if watchdog.get("guardian_pid") != readiness["wrapper_pid"] \
        or watchdog.get("guardian_start_ticks") != readiness["wrapper_start_ticks"]:
    raise AssertionError("watchdog/guardian identity mismatch")

print(
    json.dumps(
        {
            "schema": "fln.evidence-runner-assertion/1",
            "stage_id": stage_id,
            "valid": True,
            "wrapper_exit": expected_exit,
            "classification": expected_classification,
            "reason_code": expected_reason,
            "target_exec_status": expected_exec_status,
            "readiness_status": expected_readiness_status,
            "target_marker_absent": True,
            "surviving_pids": [],
        },
        sort_keys=True,
        separators=(",", ":"),
    )
)
PY
  then
    fail_case "$stage_id" "exact retained cancellation facts failed"
  fi

  ended_ns="$(monotonic_ns)"
  emit_event focused_summary \
    --string focus "$focus_name" \
    --string status passed \
    --integer expected_exit 4 \
    --string expected_classification cancelled \
    --string expected_reason_code signal_SIGTERM \
    --string expected_target_exec_status not_released \
    --string expected_readiness_status setup_cancelled \
    --integer validated_envelopes 1 \
    --integer elapsed_ms "$(((ended_ns - started_ns) / 1000000))" \
    --boolean target_marker_absent true \
    --string artifact_dir "focused/$focus_name"
  note "PASS focused $focus_name"
}

run_prerelease_cancellation

# Keep ordinary cancellation active during source sampling, bundle construction,
# recursive validation, and fsync. Only the final source-bound hardlink commit is
# signal-linearized below.
snapshot_live_sources "$SOURCE_AFTER"
if ! "$CMP_BIN" -s -- "$SOURCE_BEFORE" "$SOURCE_AFTER"; then
  fail_case source-stability "evidence runner sources changed during execution"
fi

TOTAL_ENVELOPES=$((4 * ITERATIONS + 7))
emit_event run_end \
  --string status passed \
  --string verdict pass \
  --integer core_envelopes "$((4 * ITERATIONS))" \
  --integer focused_envelopes 7 \
  --integer validated_envelopes "$TOTAL_ENVELOPES" \
  --string artifact_root "$ART_DIR" \
  --string source_set_sha256 "$SOURCE_SET_SHA256" \
  --boolean source_stable true \
  --string cleanup_status retained_by_policy \
  --string evidence_manifest manifest.json \
  --string bundle_commit bundle.complete.json \
  --string evidence_state pending_bundle_commit
PASS_TERMINAL_PUBLISHED=1

if ! "$PYTHON_BIN" -I -S - \
    "$ART_DIR" \
    "$RUN_ID" \
    "$TOTAL_ENVELOPES" \
    "$SOURCE_SET_SHA256" \
    "$ITERATIONS" \
    "$DATA_GRADE" \
    "$PYTHON_BIN" \
    "$FROZEN_EVIDENCE" \
    "$FROZEN_RUNNER" <<'PY'
import hashlib
import json
import os
import stat
import subprocess
import sys
from pathlib import Path

art_dir = Path(sys.argv[1])
run_id = sys.argv[2]
expected_envelopes = int(sys.argv[3])
expected_source_set = sys.argv[4]
iterations = int(sys.argv[5])
expected_data_grade = sys.argv[6]
python_bin = sys.argv[7]
frozen_evidence = Path(sys.argv[8])
frozen_runner = Path(sys.argv[9])
controls = {
    "manifest.json",
    "manifest.digest",
    "bundle.decision",
    "bundle.complete.json",
    "bundle.failure.json",
}


def canonical(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def write_new(path: Path, data: bytes) -> None:
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(path, flags, 0o600)
    try:
        offset = 0
        while offset < len(data):
            written = os.write(descriptor, data[offset:])
            if written <= 0:
                raise RuntimeError(f"write made no progress: {path}")
            offset += written
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def stable_bytes(path: Path) -> bytes:
    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(path, flags)
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise RuntimeError(f"artifact is not a regular file: {path}")
        chunks = []
        while True:
            block = os.read(descriptor, 1024 * 1024)
            if not block:
                break
            chunks.append(block)
        after = os.fstat(descriptor)
        if (
            before.st_dev,
            before.st_ino,
            before.st_size,
            before.st_mtime_ns,
            before.st_ctime_ns,
        ) != (
            after.st_dev,
            after.st_ino,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        ):
            raise RuntimeError(f"artifact changed while read: {path}")
        return b"".join(chunks)
    finally:
        os.close(descriptor)


records = [
    json.loads(line)
    for line in stable_bytes(art_dir / "run.ndjson").splitlines()
    if line
]
if len(records) < 2:
    raise RuntimeError("run log lacks start and terminal records")
if any(
    not isinstance(record, dict)
    or record.get("schema") != "fln.evidence-runner-stress/1"
    or record.get("run_id") != run_id
    or record.get("data_grade") != expected_data_grade
    or record.get("sequence") != index
    for index, record in enumerate(records)
):
    raise RuntimeError("run log identity or sequence is malformed")
start = records[0]
if (
    start.get("event") != "run_start"
    or start.get("status") != "started"
    or start.get("iterations_per_core_family") != iterations
    or start.get("expected_core_envelopes") != 4 * iterations
    or start.get("expected_focused_envelopes") != 7
    or start.get("artifact_root") != str(art_dir)
    or start.get("source_scope")
    != "scripts/evidence.py,scripts/e2e/evidence_runner.sh"
    or start.get("source_set_sha256") != expected_source_set
):
    raise RuntimeError("run log lacks its start record")

family_specs = {
    "immediate-true": {
        "wrapper_exit": 0,
        "classification": "pass",
        "reason_code": "exit_zero",
        "target_exec_status": "succeeded",
        "child_exit": 0,
        "child_signal": None,
        "semantic_exits": [],
    },
    "semantic-exit-7": {
        "wrapper_exit": 1,
        "classification": "fail",
        "reason_code": "child_exit_semantic_failure",
        "target_exec_status": "succeeded",
        "child_exit": 7,
        "child_signal": None,
        "semantic_exits": [7],
    },
    "unexpected-false": {
        "wrapper_exit": 2,
        "classification": "internal_fault",
        "reason_code": "unexpected_child_exit",
        "target_exec_status": "succeeded",
        "child_exit": 1,
        "child_signal": None,
        "semantic_exits": [],
    },
    "self-sigkill": {
        "wrapper_exit": 3,
        "classification": "inconclusive",
        "reason_code": "child_signal_SIGKILL",
        "target_exec_status": "succeeded_or_unknown",
        "child_exit": None,
        "child_signal": "SIGKILL",
        "semantic_exits": [],
    },
}
focus_specs = {
    "delayed-admission": {
        "directory": "delayed-admission",
        "stage_id": "focused-delayed-admission",
        "wrapper_exit": 0,
        "classification": "pass",
        "reason_code": "exit_zero",
        "target_exec_status": "succeeded",
        "readiness_status": "ready",
        "child_exit": 0,
        "child_signal": None,
        "semantic_exits": [],
        "planted": True,
        "before_stop_delay_ms": 1000,
        "gate_mode": "normal",
    },
    "never-stop-setup-timeout": {
        "directory": "never-stop-setup-timeout",
        "stage_id": "focused-never-stop-setup-timeout",
        "wrapper_exit": 3,
        "classification": "inconclusive",
        "reason_code": "setup_timeout",
        "target_exec_status": "not_released",
        "readiness_status": "setup_timeout",
        "child_exit": None,
        "child_signal": "SIGKILL",
        "semantic_exits": [],
        "planted": True,
        "before_stop_delay_ms": 0,
        "gate_mode": "never_stop",
    },
    "exit-before-stop": {
        "directory": "exit-before-stop",
        "stage_id": "focused-exit-before-stop",
        "wrapper_exit": 2,
        "classification": "internal_fault",
        "reason_code": "supervisor_or_capture_failure",
        "target_exec_status": "not_released",
        "readiness_status": "setup_failed",
        "child_exit": 2,
        "child_signal": None,
        "semantic_exits": [],
        "planted": True,
        "before_stop_delay_ms": 0,
        "gate_mode": "exit_before_stop",
        "errors_nonempty": True,
    },
    "die-after-stop": {
        "directory": "die-after-stop",
        "stage_id": "focused-die-after-stop",
        "wrapper_exit": 3,
        "classification": "inconclusive",
        "reason_code": "child_signal_SIGKILL",
        "target_exec_status": "unknown",
        "readiness_status": "ready",
        "child_exit": None,
        "child_signal": "SIGKILL",
        "semantic_exits": [],
        "planted": True,
        "before_stop_delay_ms": 0,
        "gate_mode": "die_after_stop",
    },
    "missing-executable": {
        "directory": "missing-executable",
        "stage_id": "focused-missing-executable",
        "wrapper_exit": 2,
        "classification": "internal_fault",
        "reason_code": "target_exec_failure",
        "target_exec_status": "failed",
        "readiness_status": "ready",
        "child_exit": 2,
        "child_signal": None,
        "semantic_exits": [2],
    },
    "actual-semantic-exit-2": {
        "directory": "actual-semantic-exit-2",
        "stage_id": "focused-actual-semantic-exit-2",
        "wrapper_exit": 1,
        "classification": "fail",
        "reason_code": "child_exit_semantic_failure",
        "target_exec_status": "succeeded",
        "readiness_status": "ready",
        "child_exit": 2,
        "child_signal": None,
        "semantic_exits": [2],
    },
    "pre-release-cancellation": {
        "directory": "pre-release-cancellation",
        "stage_id": "focused-pre-release-cancellation",
        "wrapper_exit": 4,
        "classification": "cancelled",
        "reason_code": "signal_SIGTERM",
        "target_exec_status": "not_released",
        "readiness_status": "setup_cancelled",
        "child_exit": None,
        "child_signal": "SIGKILL",
        "semantic_exits": [],
        "cancel_signal": "SIGTERM",
        "planted": True,
        "before_stop_delay_ms": 1500,
        "gate_mode": "normal",
    },
}

expected_summaries = []
for family, spec in family_specs.items():
    expected_summaries.append(
        (
            "family_summary",
            family,
            {
                "family": family,
                "status": "passed",
                "expected_exit": spec["wrapper_exit"],
                "expected_classification": spec["classification"],
                "expected_reason_code": spec["reason_code"],
                "expected_target_exec_status": spec["target_exec_status"],
                "expected_readiness_status": "ready",
                "iterations": iterations,
                "validated_envelopes": iterations,
                "artifact_dir": f"core/{family}",
            },
        )
    )
for focus, spec in focus_specs.items():
    expected_summaries.append(
        (
            "focused_summary",
            focus,
            {
                "focus": focus,
                "status": "passed",
                "expected_exit": spec["wrapper_exit"],
                "expected_classification": spec["classification"],
                "expected_reason_code": spec["reason_code"],
                "expected_target_exec_status": spec["target_exec_status"],
                "expected_readiness_status": spec["readiness_status"],
                "validated_envelopes": 1,
                "artifact_dir": f"focused/{spec['directory']}",
            },
        )
    )
if len(records) != len(expected_summaries) + 2:
    raise RuntimeError("run log does not contain the exact summary matrix")
for record, (event, name, expected) in zip(records[1:-1], expected_summaries):
    if record.get("event") != event:
        raise RuntimeError(f"summary event mismatch for {name}")
    for key, value in expected.items():
        if record.get(key) != value:
            raise RuntimeError(f"summary {name} has wrong {key}")

terminal = records[-1]
if (
    terminal.get("event") != "run_end"
    or terminal.get("status") != "passed"
    or terminal.get("verdict") != "pass"
    or terminal.get("core_envelopes") != 4 * iterations
    or terminal.get("focused_envelopes") != 7
    or terminal.get("validated_envelopes") != expected_envelopes
    or terminal.get("artifact_root") != str(art_dir)
    or terminal.get("source_stable") is not True
    or terminal.get("cleanup_status") != "retained_by_policy"
    or terminal.get("source_set_sha256") != expected_source_set
    or terminal.get("evidence_manifest") != "manifest.json"
    or terminal.get("bundle_commit") != "bundle.complete.json"
    or terminal.get("evidence_state") != "pending_bundle_commit"
):
    raise RuntimeError("run terminal contract is incomplete")

source_before = stable_bytes(art_dir / "source.before.sha256")
source_after = stable_bytes(art_dir / "source.after.sha256")
if source_before != source_after:
    raise RuntimeError("source identity changed before bundle finalization")
if hashlib.sha256(source_before).hexdigest() != expected_source_set:
    raise RuntimeError("source-set digest disagrees with the terminal")
source_lines = source_before.decode().splitlines()
if len(source_lines) != 2:
    raise RuntimeError("source manifest does not contain exactly two sources")
expected_frozen_digests = [
    hashlib.sha256(stable_bytes(frozen_evidence)).hexdigest(),
    hashlib.sha256(stable_bytes(frozen_runner)).hexdigest(),
]
for line, expected_digest in zip(source_lines, expected_frozen_digests):
    digest, separator, source_path = line.partition("  ")
    if separator != "  " or not source_path or digest != expected_digest:
        raise RuntimeError("source manifest does not bind the frozen executables")

expected_cases = {}
for family, spec in family_specs.items():
    for iteration in range(1, iterations + 1):
        stage = f"stress-{family}-{iteration:03d}"
        relative = Path("core") / family / f"{iteration:03d}"
        expected_cases[relative] = {
            **spec,
            "stage_id": stage,
            "readiness_status": "ready",
        }
for spec in focus_specs.values():
    relative = Path("focused") / spec["directory"]
    expected_cases[relative] = spec
if len(expected_cases) != expected_envelopes:
    raise RuntimeError("internal expected-case matrix is inconsistent")

for filename in (
    "supervisor.json",
    "validation.json",
    "assertion.json",
    "watchdog.json",
):
    discovered = {
        path.parent.relative_to(art_dir)
        for path in art_dir.rglob(filename)
    }
    if discovered != set(expected_cases):
        raise RuntimeError(f"{filename} path/stage bijection is incomplete")

for relative, spec in expected_cases.items():
    case_dir = art_dir / relative
    supervisor_path = case_dir / "supervisor.json"
    validation_path = case_dir / "validation.json"
    assertion_path = case_dir / "assertion.json"
    watchdog_path = case_dir / "watchdog.json"
    supervisor_data = stable_bytes(supervisor_path)
    supervisor = json.loads(supervisor_data)
    stage = spec["stage_id"]
    if supervisor.get("stage_id") != stage:
        raise RuntimeError(f"supervisor stage/path mismatch: {relative}")
    expected_current = {
        "wrapper_exit": spec["wrapper_exit"],
        "classification": spec["classification"],
        "reason_code": spec["reason_code"],
        "child_exit": spec["child_exit"],
        "child_signal": spec["child_signal"],
        "cancel_signal": spec.get("cancel_signal"),
        "semantic_failure_exits": spec["semantic_exits"],
        "planted": spec.get("planted", False),
    }
    for key, value in expected_current.items():
        if supervisor.get(key) != value:
            raise RuntimeError(f"current supervisor mismatch for {relative}: {key}")
    target_exec = supervisor.get("target_exec", {})
    observed_current_exec = target_exec.get("status")
    expected_current_exec = spec["target_exec_status"]
    if expected_current_exec == "succeeded_or_unknown":
        if observed_current_exec not in {"succeeded", "unknown"}:
            raise RuntimeError(f"current SIGKILL exec status is dishonest: {relative}")
    elif observed_current_exec != expected_current_exec:
        raise RuntimeError(f"current supervisor exec mismatch: {relative}")
    expected_control = {
        "before_stop_delay_ms": spec.get("before_stop_delay_ms", 0),
        "before_release_delay_ms": 0,
        "gate_mode": spec.get("gate_mode", "normal"),
        "terminal_delay_ms": 0,
        "terminal_ready_enabled": False,
        "fault_point": "none",
    }
    if supervisor.get("test_control") != expected_control:
        raise RuntimeError(f"current supervisor test control mismatch: {relative}")
    errors = supervisor.get("errors")
    if not isinstance(errors, list) or (
        spec.get("errors_nonempty", False) and not errors
    ) or (
        not spec.get("errors_nonempty", False) and errors
    ):
        raise RuntimeError(f"current supervisor error facts mismatch: {relative}")
    resource = supervisor.get("resource", {})
    if resource.get("surviving_pids") != []:
        raise RuntimeError(f"current supervisor retained survivors: {relative}")
    phase = supervisor.get("phase_timing", {})
    if phase.get("admission_protocol") \
            != "same_pid_stopped_private_gate_pidfd/1":
        raise RuntimeError(f"current admission protocol mismatch: {relative}")
    readiness = json.loads(stable_bytes(case_dir / "readiness.json"))
    if (
        readiness.get("schema") != "fln.supervisor-readiness/3"
        or readiness.get("stage_id") != stage
        or readiness.get("status") != spec["readiness_status"]
    ):
        raise RuntimeError(f"current readiness mismatch: {relative}")
    if relative == Path("focused/delayed-admission") \
            and phase.get("setup_duration_ns", 0) \
            <= resource.get("execution_timeout_ms", 0) * 1_000_000:
        raise RuntimeError("delayed admission no longer exceeds execution timeout")

    try:
        completed = subprocess.run(
            [
                python_bin,
                "-I",
                "-S",
                str(frozen_evidence),
                "validate-supervisor",
                "--file",
                str(supervisor_path),
                "--expected-stage-id",
                stage,
            ],
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=10,
        )
    except subprocess.TimeoutExpired as error:
        raise RuntimeError(
            f"fresh supervisor validation timed out: {relative}"
        ) from error
    if completed.returncode != 0:
        detail = completed.stderr.decode(errors="replace")[-500:]
        raise RuntimeError(f"fresh supervisor validation failed: {relative}: {detail}")
    retained_validation = stable_bytes(validation_path)
    if completed.stdout != retained_validation:
        raise RuntimeError(f"stale supervisor validation receipt: {relative}")
    validation = json.loads(retained_validation)
    if (
        validation.get("schema") != "fln.supervisor-validation/1"
        or validation.get("valid") is not True
        or validation.get("stage_id") != stage
        or validation.get("bytes") != len(supervisor_data)
        or validation.get("sha256")
        != hashlib.sha256(supervisor_data).hexdigest()
    ):
        raise RuntimeError(f"supervisor validation binding mismatch: {relative}")

    assertion = json.loads(stable_bytes(assertion_path))
    expected_assertion = {
        "schema": "fln.evidence-runner-assertion/1",
        "stage_id": stage,
        "valid": True,
        "wrapper_exit": spec["wrapper_exit"],
        "classification": spec["classification"],
        "reason_code": spec["reason_code"],
        "readiness_status": spec["readiness_status"],
        "surviving_pids": [],
    }
    for key, value in expected_assertion.items():
        if assertion.get(key) != value:
            raise RuntimeError(f"exact assertion mismatch for {relative}: {key}")
    observed_exec = assertion.get("target_exec_status")
    expected_exec = spec["target_exec_status"]
    if expected_exec == "succeeded_or_unknown":
        if observed_exec not in {"succeeded", "unknown"}:
            raise RuntimeError(f"SIGKILL exec status is dishonest: {relative}")
    elif observed_exec != expected_exec:
        raise RuntimeError(f"exact assertion mismatch for {relative}: target exec")
    if relative == Path("focused/pre-release-cancellation") \
            and assertion.get("target_marker_absent") is not True:
        raise RuntimeError("pre-release target marker absence was not retained")

    watchdog = json.loads(stable_bytes(watchdog_path))
    if (
        watchdog.get("schema") != "fln.evidence-runner-watchdog/1"
        or watchdog.get("stage_id") != stage
        or watchdog.get("timed_out") is not False
        or watchdog.get("term_sent") is not False
        or watchdog.get("forced_group_kill") is not False
        or watchdog.get("cleanup_proven") is not True
        or watchdog.get("wrapper_exit") != spec["wrapper_exit"]
    ):
        raise RuntimeError(f"invalid outer watchdog proof: {relative}")

precommit = {
    "schema": "fln.evidence-runner-precommit-validation/1",
    "run_id": run_id,
    "valid": True,
    "validated_envelopes": expected_envelopes,
    "source_set_sha256": expected_source_set,
    "case_matrix": {
        "core_families": list(family_specs),
        "focused_cases": list(focus_specs),
        "iterations_per_core_family": iterations,
    },
    "fresh_validation_count": expected_envelopes,
}
write_new(art_dir / "bundle.precommit.validation.json", canonical(precommit))

entries = []
for path in sorted(art_dir.rglob("*"), key=lambda item: item.as_posix().encode()):
    relative = path.relative_to(art_dir).as_posix()
    if relative in controls:
        continue
    mode = os.lstat(path).st_mode
    if stat.S_ISLNK(mode):
        raise RuntimeError(f"bundle contains a symlink: {relative}")
    if stat.S_ISDIR(mode):
        entries.append(
            {
                "path": relative,
                "role": "directory",
                "bytes": 0,
                "sha256": hashlib.sha256(
                    b"fln-evidence-runner-directory/1"
                ).hexdigest(),
            }
        )
    elif stat.S_ISREG(mode):
        data = stable_bytes(path)
        entries.append(
            {
                "path": relative,
                "role": "file",
                "bytes": len(data),
                "sha256": hashlib.sha256(data).hexdigest(),
            }
        )
    else:
        raise RuntimeError(f"bundle contains a special file: {relative}")

manifest = {
    "schema": "fln.evidence-runner-manifest/1",
    "run_id": run_id,
    "verdict": "pass",
    "source_set_sha256": expected_source_set,
    "artifact_count": len(entries),
    "artifacts": entries,
}
manifest_data = canonical(manifest)
manifest_path = art_dir / "manifest.json"
digest_path = art_dir / "manifest.digest"
write_new(manifest_path, manifest_data)
write_new(
    digest_path,
    f"sha256:{hashlib.sha256(manifest_data).hexdigest()}  manifest.json\n".encode(),
)

for entry in entries:
    if entry["role"] == "file":
        descriptor = os.open(art_dir / entry["path"], os.O_RDONLY | os.O_CLOEXEC)
        try:
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
for path in (manifest_path, digest_path):
    descriptor = os.open(path, os.O_RDONLY | os.O_CLOEXEC)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
for path in sorted(
    (item for item in art_dir.rglob("*") if item.is_dir()),
    key=lambda item: len(item.parts),
    reverse=True,
):
    descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)

decision = {
    "schema": "fln.evidence-runner-bundle-commit/1",
    "status": "committed",
    "run_id": run_id,
    "manifest_sha256": hashlib.sha256(manifest_data).hexdigest(),
    "digest_sha256": hashlib.sha256(stable_bytes(digest_path)).hexdigest(),
    "run_log_sha256": hashlib.sha256(
        stable_bytes(art_dir / "run.ndjson")
    ).hexdigest(),
    "artifact_count": len(entries),
    "precommit_sha256": hashlib.sha256(
        stable_bytes(art_dir / "bundle.precommit.validation.json")
    ).hexdigest(),
}
decision_path = art_dir / "bundle.decision"
write_new(decision_path, canonical(decision))
descriptor = os.open(art_dir, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
try:
    os.fsync(descriptor)
finally:
    os.close(descriptor)
PY
then
  printf '[evidence_runner] INTERNAL FAULT: bundle preparation failed; retained artifacts: %s\n' \
    "$ART_DIR" >&2
  exit 2
fi

if ! "$PYTHON_BIN" -I -S - \
    "$ART_DIR" "$RUN_ID" "$SOURCE_SET_SHA256" >/dev/null <<'PY'
import hashlib
import json
import os
import stat
import sys
from pathlib import Path

art_dir = Path(sys.argv[1])
run_id = sys.argv[2]
expected_source_set = sys.argv[3]
controls = {
    "manifest.json",
    "manifest.digest",
    "bundle.decision",
    "bundle.complete.json",
    "bundle.failure.json",
}


def stable(path: Path) -> bytes:
    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(path, flags)
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise RuntimeError(f"non-regular committed artifact: {path}")
        chunks = []
        while True:
            block = os.read(descriptor, 1024 * 1024)
            if not block:
                break
            chunks.append(block)
        after = os.fstat(descriptor)
        if (
            before.st_dev,
            before.st_ino,
            before.st_size,
            before.st_mtime_ns,
            before.st_ctime_ns,
        ) != (
            after.st_dev,
            after.st_ino,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        ):
            raise RuntimeError(f"committed artifact changed while read: {path}")
        return b"".join(chunks)
    finally:
        os.close(descriptor)


manifest_data = stable(art_dir / "manifest.json")
manifest = json.loads(manifest_data)
digest_data = stable(art_dir / "manifest.digest")
digest = digest_data.decode()
expected_digest = hashlib.sha256(manifest_data).hexdigest()
if digest != f"sha256:{expected_digest}  manifest.json\n":
    raise RuntimeError("manifest digest sidecar mismatch")
if (
    manifest.get("schema") != "fln.evidence-runner-manifest/1"
    or manifest.get("run_id") != run_id
    or manifest.get("verdict") != "pass"
    or manifest.get("artifact_count") != len(manifest.get("artifacts", []))
):
    raise RuntimeError("committed manifest identity mismatch")

decision_path = art_dir / "bundle.decision"
commit_path = art_dir / "bundle.complete.json"
if commit_path.exists() or commit_path.is_symlink():
    raise RuntimeError("bundle commit marker exists before independent validation")
decision_data = stable(decision_path)
decision = json.loads(decision_data)
if (
    decision.get("schema") != "fln.evidence-runner-bundle-commit/1"
    or decision.get("status") != "committed"
    or decision.get("run_id") != run_id
    or decision.get("manifest_sha256") != expected_digest
    or decision.get("digest_sha256") != hashlib.sha256(digest_data).hexdigest()
    or decision.get("precommit_sha256")
    != hashlib.sha256(
        stable(art_dir / "bundle.precommit.validation.json")
    ).hexdigest()
):
    raise RuntimeError("bundle decision identity mismatch")

observed = []
for path in sorted(art_dir.rglob("*"), key=lambda item: item.as_posix().encode()):
    relative = path.relative_to(art_dir).as_posix()
    if relative in controls:
        continue
    mode = os.lstat(path).st_mode
    if stat.S_ISLNK(mode):
        raise RuntimeError(f"committed bundle contains symlink: {relative}")
    if stat.S_ISDIR(mode):
        observed.append(
            {
                "path": relative,
                "role": "directory",
                "bytes": 0,
                "sha256": hashlib.sha256(
                    b"fln-evidence-runner-directory/1"
                ).hexdigest(),
            }
        )
    elif stat.S_ISREG(mode):
        data = stable(path)
        observed.append(
            {
                "path": relative,
                "role": "file",
                "bytes": len(data),
                "sha256": hashlib.sha256(data).hexdigest(),
            }
        )
    else:
        raise RuntimeError(f"committed bundle contains special file: {relative}")
if observed != manifest.get("artifacts"):
    raise RuntimeError("prepared bundle inventory mismatch")
if decision.get("artifact_count") != len(observed):
    raise RuntimeError("bundle commit artifact count mismatch")
run_log_data = stable(art_dir / "run.ndjson")
if decision.get("run_log_sha256") != hashlib.sha256(run_log_data).hexdigest():
    raise RuntimeError("bundle commit run-log binding mismatch")
records = [
    json.loads(line)
    for line in run_log_data.splitlines()
    if line
]
if records[-1].get("event") != "run_end" \
        or records[-1].get("status") != "passed":
    raise RuntimeError("prepared run terminal is not passing")
if manifest.get("source_set_sha256") != expected_source_set:
    raise RuntimeError("prepared manifest source identity mismatch")
print(
    json.dumps(
        {
            "schema": "fln.evidence-runner-bundle-precommit-validation/1",
            "run_id": run_id,
            "valid": True,
            "manifest_sha256": expected_digest,
            "artifact_count": len(observed),
        },
        sort_keys=True,
        separators=(",", ":"),
    )
)
PY
then
  printf '[evidence_runner] INTERNAL FAULT: read-only bundle validation failed: %s\n' \
    "$ART_DIR" >&2
  exit 2
fi

# This is the only signal-deferred region. The final helper re-reads the live
# sources through stable descriptors, binds them to the exact frozen bytes and
# prepared decision, then performs os.link as its final operation.
trap '' HUP INT TERM
if ! "$PYTHON_BIN" -I -S - \
    "$ART_DIR" \
    "$RUN_ID" \
    "$SOURCE_SET_SHA256" \
    "$EVIDENCE_SOURCE" \
    "$SELF" \
    "$FROZEN_EVIDENCE" \
    "$FROZEN_RUNNER" \
    "$EXECUTED_RUNNER_SOURCE" <<'PY'
import hashlib
import json
import os
import stat
import sys
from pathlib import Path

art_dir = Path(sys.argv[1])
run_id = sys.argv[2]
expected_source_set = sys.argv[3]
live_sources = [Path(sys.argv[4]), Path(sys.argv[5])]
frozen_sources = [Path(sys.argv[6]), Path(sys.argv[7])]
executed_runner_source = Path(sys.argv[8])


def stable(path: Path, *, allow_proc_fd: bool = False) -> bytes:
    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW") and not allow_proc_fd:
        flags |= os.O_NOFOLLOW
    descriptor = os.open(path, flags)
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise RuntimeError(f"non-regular commit input: {path}")
        chunks = []
        while True:
            block = os.read(descriptor, 1024 * 1024)
            if not block:
                break
            chunks.append(block)
        after = os.fstat(descriptor)
        if (
            before.st_dev,
            before.st_ino,
            before.st_size,
            before.st_mtime_ns,
            before.st_ctime_ns,
        ) != (
            after.st_dev,
            after.st_ino,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        ):
            raise RuntimeError(f"commit input changed while read: {path}")
        return b"".join(chunks)
    finally:
        os.close(descriptor)


source_before = stable(art_dir / "source.before.sha256")
source_after = stable(art_dir / "source.after.sha256")
if source_before != source_after \
        or hashlib.sha256(source_before).hexdigest() != expected_source_set:
    raise RuntimeError("source manifests changed before atomic commit")
lines = source_before.decode().splitlines()
if len(lines) != 2:
    raise RuntimeError("source manifest cardinality changed before commit")
for line, live_path, frozen_path in zip(lines, live_sources, frozen_sources):
    live_data = stable(live_path)
    frozen_data = stable(frozen_path)
    if live_data != frozen_data:
        raise RuntimeError(f"live/frozen source mismatch before commit: {live_path}")
    digest, separator, recorded_path = line.partition("  ")
    if (
        separator != "  "
        or recorded_path != str(live_path)
        or digest != hashlib.sha256(live_data).hexdigest()
    ):
        raise RuntimeError(f"source manifest binding mismatch: {live_path}")
if stable(executed_runner_source, allow_proc_fd=True) != stable(frozen_sources[1]):
    raise RuntimeError("Bash's executed runner inode changed before commit")

manifest_data = stable(art_dir / "manifest.json")
digest_data = stable(art_dir / "manifest.digest")
manifest_digest = hashlib.sha256(manifest_data).hexdigest()
if digest_data != f"sha256:{manifest_digest}  manifest.json\n".encode():
    raise RuntimeError("manifest digest changed before commit")
decision_path = art_dir / "bundle.decision"
decision_data = stable(decision_path)
decision = json.loads(decision_data)
if (
    decision.get("schema") != "fln.evidence-runner-bundle-commit/1"
    or decision.get("status") != "committed"
    or decision.get("run_id") != run_id
    or decision.get("manifest_sha256") != manifest_digest
    or decision.get("digest_sha256") != hashlib.sha256(digest_data).hexdigest()
    or decision.get("run_log_sha256")
    != hashlib.sha256(stable(art_dir / "run.ndjson")).hexdigest()
    or decision.get("precommit_sha256")
    != hashlib.sha256(
        stable(art_dir / "bundle.precommit.validation.json")
    ).hexdigest()
):
    raise RuntimeError("bundle decision changed before commit")
commit_path = art_dir / "bundle.complete.json"
failure_path = art_dir / "bundle.failure.json"
for path in (commit_path, failure_path):
    try:
        os.lstat(path)
    except FileNotFoundError:
        continue
    raise RuntimeError(f"terminal bundle path already exists: {path}")
descriptor = os.open(art_dir, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
try:
    os.fsync(descriptor)
finally:
    os.close(descriptor)
os.link(decision_path, commit_path, follow_symlinks=False)
PY
then
  printf '[evidence_runner] INTERNAL FAULT: atomic bundle commit failed: %s\n' \
    "$ART_DIR" >&2
  exit 2
fi

FINALIZED=1
printf '[evidence_runner] PASS (%s validated envelopes, %s); committed artifacts: %s\n' \
  "$TOTAL_ENVELOPES" "$DATA_GRADE" "$ART_DIR" >&2 || true
