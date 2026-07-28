#!/usr/bin/env bash
# Real-path E2E for G0-10's governed dependency closure. The exact child verdict,
# exit, and complete finding set are schema-validated; all fixtures are retained.

set -Eeuo pipefail

PYTHON_BIN="$(command -v python3 || true)"
[ -n "$PYTHON_BIN" ] || {
  echo "[closure_audit] setup failure: python3 is required" >&2
  exit 2
}
PYTHON=("$PYTHON_BIN" -I -S)
HOSTILE_PYTHON_CONFIGURATION=()
while IFS= read -r environment_name; do
  [[ "$environment_name" == PYTHON* ]] \
    && HOSTILE_PYTHON_CONFIGURATION+=("$environment_name")
done < <(compgen -e | LC_ALL=C sort)
if ((${#HOSTILE_PYTHON_CONFIGURATION[@]} > 0)); then
  printf '[closure_audit] setup failure: sealed_interpreter_hostile_environment names=%s\n' \
    "$(IFS=,; printf '%s' "${HOSTILE_PYTHON_CONFIGURATION[*]}")" >&2
  exit 2
fi
command -v setsid >/dev/null 2>&1 || {
  echo "[closure_audit] setup failure: setsid is required" >&2
  exit 2
}

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
EVIDENCE="$ROOT/scripts/evidence.py"
SCHEMA="fln.e2e/2"
BEAD="franken_lean-xwf"
SCENARIO="closure_audit"

# The build gate, taken by this lane rather than by whoever launched it — bead
# franken_lean-gate-lock-producer-optional-o2vz; the core landed verified and unwired at 5a94b48e
# and this is its wiring. One lane only: the rollout to the remaining sites is a separate decision.
# Sits before the EXIT finalizer is installed, so a contention `exit 3` writes no evidence.
# The library is NOT added to this lane's INPUT_PATHS: that would move a governed-set row that
# build_gate_governed_sets.rs pins in both directions, and the gate is not this lane's subject.
# SC1091: the library is checked directly as its own input to check.sh's shellcheck stage.
# shellcheck source=scripts/lib/gate_lock.sh
# shellcheck disable=SC1091
. "$ROOT/scripts/lib/gate_lock.sh"
fln_gate_acquire "$SCENARIO"
RUN_ID="closure-audit-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_ROOT="${FLN_E2E_ART_ROOT:-$ROOT/target/e2e}"
ART_DIR="$ART_ROOT/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
HUMAN="$ART_DIR/human.log"
BUILD_TARGET="${CARGO_TARGET_DIR:-$ROOT/target/cargo}/e2e-structure-guard"
FROZEN_GUARD="$ART_DIR/bin/structure-guard"
CAPTURE_BYTES="${FLN_E2E_CAPTURE_BYTES:-262144}"
OUTPUT_BUDGET_BYTES="${FLN_E2E_OUTPUT_BUDGET_BYTES:-16777216}"
TIMEOUT_MS="${FLN_E2E_TIMEOUT_MS:-300000}"
GRACE_MS="${FLN_E2E_KILL_GRACE_MS:-2000}"
READY_WAIT_MS="${FLN_E2E_READY_WAIT_MS:-30000}"
START_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
SEQ=0
ACTIVE_STEP="setup"
ACTIVE_RUNNER_PID=""
ACTIVE_RUNNER_START_TICKS=""
ACTIVE_READINESS=""
SPAWNING=0
PENDING_SIGNAL=""
PENDING_SIGNAL_EXIT=0
FINAL_SET=0
FINAL_VERDICT="internal_fault"
FINAL_REASON="uncommitted_exit"
FINAL_EXIT=2
TERMINAL_EMITTED=0
FINALIZING=0
FINALIZER_TRANSITION=0
FINALIZER_PID=""
FINALIZER_START_TICKS=""
FINALIZER_CLEANUP_UNPROVEN=0
FINALIZER_WAIT_UNSAFE=0
PROCESS_TREE_CLEANUP_UNPROVEN=0
FINALIZATION_SIGNAL=""
FINALIZATION_SIGNAL_EXIT=0
FINALIZATION_SIGNAL_GENERATION=0
FINALIZATION_DECISION="$ART_DIR/bundle.decision"
FINAL_ROOT_FILE="$ART_DIR/final-root.txt"
EVENT_COMMAND=()
RUN_STARTED=0
ART_DIR_CLAIMED=0
EARLY_STEP=preflight
TEST_EARLY_FAULT="${FLN_CA_TEST_EARLY_FAULT:-}"
INPUT_PATHS=(
  Cargo.toml Cargo.lock SUITE.lock rust-toolchain.toml
  ABI_CONTRACT.md OLEAN_CONTRACT.md ci contracts crates tools
  vendor/NOTICE
  scripts/check.sh scripts/evidence.py scripts/verify_vendor_tree.sh
  scripts/e2e/structure_gate.sh scripts/e2e/closure_audit.sh
  scripts/e2e/structural_gate.sh .github/workflows/ci.yml
)
SUBJECT_PATHS=(
  Cargo.toml Cargo.lock SUITE.lock rust-toolchain.toml
  ABI_CONTRACT.md OLEAN_CONTRACT.md ci contracts crates tools
)
VENDOR_PATH="vendor/lean4-src"
VENDOR_BINDING="$ART_DIR/vendor-binding.json"
HASH_ARGS=()
GOVERNED_ARGS=()
for input_path in "${INPUT_PATHS[@]}"; do
  HASH_ARGS+=(--path "$input_path")
  GOVERNED_ARGS+=(--governed-path "$input_path")
done
SUBJECT_HASH_ARGS=()
for subject_path in "${SUBJECT_PATHS[@]}"; do
  SUBJECT_HASH_ARGS+=(--path "$subject_path")
done

# Hash the complete governed input before creating an artifact directory. A broken
# preflight therefore cannot leave a directory that resembles a typed evidence run.
if ! INPUT_ROOT="$("${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
  --vendor-path "$VENDOR_PATH")"; then
  echo "[closure_audit] setup failure: cannot hash governed inputs" >&2
  exit 2
fi
HOST_FACTS_JSON="$("${PYTHON[@]}" - <<'PY'
import json, platform
print(json.dumps({
    "machine": platform.machine(),
    "python": platform.python_version(),
    "release": platform.release(),
    "system": platform.system(),
}, sort_keys=True, separators=(",", ":")))
PY
)"

note() { printf '[closure_audit] %s\n' "$*" | tee -a "$HUMAN" >&2; }

build_event_command() {
  local sequence="$SEQ"
  SEQ=$((SEQ + 1))
  EVENT_COMMAND=("${PYTHON[@]}" "$EVIDENCE" emit --file "$LOG" --artifact-root "$ART_DIR" \
    --string schema "$SCHEMA" --string run_id "$RUN_ID" --string bead "$BEAD" \
    --string scenario "$SCENARIO" --integer sequence "$sequence" \
    --integer monotonic_ns "$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')" \
    --string wall_time_utc "$(date -u -Is)" "$@")
}

emit_event() {
  build_event_command "$@"
  "${EVENT_COMMAND[@]}"
}

set_final() { FINAL_SET=1; FINAL_VERDICT="$1"; FINAL_REASON="$2"; FINAL_EXIT="$3"; }

# Typed early-envelope faults (bead fln-evidence-runner-bootstrap-btk): any
# failure between artifact-directory creation and the run_start emission still
# finalizes a typed durable PARTIAL bundle — never a complete one.
early_fault() {
  local reason="$1" message="$2"
  echo "[closure_audit] setup failure: $message" >&2
  set_final internal_fault "$reason" 2
  exit 2
}

# shellcheck disable=SC2317
finalize_early_envelope() {
  local observed_rc="$1"
  trap '' HUP INT TERM
  set +e
  if [ "$FINAL_SET" -eq 0 ]; then
    if [ "$observed_rc" -eq 0 ]; then
      set_final internal_fault "early_${EARLY_STEP}_uncommitted_success" 2
    else
      set_final internal_fault "early_${EARLY_STEP}_unexpected_exit" 2
    fi
  fi
  if [ "$ART_DIR_CLAIMED" -eq 1 ] && [ -d "$ART_DIR" ]; then
    note "typed early-envelope fault: step=$EARLY_STEP reason=$FINAL_REASON verdict=$FINAL_VERDICT"
    if ! "${PYTHON[@]}" "$EVIDENCE" publish-partial-bundle --art-dir "$ART_DIR" \
        --run-id "$RUN_ID" --bead "$BEAD" --scenario "$SCENARIO" \
        --step "$EARLY_STEP" --reason "$FINAL_REASON" \
        --classification "$FINAL_VERDICT" \
        --argv-json '["scripts/e2e/closure_audit.sh"]' \
        --cwd "$ROOT"; then
      printf '[closure_audit] INTERNAL FAULT: early evidence bundle did not publish: %s\n' \
        "$ART_DIR" >&2
      exit 2
    fi
    if ! "${PYTHON[@]}" "$EVIDENCE" validate-partial-bundle --art-dir "$ART_DIR" \
        --artifact-root "$ART_DIR" >/dev/null; then
      printf '[closure_audit] INTERNAL FAULT: early evidence bundle did not validate: %s\n' \
        "$ART_DIR" >&2
      exit 2
    fi
    printf '[closure_audit] %s — reason=%s; partial early-envelope evidence: %s\n' \
      "$FINAL_VERDICT" "$FINAL_REASON" "$ART_DIR" >&2
  fi
  exit "$FINAL_EXIT"
}

mark_process_tree_cleanup_unproven() {
  PROCESS_TREE_CLEANUP_UNPROVEN=1
  trap '' HUP INT TERM
  set_final internal_fault process_tree_cleanup_unproven 2
}

# Wait until the nested supervisor has installed handlers and published its exact
# guardian/supervisor/child binding before forwarding a targeted signal.
# shellcheck disable=SC2317
bounded_readiness_wait() {
  local pid="$1" ready_path="$2" limit_ms="$3" state
  local ticks=$(( (limit_ms + 19) / 20 )) index
  for ((index = 0; index < ticks; index += 1)); do
    if [ -s "$ready_path" ]; then return 0; fi
    if [ ! -r "/proc/$pid/stat" ]; then return 1; fi
    state="$(awk '{print $3}' "/proc/$pid/stat" 2>/dev/null || printf X)"
    if [ "$state" = Z ]; then return 1; fi
    sleep 0.02
  done
  return 1
}

# The launch gate guarantees that this direct child has not forked yet.
terminate_unreleased_runner() {
  local pid="$1"
  if ! setsid -- "${PYTHON[@]}" "$EVIDENCE" kill-direct-child --pid "$pid" \
      --expected-parent-pid "$$" --wait-ms 5000; then
    return 1
  fi
  wait "$pid" 2>/dev/null || true
}

release_guardian_launch() {
  local stage="$1" pid="$2" ticks="$3" ready="$4" output="$5"
  for _ in 1 2; do
    if setsid -- "${PYTHON[@]}" "$EVIDENCE" release-process-launch --ready "$ready" \
      --output "$output" --artifact-root "$ART_DIR" --stage-id "$stage" \
      --pid "$pid" --expected-start-ticks "$ticks" \
      --expected-parent-pid "$$" --wait-ms "$READY_WAIT_MS"; then
      return 0
    fi
  done
  return 1
}

# Invoked from signal handling; bounded so publication cannot hang indefinitely.
# shellcheck disable=SC2317
stop_active_runner() {
  local name="$1" pid="$ACTIVE_RUNNER_PID" state cleanup_rc=0 forced=0 guardian_rc=0
  [ -n "$pid" ] || return 0
  if bounded_readiness_wait "$pid" "$ACTIVE_READINESS" "$READY_WAIT_MS" \
      && [ -n "$ACTIVE_RUNNER_START_TICKS" ]; then
    "${PYTHON[@]}" "$EVIDENCE" signal-bound-process --pid "$pid" \
      --expected-start-ticks "$ACTIVE_RUNNER_START_TICKS" --signal "$name" \
      >/dev/null 2>&1 || true
  fi
  for _ in $(seq 1 500); do
    if [ ! -r "/proc/$pid/stat" ]; then break; fi
    state="$(awk '{print $3}' "/proc/$pid/stat" 2>/dev/null || printf X)"
    [ "$state" = Z ] && break
    sleep 0.02
  done
  if [ -r "/proc/$pid/stat" ]; then
    state="$(awk '{print $3}' "/proc/$pid/stat" 2>/dev/null || printf X)"
    if [ "$state" != Z ]; then
      if [ -f "$ACTIVE_READINESS" ]; then
        if ! "${PYTHON[@]}" "$EVIDENCE" emergency-kill --readiness "$ACTIVE_READINESS" \
          --expected-wrapper-pid "$pid" --expected-stage-id "$ACTIVE_STEP" \
          >/dev/null 2>&1; then
          cleanup_rc=1
        else
          forced=1
        fi
      else
        cleanup_rc=1
      fi
    fi
  fi
  if [ "$cleanup_rc" -ne 0 ]; then
    ACTIVE_RUNNER_PID=""
    ACTIVE_RUNNER_START_TICKS=""
    ACTIVE_READINESS=""
    return "$cleanup_rc"
  fi
  wait "$pid" 2>/dev/null || guardian_rc=$?
  if [ "$forced" -eq 0 ]; then
    case "$guardian_rc" in 0|1|3|4) ;; *) cleanup_rc=1 ;; esac
  fi
  ACTIVE_RUNNER_PID=""
  ACTIVE_RUNNER_START_TICKS=""
  ACTIVE_READINESS=""
  return "$cleanup_rc"
}

# Invoked indirectly by trap.
# shellcheck disable=SC2317
on_signal() {
  local name="$1" exit_code="$2"
  if [ "$FINALIZER_TRANSITION" -eq 1 ]; then
    on_finalizer_signal "$name" "$exit_code"
    return 0
  fi
  trap '' HUP INT TERM
  if [ "$SPAWNING" -eq 1 ]; then
    PENDING_SIGNAL="$name"
    PENDING_SIGNAL_EXIT="$exit_code"
    trap 'on_signal HUP 129' HUP
    trap 'on_signal INT 130' INT
    trap 'on_signal TERM 143' TERM
    return 0
  fi
  if [ -n "$ACTIVE_RUNNER_PID" ]; then
    if ! stop_active_runner "$name"; then
      mark_process_tree_cleanup_unproven
      exit 2
    fi
  fi
  set_final cancelled "signal_$name" "$exit_code"
  exit "$exit_code"
}

# shellcheck disable=SC2317
contain_bound_finalizer() {
  if [ -z "$FINALIZER_PID" ] || [ -z "$FINALIZER_START_TICKS" ]; then
    FINALIZER_CLEANUP_UNPROVEN=1
    FINALIZER_WAIT_UNSAFE=1
    mark_process_tree_cleanup_unproven
    return 1
  fi
  if ! setsid -- "${PYTHON[@]}" "$EVIDENCE" kill-bound-group --pid "$FINALIZER_PID" \
      --expected-start-ticks "$FINALIZER_START_TICKS" \
      --expected-parent-pid "$$" >/dev/null 2>&1; then
    FINALIZER_CLEANUP_UNPROVEN=1
    FINALIZER_WAIT_UNSAFE=1
    mark_process_tree_cleanup_unproven
    return 1
  fi
  if ! setsid -- "${PYTHON[@]}" "$EVIDENCE" assert-process-group-empty \
      --pgid "$FINALIZER_PID" --wait-ms 2000 >/dev/null 2>&1; then
    FINALIZER_CLEANUP_UNPROVEN=1
    FINALIZER_WAIT_UNSAFE=1
    mark_process_tree_cleanup_unproven
    return 1
  fi
  return 0
}

# shellcheck disable=SC2317
on_finalizer_signal() {
  local name="$1" exit_code="$2" noclobber_was_set=0
  trap '' HUP INT TERM
  if [ "$PROCESS_TREE_CLEANUP_UNPROVEN" -ne 0 ]; then return 0; fi
  case $- in *C*) noclobber_was_set=1 ;; esac
  set -o noclobber
  : 2>/dev/null > "$FINALIZATION_DECISION" || true
  [ "$noclobber_was_set" -eq 1 ] || set +o noclobber
  FINALIZATION_SIGNAL_GENERATION=$((FINALIZATION_SIGNAL_GENERATION + 1))
  if [ -s "$FINALIZATION_DECISION" ]; then
    trap '' HUP INT TERM
    return 0
  fi
  if [ -z "$FINALIZATION_SIGNAL" ]; then
    FINALIZATION_SIGNAL="$name"
    FINALIZATION_SIGNAL_EXIT="$exit_code"
  fi
  if [ -n "$FINALIZER_PID" ]; then
    if [ -n "$FINALIZER_START_TICKS" ]; then
      if ! contain_bound_finalizer; then return 0; fi
    elif ! terminate_unreleased_runner "$FINALIZER_PID"; then
      FINALIZER_CLEANUP_UNPROVEN=1
      FINALIZER_WAIT_UNSAFE=1
      mark_process_tree_cleanup_unproven
      return 0
    fi
  fi
  trap 'on_finalizer_signal HUP 129' HUP
  trap 'on_finalizer_signal INT 130' INT
  trap 'on_finalizer_signal TERM 143' TERM
}

# shellcheck disable=SC2317
run_finalizer_command() {
  local rc=0 generation binding_valid=1 resume_failed=0 wait_safe=1
  [ "$PROCESS_TREE_CLEANUP_UNPROVEN" -eq 0 ] || return 2
  [ "$FINALIZER_CLEANUP_UNPROVEN" -eq 0 ] || return 2
  [ -z "$FINALIZATION_SIGNAL" ] || return 125
  if [ -s "$FINALIZATION_DECISION" ]; then trap '' HUP INT TERM; fi
  setsid -- "${PYTHON[@]}" "$EVIDENCE" stopped-exec \
    --expected-parent-pid "$$" -- "$@" &
  FINALIZER_PID=$!
  FINALIZER_START_TICKS="$(
    setsid -- "${PYTHON[@]}" "$EVIDENCE" process-start-ticks --pid "$FINALIZER_PID" \
      --expected-parent-pid "$$" --wait-ms "$READY_WAIT_MS" \
      --session-leader --stopped \
      2>/dev/null
  )" || true
  case "$FINALIZER_START_TICKS" in ''|*[!0-9]*) binding_valid=0 ;; esac
  if [ "$binding_valid" -eq 0 ]; then
    # Without the binder's start ticks, only the exact direct-child pidfd helper
    # may act. The launch gate proves this child has not forked or execed yet.
    if ! terminate_unreleased_runner "$FINALIZER_PID"; then
      FINALIZER_CLEANUP_UNPROVEN=1
      FINALIZER_WAIT_UNSAFE=1
      mark_process_tree_cleanup_unproven
    fi
    FINALIZER_PID=""
    FINALIZER_START_TICKS=""
    return 2
  fi
  # A terminal trap can interrupt Bash's command-substitution wait after the
  # isolated binder emitted a valid identity, so the canonical digits are the proof.
  if [ -z "$FINALIZATION_SIGNAL" ]; then
    if ! setsid -- "${PYTHON[@]}" "$EVIDENCE" resume-bound-process \
        --pid "$FINALIZER_PID" \
        --expected-start-ticks "$FINALIZER_START_TICKS" \
        --expected-parent-pid "$$"; then
      contain_bound_finalizer || wait_safe=0
      resume_failed=1
    fi
  fi
  if [ -n "$FINALIZATION_SIGNAL" ] && [ -n "$FINALIZER_START_TICKS" ]; then
    contain_bound_finalizer || wait_safe=0
  fi
  if [ "$wait_safe" -eq 1 ]; then
    while true; do
      generation="$FINALIZATION_SIGNAL_GENERATION"
      wait "$FINALIZER_PID" && rc=0 || rc=$?
      if [ "$FINALIZER_WAIT_UNSAFE" -ne 0 ]; then
        rc=2
        break
      fi
      case "$rc" in
        129|130|143)
          if [ "$generation" -ne "$FINALIZATION_SIGNAL_GENERATION" ]; then
            continue
          fi
          ;;
      esac
      break
    done
  else
    rc=2
  fi
  FINALIZER_PID=""
  FINALIZER_START_TICKS=""
  if [ "$resume_failed" -ne 0 ]; then return 2; fi
  return "$rc"
}

# shellcheck disable=SC2317
abort_if_finalizer_signalled() {
  if [ "$PROCESS_TREE_CLEANUP_UNPROVEN" -ne 0 ]; then
    note "INTERNAL FAULT: process-tree cleanup was not proven"
    exit 2
  fi
  if [ "$FINALIZER_CLEANUP_UNPROVEN" -ne 0 ]; then
    note "INTERNAL FAULT: finalizer cleanup was not proven"
    exit 2
  fi
  if [ -n "$FINALIZATION_SIGNAL" ]; then
    if [ -s "$FINALIZATION_DECISION" ]; then
      return 0
    fi
    note "CANCELLED: signal_$FINALIZATION_SIGNAL won evidence bundle decision: $ART_DIR"
    exit "$FINALIZATION_SIGNAL_EXIT"
  fi
}

# Invoked indirectly by trap.
# shellcheck disable=SC2317
on_exit() {
  local observed_rc="$1" final_root="unavailable" publish_rc=0 hash_rc=0
  local first_divergence=none
  # First, so it survives every later early-exit path; `|| true` because `set -e` is in force.
  fln_gate_release_note "$SCENARIO" || true
  if [ "$RUN_STARTED" -eq 0 ]; then
    trap - EXIT
    finalize_early_envelope "$observed_rc"
  fi
  trap 'on_finalizer_signal HUP 129' HUP
  trap 'on_finalizer_signal INT 130' INT
  trap 'on_finalizer_signal TERM 143' TERM
  trap - EXIT
  set +e
  if [ "$FINALIZING" -ne 0 ]; then exit 2; fi
  FINALIZING=1
  if [ "$FINAL_SET" -eq 0 ]; then
    set_final internal_fault "$([ "$observed_rc" -eq 0 ] && printf uncommitted_success || printf unexpected_shell_exit)" 2
  fi
  run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" \
    "${HASH_ARGS[@]}" --vendor-path "$VENDOR_PATH" \
    --output "$FINAL_ROOT_FILE" --artifact-root "$ART_DIR" 2>/dev/null || hash_rc=$?
  abort_if_finalizer_signalled
  if [ "$hash_rc" -eq 0 ]; then
    IFS= read -r final_root < "$FINAL_ROOT_FILE" || hash_rc=2
  fi
  if [ "$hash_rc" -ne 0 ]; then
    final_root="unavailable"
    set_final internal_fault final_workspace_hash_unavailable 2
  elif [ "$FINAL_VERDICT" = pass ] && [ "$final_root" != "$INPUT_ROOT" ]; then
    set_final inconclusive final_workspace_changed 3
  fi
  if [ "$FINAL_VERDICT" != pass ]; then first_divergence="$FINAL_REASON"; fi
  if [ "$TERMINAL_EMITTED" -eq 0 ]; then
    build_event_command --string event run_end --string verdict "$FINAL_VERDICT" \
      --string reason_code "$FINAL_REASON" --integer process_exit "$FINAL_EXIT" \
      --string active_step "$ACTIVE_STEP" \
      --integer duration_ns "$(( $("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())') - START_NS ))" \
      --string cleanup_status retained_by_policy --string final_state "$final_root" \
      --string logical_root "$final_root" \
      --string receipt_root not_applicable_dependency_closure \
      --string first_divergence "$first_divergence" \
      --string evidence_manifest manifest.json \
      --string bundle_commit bundle.complete.json \
      --string evidence_state pending_bundle_commit
    if run_finalizer_command "${EVENT_COMMAND[@]}"; then
      TERMINAL_EMITTED=1
    else
      publish_rc=2
    fi
    abort_if_finalizer_signalled
  fi
  if [ "$publish_rc" -eq 0 ]; then
    run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" validate-run --file "$LOG" --schema "$SCHEMA" \
      --expected-verdict "$FINAL_VERDICT" --artifact-root "$ART_DIR" \
      --output "$ART_DIR/run.validation.json" || publish_rc=2
    abort_if_finalizer_signalled
  fi
  if [ "$publish_rc" -eq 0 ]; then
    run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" manifest --art-dir "$ART_DIR" \
      --output "$ART_DIR/manifest.json" --digest-output "$ART_DIR/manifest.digest" \
      --run-id "$RUN_ID" --bead "$BEAD" --scenario "$SCENARIO" \
      --verdict "$FINAL_VERDICT" --input-root "$INPUT_ROOT" --final-root "$final_root" \
      || publish_rc=2
    abort_if_finalizer_signalled
  fi
  if [ "$publish_rc" -eq 0 ]; then
    run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" complete-bundle --art-dir "$ART_DIR" \
      --manifest "$ART_DIR/manifest.json" --digest "$ART_DIR/manifest.digest" \
      --output "$ART_DIR/bundle.complete.json" --governed-root "$ROOT" \
      "${GOVERNED_ARGS[@]}" --expected-root "$final_root" \
      --vendor-path "$VENDOR_PATH" || true
    if run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" adopt-bundle --art-dir "$ART_DIR" \
        --manifest "$ART_DIR/manifest.json" --digest "$ART_DIR/manifest.digest" \
        --commit "$ART_DIR/bundle.complete.json" --artifact-root "$ART_DIR" \
        >/dev/null; then
      trap '' HUP INT TERM
    else
      abort_if_finalizer_signalled
      publish_rc=2
    fi
  fi
  if [ "$publish_rc" -ne 0 ]; then
    note "INTERNAL FAULT: incomplete bundle $ART_DIR"
    exit 2
  fi
  if [ "$FINAL_VERDICT" = pass ]; then
    printf '[closure_audit] PASS — committed artifacts and retained fixtures: %s\n' \
      "$ART_DIR" >&2
  fi
  exit "$FINAL_EXIT"
}

# From artifact-directory creation onward every exit is typed: the envelope
# runs under the terminal/finalizer state machine and any pre-run_start fault
# still finalizes a typed durable partial bundle
# (bead fln-evidence-runner-bootstrap-btk).
trap 'on_signal HUP 129' HUP
trap 'on_signal INT 130' INT
trap 'on_signal TERM 143' TERM
trap 'FINALIZER_TRANSITION=1 on_exit "$?"' EXIT
EARLY_STEP=artifact_directory_creation
mkdir -p "$(dirname "$ART_DIR")"
if ! mkdir "$ART_DIR" 2>/dev/null; then
  # The leaf mkdir is the single-writer claim. The losing process owns no
  # artifact path and therefore must not run its already-armed finalizer.
  trap - EXIT
  echo "[closure_audit] evidence directory already claimed: $ART_DIR" >&2
  exit 2
fi
ART_DIR_CLAIMED=1
if [ "$TEST_EARLY_FAULT" = early_signal_hold ]; then
  # Deterministic early-signal window for the deliberate fault scenarios.
  : > "$ART_DIR/early.hold"
  for _ in $(seq 1 3000); do
    if [ -e "$ART_DIR/early.release" ]; then break; fi
    sleep 0.01
  done
fi
EARLY_STEP=vendor_binding
if [ "$TEST_EARLY_FAULT" = vendor_binding ]; then
  # A directory at the output path makes the real write path fail typed.
  mkdir "$VENDOR_BINDING"
fi
"${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ROOT" --vendor-path "$VENDOR_PATH" \
  --output "$VENDOR_BINDING" --artifact-root "$ART_DIR" \
  || early_fault early_vendor_binding_failure "cannot verify the pinned Reference tree"

EARLY_STEP=run_start_emission
if [ "$TEST_EARLY_FAULT" = run_start_emission ]; then
  mkdir "$LOG"
fi
emit_event --new-log --string event run_start \
  --json-value argv '["scripts/e2e/closure_audit.sh"]' --string cwd "$ROOT" \
  --append-string claim_ids FLN-G0-10-DEPENDENCY-CLOSURE \
  --append-string invariant_ids D1 --append-string invariant_ids FL-INV-07 \
  --append-string gate_ids G0-10 \
  --string parity_ledger_row not_applicable_dependency_governance \
  --string epoch lean-v4.32.0 --string mode sound --string profile e2e \
  --string platform "$(uname -srm)" --integer thread_count 1 \
  --json-value host_facts "$HOST_FACTS_JSON" \
  --string seed deterministic-fixture-v1 --string cache_state "${FLN_E2E_CACHE_STATE:-uncontrolled}" \
  --string input_root "$INPUT_ROOT" \
  --producer-binding-root "$ROOT" "${GOVERNED_ARGS[@]}" \
  --string vendor_binding vendor-binding.json \
  --json-value budgets "{\"capture_bytes_per_stream\":$CAPTURE_BYTES,\"output_budget_bytes\":$OUTPUT_BUDGET_BYTES,\"step_timeout_ms\":$TIMEOUT_MS,\"kill_grace_ms\":$GRACE_MS}" \
  || early_fault early_run_start_emission_failure "cannot emit run_start"
EARLY_STEP=human_log
if [ "$TEST_EARLY_FAULT" = human_log ]; then
  mkdir "$HUMAN"
fi
: > "$HUMAN" || early_fault early_human_log_failure "cannot create the human log"
# From here the run log exists with its run_start, so the full finalizer owns
# terminal publication; the early-envelope partial machinery stands down.
RUN_STARTED=1
if [ "$TEST_EARLY_FAULT" = post_run_start_abort ]; then
  # Deliberate internal fault after run_start: an unexpected shell exit must
  # still finalize a complete typed internal_fault bundle.
  exit 9
fi

read_meta_field() {
  "${PYTHON[@]}" - "$1" "$2" <<'PY'
import json, pathlib, sys
value = json.loads(pathlib.Path(sys.argv[1]).read_text())[sys.argv[2]]
print("null" if value is None else value)
PY
}

hash_governed() {
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path "$VENDOR_PATH"
}

hash_subject() {
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$1" "${SUBJECT_HASH_ARGS[@]}"
}

supervise() {
  local step="$1"
  shift
  local -a semantic_args=()
  while [ "${1:-}" = --semantic-failure-exit ]; do
    semantic_args+=(--semantic-failure-exit "$2")
    shift 2
  done
  LAST_META="$ART_DIR/$step.meta.json"
  LAST_OUT="$ART_DIR/$step.out"
  LAST_ERR="$ART_DIR/$step.err"
  LAST_READY="$ART_DIR/$step.ready.json"
  local launch_ready="$ART_DIR/$step.launch.ready.json"
  local launch_release="$ART_DIR/$step.launch.release.json"
  ACTIVE_STEP="$step"
  SPAWNING=1
  setsid -- "${PYTHON[@]}" "$EVIDENCE" run --cwd "$ROOT" --metadata "$LAST_META" \
    --stdout "$LAST_OUT" --stderr "$LAST_ERR" --readiness "$LAST_READY" \
    --launch-ready "$launch_ready" --launch-release "$launch_release" \
    --artifact-root "$ART_DIR" --capture-bytes "$CAPTURE_BYTES" \
    --output-budget-bytes "$OUTPUT_BUDGET_BYTES" --timeout-ms "$TIMEOUT_MS" \
    --grace-ms "$GRACE_MS" --stage-id "$step" "${semantic_args[@]}" -- "$@" &
  ACTIVE_RUNNER_PID=$!
  if ! ACTIVE_RUNNER_START_TICKS="$(
    setsid -- "${PYTHON[@]}" "$EVIDENCE" process-start-ticks --pid "$ACTIVE_RUNNER_PID" \
      --expected-parent-pid "$$" --wait-ms "$READY_WAIT_MS" --session-leader \
      2>/dev/null
  )"; then
    if ! terminate_unreleased_runner "$ACTIVE_RUNNER_PID"; then
      mark_process_tree_cleanup_unproven
      exit 2
    fi
    SPAWNING=0
    ACTIVE_RUNNER_PID=""
    if [ -n "$PENDING_SIGNAL" ]; then
      local pending_name="$PENDING_SIGNAL" pending_exit="$PENDING_SIGNAL_EXIT"
      PENDING_SIGNAL=""
      set_final cancelled "signal_$pending_name" "$pending_exit"
      exit "$pending_exit"
    fi
    set_final internal_fault active_runner_identity_unproven 2
    exit 2
  fi
  if [ -n "$PENDING_SIGNAL" ]; then
    local pending_name="$PENDING_SIGNAL" pending_exit="$PENDING_SIGNAL_EXIT"
    PENDING_SIGNAL=""
    if ! terminate_unreleased_runner "$ACTIVE_RUNNER_PID"; then
      mark_process_tree_cleanup_unproven
      exit 2
    fi
    SPAWNING=0
    ACTIVE_RUNNER_PID=""
    ACTIVE_RUNNER_START_TICKS=""
    set_final cancelled "signal_$pending_name" "$pending_exit"
    exit "$pending_exit"
  fi
  ACTIVE_READINESS="$LAST_READY"
  if ! release_guardian_launch "$step" "$ACTIVE_RUNNER_PID" \
      "$ACTIVE_RUNNER_START_TICKS" "$launch_ready" "$launch_release"; then
    local release_cleanup_failed=0
    if [ -s "$launch_release" ]; then
      if ! stop_active_runner TERM; then
        release_cleanup_failed=1
      fi
    else
      if ! terminate_unreleased_runner "$ACTIVE_RUNNER_PID"; then
        release_cleanup_failed=1
      fi
    fi
    if [ "$release_cleanup_failed" -ne 0 ]; then
      mark_process_tree_cleanup_unproven
      exit 2
    fi
    SPAWNING=0
    ACTIVE_RUNNER_PID=""
    ACTIVE_RUNNER_START_TICKS=""
    if [ -n "$PENDING_SIGNAL" ]; then
      local pending_name="$PENDING_SIGNAL" pending_exit="$PENDING_SIGNAL_EXIT"
      PENDING_SIGNAL=""
      set_final cancelled "signal_$pending_name" "$pending_exit"
      exit "$pending_exit"
    fi
    set_final internal_fault active_runner_launch_unproven 2
    exit 2
  fi
  SPAWNING=0
  if [ -n "$PENDING_SIGNAL" ]; then
    local pending_name="$PENDING_SIGNAL" pending_exit="$PENDING_SIGNAL_EXIT"
    PENDING_SIGNAL=""
    if ! stop_active_runner "$pending_name"; then
      mark_process_tree_cleanup_unproven
      exit 2
    fi
    set_final cancelled "signal_$pending_name" "$pending_exit"
    exit "$pending_exit"
  fi
  if wait "$ACTIVE_RUNNER_PID"; then LAST_RC=0; else LAST_RC=$?; fi
  ACTIVE_RUNNER_PID=""
  ACTIVE_RUNNER_START_TICKS=""
  ACTIVE_READINESS=""
}

record_step() {
  local step="$1" assertion="$2" expected="$3" actual="$4" validation="$5"
  local expected_classification="$6" expected_wrapper="$7" expected_child="$8"
  local subject_root="$9" subject_final_state="${10}"
  local input_root="${11}" final_state="${12}"
  local -a child_field
  if [ "$expected_child" = null ]; then
    child_field=(--null expected_child_exit)
  else
    child_field=(--integer expected_child_exit "$expected_child")
  fi
  emit_event --string event step --string step_id "$step" --string assertion "$assertion" \
    --string expected "$expected" --string actual "$actual" \
    --string input_root "$input_root" --string final_state "$final_state" \
    --string validation_artifact "$validation" \
    --string expected_supervisor_classification "$expected_classification" \
    --integer expected_wrapper_exit "$expected_wrapper" "${child_field[@]}" \
    --string subject_root "$subject_root" --string subject_final_state "$subject_final_state" \
    --json-file supervisor "$LAST_META"
}

inspect_supervisor() {
  local step="$1" expected_class
  if [ ! -f "$LAST_META" ]; then
    set_final internal_fault "$step:missing_supervisor_metadata" 2
    exit 2
  fi
  if ! LAST_CLASSIFICATION="$(read_meta_field "$LAST_META" classification)" || \
     ! LAST_REASON="$(read_meta_field "$LAST_META" reason_code)" || \
     ! LAST_META_WRAPPER="$(read_meta_field "$LAST_META" wrapper_exit)" || \
     ! LAST_CHILD_EXIT="$(read_meta_field "$LAST_META" child_exit)"; then
    set_final internal_fault "$step:malformed_supervisor_metadata" 2
    exit 2
  fi
  case "$LAST_RC" in
    0) expected_class=pass ;;
    1) expected_class=fail ;;
    2) expected_class=internal_fault ;;
    3) expected_class=inconclusive ;;
    4) expected_class=cancelled ;;
    *)
      set_final internal_fault "$step:unknown_wrapper_exit_$LAST_RC" 2
      exit 2
      ;;
  esac
  if [ "$LAST_META_WRAPPER" != "$LAST_RC" ] || \
     [ "$LAST_CLASSIFICATION" != "$expected_class" ]; then
    set_final internal_fault "$step:supervisor_envelope_disagreement" 2
    exit 2
  fi
  case "$LAST_RC" in
    2)
      set_final internal_fault "$step:$LAST_REASON" 2
      exit 2
      ;;
    3)
      set_final inconclusive "$step:$LAST_REASON" 3
      exit 3
      ;;
    4)
      set_final cancelled "$step:$LAST_REASON" 4
      exit 4
      ;;
  esac
}

record_contract_failure() {
  local step="$1" reason="$2" subject_before="$3" subject_after="$4"
  local global_before="$5" global_after="$6"
  note "FAIL step=$step: $reason"
  record_step "$step" fail "$reason" \
    "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" not_applicable \
    "$LAST_CLASSIFICATION" "$LAST_RC" "$LAST_CHILD_EXIT" \
    "$subject_before" "$subject_after" "$global_before" "$global_after"
  set_final fail "$step:$reason" 1
  exit 1
}

snapshot_before() {
  local subject="$1" step="$2"
  if ! SUBJECT_BEFORE="$(hash_subject "$subject")" || \
     ! GLOBAL_BEFORE="$(hash_governed)"; then
    set_final internal_fault "$step:pre_assertion_hash_unavailable" 2
    exit 2
  fi
}

snapshot_after() {
  local subject="$1" step="$2"
  if ! SUBJECT_AFTER="$(hash_subject "$subject")" || \
     ! GLOBAL_AFTER="$(hash_governed)"; then
    set_final internal_fault "$step:post_assertion_hash_unavailable" 2
    exit 2
  fi
}

run_pass_step() {
  local step="$1" subject="$2"
  shift 2
  snapshot_before "$subject" "$step"
  note "running step=$step: $*"
  supervise "$step" "$@"
  inspect_supervisor "$step"
  snapshot_after "$subject" "$step"
  if [ "$LAST_RC" -ne 0 ]; then
    record_contract_failure "$step" unexpected_command_failure \
      "$SUBJECT_BEFORE" "$SUBJECT_AFTER" "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
  fi
  if [ "$SUBJECT_BEFORE" != "$SUBJECT_AFTER" ] || \
     [ "$GLOBAL_BEFORE" != "$GLOBAL_AFTER" ]; then
    note "INCONCLUSIVE step=$step: governed_inputs_changed"
    set_final inconclusive "$step:governed_inputs_changed" 3
    exit 3
  fi
  record_step "$step" pass pass/wrapper=0/child=0 pass/wrapper=0/child=0 \
    not_applicable pass 0 0 "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
    "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
}

guard_step() {
  local step="$1" fixture_root="$2" expected_exit="$3" expected_verdict="$4"; shift 4
  local -a findings=("$@") validate_args=()
  local validation="$ART_DIR/$step.validation.json" expected_classification expected_wrapper
  for finding in "${findings[@]}"; do validate_args+=(--finding "$finding"); done
  if [ "$expected_exit" -eq 0 ]; then
    expected_classification=pass
    expected_wrapper=0
  else
    expected_classification=fail
    expected_wrapper=1
  fi
  snapshot_before "$fixture_root" "$step"
  note "running guard step=$step root=$fixture_root expected=$expected_verdict/$expected_exit"
  if [ "$expected_exit" -eq 0 ]; then
    supervise "$step" "$FROZEN_GUARD" --root "$fixture_root" --robot
  else
    supervise "$step" --semantic-failure-exit "$expected_exit" \
      "$FROZEN_GUARD" --root "$fixture_root" --robot
  fi
  inspect_supervisor "$step"
  snapshot_after "$fixture_root" "$step"
  if [ "$LAST_CLASSIFICATION" != "$expected_classification" ] || \
     [ "$LAST_RC" -ne "$expected_wrapper" ] || \
     [ "$LAST_CHILD_EXIT" != "$expected_exit" ]; then
    record_contract_failure "$step" \
      "supervisor_contract_expected_${expected_classification}_${expected_wrapper}_${expected_exit}" \
      "$SUBJECT_BEFORE" "$SUBJECT_AFTER" "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
  fi
  if [ "$SUBJECT_BEFORE" != "$SUBJECT_AFTER" ] || \
     [ "$GLOBAL_BEFORE" != "$GLOBAL_AFTER" ]; then
    note "INCONCLUSIVE step=$step: governed_inputs_changed"
    set_final inconclusive "$step:governed_inputs_changed" 3
    exit 3
  fi
  if ! "${PYTHON[@]}" "$EVIDENCE" validate-guard --file "$LAST_OUT" \
    --expected-exit "$expected_exit" --expected-verdict "$expected_verdict" \
    --expected-root "$fixture_root" --observed-exit "$LAST_CHILD_EXIT" \
    --artifact-root "$ART_DIR" "${validate_args[@]}" --output "$validation"; then
    record_contract_failure "$step" structure-guard/5_exact_contract_mismatch \
      "$SUBJECT_BEFORE" "$SUBJECT_AFTER" "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
  fi
  record_step "$step" pass \
    "structure-guard/5:$expected_verdict/wrapper=$expected_wrapper/child=$expected_exit" \
    "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
    "${validation#"$ART_DIR"/}" "$expected_classification" "$expected_wrapper" \
    "$expected_exit" "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
    "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
}

copy_workspace() {
  local destination="$1" step="$2"
  mkdir "$destination"
  # One supervised copy plus before/after source hashes prevents a fixture from
  # silently becoming a hybrid of two governed workspace states. Reflinks keep
  # the generated census shards cheap without excluding them from that state.
  run_pass_step "$step" "$ROOT" cp -R --reflink=auto -- \
    "$ROOT/ci" "$ROOT/contracts" "$ROOT/crates" "$ROOT/tools" \
    "$ROOT/Cargo.toml" "$ROOT/Cargo.lock" "$ROOT/SUITE.lock" \
    "$ROOT/rust-toolchain.toml" "$ROOT/ABI_CONTRACT.md" \
    "$ROOT/OLEAN_CONTRACT.md" "$destination/"
}

if [ "$TEST_EARLY_FAULT" = unexpected_first_step ]; then
  # Deliberate unexpected-failure scenario (bead
  # fln-evidence-runner-bootstrap-btk): exit 7 is outside every registered
  # semantic set, so the real step supervision must type internal_fault.
  run_pass_step build_guard "$ROOT" sh -c 'exit 7'
elif [ "$TEST_EARLY_FAULT" = during_first_step_drift ]; then
  # Deliberate concurrent source drift, CLONE-ONLY: the mutator appends to a
  # governed input while the (argv-swapped, cheap) first step runs, so the
  # per-step snapshot law must type inconclusive. The confirmation guard
  # makes accidental use against a real working tree impossible.
  if [ "${FLN_CA_DRIFT_ROOT_CONFIRM:-}" != "$ROOT" ]; then
    note "drift plant refused: FLN_CA_DRIFT_ROOT_CONFIRM does not name this root"
    set_final internal_fault drift_plant_guard_refused 2
    exit 2
  fi
  ( sleep 2; printf '\n' >> "$ROOT/ci/WORKSPACE_GRAPH.txt" ) &
  run_pass_step build_guard "$ROOT" sleep 5
else
  run_pass_step build_guard "$ROOT" \
    --semantic-failure-exit 101 \
    env CARGO_TARGET_DIR="$BUILD_TARGET" cargo build --locked -p structure-guard --quiet
fi
BUILT_GUARD="$BUILD_TARGET/debug/structure-guard"
mkdir "$ART_DIR/bin"
# The positional parameters are intentionally expanded by the supervised child.
# shellcheck disable=SC2016
run_pass_step freeze_guard "$ROOT" bash -c \
  'set -euo pipefail; test -x "$1"; cp -- "$1" "$2"; test -x "$2"' \
  closure-audit-freeze "$BUILT_GUARD" "$FROZEN_GUARD"
guard_step real_closure "$ROOT" 0 pass

SCRATCH_ROOT="$ART_DIR/fixtures"
mkdir "$SCRATCH_ROOT"
SEEDED="$SCRATCH_ROOT/seeded"
copy_workspace "$SEEDED" copy_seeded_fixture
printf '\n[[package]]\nname = "serde"\nversion = "1.0.219"\nsource = "registry+https://github.com/rust-lang/crates.io-index"\nchecksum = "5f0e2c6ed6606019b4e29e69dbaba95b11854410e5347d525002456dbbb786b6"\n' \
  >> "$SEEDED/Cargo.lock"
# The planted registry package makes Cargo.lock disagree with the manifest,
# so the FLN-STRUCT-025 expansion covenant (bead fln-lld) cannot cargo-expand
# the boundary crates and fails closed — two typed findings per boundary
# crate (lib and lib+test-cfg) are part of this fixture's exact contract.
guard_step seeded_registry_package "$SEEDED" 1 fail \
  FLN-STRUCT-018@Cargo.lock \
  FLN-STRUCT-025@crates/fln-unsafe-abi/src \
  FLN-STRUCT-025@crates/fln-unsafe-abi/src \
  FLN-STRUCT-025@crates/fln-unsafe-region/src \
  FLN-STRUCT-025@crates/fln-unsafe-region/src

RECOVERED="$SCRATCH_ROOT/recovered"
copy_workspace "$RECOVERED" copy_recovery_fixture
guard_step closure_recovery "$RECOVERED" 0 pass
guard_step final_real_recheck "$ROOT" 0 pass

ACTIVE_STEP=complete
set_final pass all_scenarios_satisfied 0
exit 0
