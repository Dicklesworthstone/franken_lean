#!/usr/bin/env bash
# Authoritative, no-mock Grimoire environment evidence. The outer run owns the
# fln.e2e/2 lifecycle and references each nested child exactly once.

set -Eeuo pipefail

PYTHON_BIN="$(command -v python3 || true)"
[ -n "$PYTHON_BIN" ] || {
  echo "[env_snapshots] setup failure: python3 is required" >&2
  exit 2
}
PYTHON=("$PYTHON_BIN" -I -S)
HOSTILE_PYTHON_CONFIGURATION=()
while IFS= read -r environment_name; do
  [[ "$environment_name" == PYTHON* ]] \
    && HOSTILE_PYTHON_CONFIGURATION+=("$environment_name")
done < <(compgen -e | LC_ALL=C sort)
if ((${#HOSTILE_PYTHON_CONFIGURATION[@]} > 0)); then
  printf '[env_snapshots] setup failure: sealed_interpreter_hostile_environment names=%s\n' \
    "$(IFS=,; printf '%s' "${HOSTILE_PYTHON_CONFIGURATION[*]}")" >&2
  exit 2
fi
command -v setsid >/dev/null 2>&1 || {
  echo "[env_snapshots] setup failure: setsid is required" >&2
  exit 2
}

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
EVIDENCE="$ROOT/scripts/evidence.py"
SCHEMA="fln.e2e/2"
BEAD="franken_lean-1umc"
SCENARIO="env_snapshots"
RUN_ID="env-snapshots-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_ROOT="${FLN_E2E_ART_ROOT:-$ROOT/target/e2e}"
ART_DIR="$ART_ROOT/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
HUMAN="$ART_DIR/human.log"
VENDOR_PATH="vendor/lean4-src"
VENDOR_BINDING="$ART_DIR/vendor-binding.json"
CAPTURE_BYTES="${FLN_E2E_CAPTURE_BYTES:-262144}"
OUTPUT_BUDGET_BYTES="${FLN_E2E_OUTPUT_BUDGET_BYTES:-67108864}"
TIMEOUT_MS="${FLN_E2E_TIMEOUT_MS:-1200000}"
GRACE_MS="${FLN_E2E_KILL_GRACE_MS:-2000}"
READY_WAIT_MS="${FLN_E2E_READY_WAIT_MS:-30000}"
CACHE_STATE="${FLN_E2E_CACHE_STATE:-uncontrolled}"
START_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
SEQ=0
ACTIVE_STEP=setup
ACTIVE_RUNNER_PID=""
ACTIVE_RUNNER_START_TICKS=""
ACTIVE_READINESS=""
SPAWNING=0
PENDING_SIGNAL=""
PENDING_SIGNAL_EXIT=0
FINAL_SET=0
FINAL_VERDICT=internal_fault
FINAL_REASON=uncommitted_exit
FINAL_EXIT=2
TERMINAL_EMITTED=0
HUMAN_LOG_SEALED=0
FINALIZING=0
RUN_STARTED=0
ART_DIR_CLAIMED=0
EARLY_STEP=preflight
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
INPUT_PATHS=(
  Cargo.toml Cargo.lock SUITE.lock rust-toolchain.toml
  crates/fln-core crates/fln-hash crates/fln-env
  vendor/NOTICE
  scripts/check.sh scripts/evidence.py scripts/verify_vendor_tree.sh
  scripts/e2e/env_snapshots.sh .github/workflows/ci.yml
)
HASH_ARGS=()
GOVERNED_ARGS=()
for input_path in "${INPUT_PATHS[@]}"; do
  HASH_ARGS+=(--path "$input_path")
  GOVERNED_ARGS+=(--governed-path "$input_path")
done

if ! INPUT_ROOT="$(
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path "$VENDOR_PATH"
)"; then
  echo "[env_snapshots] setup failure: cannot hash governed inputs" >&2
  exit 2
fi
HOST_FACTS_JSON="$("${PYTHON[@]}" - <<'PY'
import json
import platform

print(json.dumps({
    "machine": platform.machine(),
    "python": platform.python_version(),
    "release": platform.release(),
    "system": platform.system(),
}, sort_keys=True, separators=(",", ":")))
PY
)"

note() {
  if [ "$HUMAN_LOG_SEALED" -eq 1 ]; then
    printf '[env_snapshots] %s\n' "$*" >&2
    return 0
  fi
  printf '[env_snapshots] %s\n' "$*" | tee -a "$HUMAN" >&2
}

build_event_command() {
  local sequence="$SEQ"
  SEQ=$((SEQ + 1))
  EVENT_COMMAND=("${PYTHON[@]}" "$EVIDENCE" emit --file "$LOG" \
    --artifact-root "$ART_DIR" --string schema "$SCHEMA" \
    --string run_id "$RUN_ID" --string bead "$BEAD" \
    --string scenario "$SCENARIO" --integer sequence "$sequence" \
    --integer monotonic_ns "$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')" \
    --string wall_time_utc "$(date -u -Is)" "$@")
}

emit_event() {
  build_event_command "$@"
  "${EVENT_COMMAND[@]}"
}

set_final() {
  FINAL_SET=1
  FINAL_VERDICT="$1"
  FINAL_REASON="$2"
  FINAL_EXIT="$3"
}

read_meta_field() {
  "${PYTHON[@]}" - "$1" "$2" <<'PY'
import json
import pathlib
import sys

value = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))[sys.argv[2]]
if value is None:
    print("null")
elif value is True:
    print("true")
elif value is False:
    print("false")
else:
    print(value)
PY
}

hash_governed() {
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path "$VENDOR_PATH"
}

hash_subject() {
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$1" --path "$2"
}

mark_process_tree_cleanup_unproven() {
  PROCESS_TREE_CLEANUP_UNPROVEN=1
  trap '' HUP INT TERM
  set_final internal_fault process_tree_cleanup_unproven 2
}

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

terminate_unreleased_runner() {
  local pid="$1"
  setsid -- "${PYTHON[@]}" "$EVIDENCE" kill-direct-child --pid "$pid" \
    --expected-parent-pid "$$" --wait-ms 5000 || return 1
  wait "$pid" 2>/dev/null || true
}

release_guardian_launch() {
  local stage="$1" pid="$2" ticks="$3" ready="$4" output="$5"
  local artifact_root="$6"
  for _ in 1 2; do
    if setsid -- "${PYTHON[@]}" "$EVIDENCE" release-process-launch --ready "$ready" \
      --output "$output" --artifact-root "$artifact_root" --stage-id "$stage" \
      --pid "$pid" --expected-start-ticks "$ticks" \
      --expected-parent-pid "$$" --wait-ms "$READY_WAIT_MS"; then
      return 0
    fi
  done
  return 1
}

stop_active_runner() {
  local name="$1" pid="$ACTIVE_RUNNER_PID" state cleanup_rc=0 forced=0
  local guardian_rc=0
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
      if [ -f "$ACTIVE_READINESS" ] && \
          "${PYTHON[@]}" "$EVIDENCE" emergency-kill --readiness "$ACTIVE_READINESS" \
            --expected-wrapper-pid "$pid" --expected-stage-id "$ACTIVE_STEP" \
            >/dev/null 2>&1; then
        forced=1
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
  if [ -n "$ACTIVE_RUNNER_PID" ] && ! stop_active_runner "$name"; then
    mark_process_tree_cleanup_unproven
    exit 2
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
      contain_bound_finalizer || return 0
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
      --session-leader --stopped 2>/dev/null
  )" || true
  case "$FINALIZER_START_TICKS" in ''|*[!0-9]*) binding_valid=0 ;; esac
  if [ "$binding_valid" -eq 0 ]; then
    if ! terminate_unreleased_runner "$FINALIZER_PID"; then
      FINALIZER_CLEANUP_UNPROVEN=1
      FINALIZER_WAIT_UNSAFE=1
      mark_process_tree_cleanup_unproven
    fi
    FINALIZER_PID=""
    FINALIZER_START_TICKS=""
    return 2
  fi
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
    if [ -s "$FINALIZATION_DECISION" ]; then return 0; fi
    note "CANCELLED: signal_$FINALIZATION_SIGNAL won bundle decision: $ART_DIR"
    exit "$FINALIZATION_SIGNAL_EXIT"
  fi
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
    note "typed early-envelope fault: step=$EARLY_STEP reason=$FINAL_REASON"
    "${PYTHON[@]}" "$EVIDENCE" publish-partial-bundle --art-dir "$ART_DIR" \
      --run-id "$RUN_ID" --bead "$BEAD" --scenario "$SCENARIO" \
      --step "$EARLY_STEP" --reason "$FINAL_REASON" \
      --classification "$FINAL_VERDICT" \
      --argv-json '["scripts/e2e/env_snapshots.sh"]' --cwd "$ROOT" \
      >/dev/null 2>&1 || true
  fi
  exit "$FINAL_EXIT"
}

# shellcheck disable=SC2317
on_exit() {
  local observed_rc="$1" final_root=unavailable first_divergence=none
  local publish_rc=0 hash_rc=0
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
    set_final internal_fault \
      "$([ "$observed_rc" -eq 0 ] && printf uncommitted_success || printf unexpected_shell_exit)" \
      2
  fi
  run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" \
    "${HASH_ARGS[@]}" --vendor-path "$VENDOR_PATH" \
    --output "$FINAL_ROOT_FILE" --artifact-root "$ART_DIR" \
    2>/dev/null || hash_rc=$?
  abort_if_finalizer_signalled
  if [ "$hash_rc" -eq 0 ]; then
    IFS= read -r final_root < "$FINAL_ROOT_FILE" || hash_rc=2
  fi
  if [ "$hash_rc" -ne 0 ]; then
    set_final internal_fault final_workspace_hash_unavailable 2
    final_root=unavailable
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
      --string receipt_root not_applicable_environment_identity_matrix \
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
    run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" validate-run --file "$LOG" \
      --schema "$SCHEMA" --expected-verdict "$FINAL_VERDICT" \
      --artifact-root "$ART_DIR" --output "$ART_DIR/run.validation.json" \
      || publish_rc=2
    abort_if_finalizer_signalled
  fi
  if [ "$publish_rc" -eq 0 ]; then
    note "terminal verdict=$FINAL_VERDICT reason=$FINAL_REASON process_exit=$FINAL_EXIT" \
      || publish_rc=2
    HUMAN_LOG_SEALED=1
    abort_if_finalizer_signalled
  fi
  if [ "$publish_rc" -eq 0 ]; then
    run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" manifest --art-dir "$ART_DIR" \
      --output "$ART_DIR/manifest.json" \
      --digest-output "$ART_DIR/manifest.digest" \
      --run-id "$RUN_ID" --bead "$BEAD" --scenario "$SCENARIO" \
      --verdict "$FINAL_VERDICT" --input-root "$INPUT_ROOT" \
      --final-root "$final_root" || publish_rc=2
    abort_if_finalizer_signalled
  fi
  if [ "$publish_rc" -eq 0 ]; then
    run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" complete-bundle \
      --art-dir "$ART_DIR" --manifest "$ART_DIR/manifest.json" \
      --digest "$ART_DIR/manifest.digest" \
      --output "$ART_DIR/bundle.complete.json" --governed-root "$ROOT" \
      "${GOVERNED_ARGS[@]}" --expected-root "$final_root" \
      --vendor-path "$VENDOR_PATH" || true
    if run_finalizer_command "${PYTHON[@]}" "$EVIDENCE" adopt-bundle \
        --art-dir "$ART_DIR" --manifest "$ART_DIR/manifest.json" \
        --digest "$ART_DIR/manifest.digest" \
        --commit "$ART_DIR/bundle.complete.json" \
        --artifact-root "$ART_DIR" >/dev/null; then
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
    printf '[env_snapshots] PASS — committed evidence: %s\n' "$ART_DIR" >&2
  fi
  exit "$FINAL_EXIT"
}

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
  echo "[env_snapshots] evidence directory already claimed: $ART_DIR" >&2
  exit 2
fi
ART_DIR_CLAIMED=1
EARLY_STEP=vendor_binding
"${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ROOT" \
  --vendor-path "$VENDOR_PATH" --output "$VENDOR_BINDING" \
  --artifact-root "$ART_DIR" || {
    set_final internal_fault early_vendor_binding_failure 2
    exit 2
  }
EARLY_STEP=run_start_emission
emit_event --new-log --string event run_start \
  --json-value argv '["scripts/e2e/env_snapshots.sh"]' --string cwd "$ROOT" \
  --append-string claim_ids franken_lean-1umc-environment-identity \
  --append-string invariant_ids FL-INV-01 \
  --append-string invariant_ids FL-INV-07 \
  --append-string gate_ids W2-environment \
  --append-string gate_ids PG-5 \
  --string parity_ledger_row not_applicable_internal_environment_identity \
  --string epoch lean-v4.32.0 --string mode sound --string profile e2e \
  --string platform "$(uname -srm)" --json-value host_facts "$HOST_FACTS_JSON" \
  --integer thread_count 32 --json-value thread_matrix '[1,8,32]' \
  --string seed environment-identity-v1 --string cache_state "$CACHE_STATE" \
  --string input_root "$INPUT_ROOT" --string vendor_binding vendor-binding.json \
  --json-value budgets "{\"capture_bytes_per_stream\":$CAPTURE_BYTES,\"output_budget_bytes\":$OUTPUT_BUDGET_BYTES,\"step_timeout_ms\":$TIMEOUT_MS,\"kill_grace_ms\":$GRACE_MS,\"readiness_wait_ms\":$READY_WAIT_MS}"
: > "$HUMAN"
RUN_STARTED=1

supervise_in() {
  local artifact_dir="$1" step="$2" cwd="$3"
  shift 3
  local -a semantic_args=()
  while true; do
    case "${1:-}" in
      --semantic-failure-exit)
        semantic_args+=(--semantic-failure-exit "$2")
        shift 2
        ;;
      --planted)
        semantic_args+=(--planted)
        shift
        ;;
      *)
        break
        ;;
    esac
  done
  LAST_META="$artifact_dir/$step.meta.json"
  LAST_OUT="$artifact_dir/$step.out"
  LAST_ERR="$artifact_dir/$step.err"
  LAST_READY="$artifact_dir/$step.ready.json"
  local launch_ready="$artifact_dir/$step.launch.ready.json"
  local launch_release="$artifact_dir/$step.launch.release.json"
  ACTIVE_STEP="$step"
  SPAWNING=1
  setsid -- "${PYTHON[@]}" "$EVIDENCE" run --cwd "$cwd" \
    --metadata "$LAST_META" --stdout "$LAST_OUT" --stderr "$LAST_ERR" \
    --readiness "$LAST_READY" --launch-ready "$launch_ready" \
    --launch-release "$launch_release" --artifact-root "$artifact_dir" \
    --capture-bytes "$CAPTURE_BYTES" \
    --output-budget-bytes "$OUTPUT_BUDGET_BYTES" \
    --timeout-ms "$TIMEOUT_MS" --grace-ms "$GRACE_MS" \
    --stage-id "$step" "${semantic_args[@]}" -- "$@" &
  ACTIVE_RUNNER_PID=$!
  if ! ACTIVE_RUNNER_START_TICKS="$(
    setsid -- "${PYTHON[@]}" "$EVIDENCE" process-start-ticks \
      --pid "$ACTIVE_RUNNER_PID" --expected-parent-pid "$$" \
      --wait-ms "$READY_WAIT_MS" --session-leader 2>/dev/null
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
    set_final internal_fault "$step:active_runner_identity_unproven" 2
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
      "$ACTIVE_RUNNER_START_TICKS" "$launch_ready" "$launch_release" \
      "$artifact_dir"; then
    local release_cleanup_failed=0
    if [ -s "$launch_release" ]; then
      stop_active_runner TERM || release_cleanup_failed=1
    else
      terminate_unreleased_runner "$ACTIVE_RUNNER_PID" || release_cleanup_failed=1
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
    set_final internal_fault "$step:active_runner_launch_unproven" 2
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

supervise() {
  local step="$1"
  shift
  supervise_in "$ART_DIR" "$step" "$ROOT" "$@"
}

inspect_supervisor() {
  local step="$1" expected_class
  if [ ! -s "$LAST_META" ]; then
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
  emit_event --string event step --string step_id "$step" \
    --string assertion "$assertion" --string expected "$expected" \
    --string actual "$actual" --string input_root "$input_root" \
    --string final_state "$final_state" \
    --string validation_artifact "$validation" \
    --string expected_supervisor_classification "$expected_classification" \
    --integer expected_wrapper_exit "$expected_wrapper" "${child_field[@]}" \
    --string subject_root "$subject_root" \
    --string subject_final_state "$subject_final_state" \
    --json-file supervisor "$LAST_META"
}

snapshot_before() {
  local subject_root="$1" subject_path="$2" step="$3"
  if ! SUBJECT_BEFORE="$(hash_subject "$subject_root" "$subject_path")" || \
     ! GLOBAL_BEFORE="$(hash_governed)"; then
    set_final internal_fault "$step:pre_assertion_hash_unavailable" 2
    exit 2
  fi
}

snapshot_after() {
  local subject_root="$1" subject_path="$2" step="$3"
  if ! SUBJECT_AFTER="$(hash_subject "$subject_root" "$subject_path")" || \
     ! GLOBAL_AFTER="$(hash_governed)"; then
    set_final internal_fault "$step:post_assertion_hash_unavailable" 2
    exit 2
  fi
}

require_unchanged() {
  local step="$1"
  if [ "$SUBJECT_BEFORE" != "$SUBJECT_AFTER" ] || \
     [ "$GLOBAL_BEFORE" != "$INPUT_ROOT" ] || \
     [ "$GLOBAL_AFTER" != "$INPUT_ROOT" ]; then
    note "INCONCLUSIVE step=$step: governed_inputs_changed"
    set_final inconclusive "$step:governed_inputs_changed" 3
    exit 3
  fi
}

record_contract_failure() {
  local step="$1" reason="$2"
  note "FAIL step=$step: $reason"
  record_step "$step" fail "$reason" \
    "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
    not_applicable "$LAST_CLASSIFICATION" "$LAST_RC" "$LAST_CHILD_EXIT" \
    "$SUBJECT_BEFORE" "$SUBJECT_AFTER" "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
  set_final fail "$step:$reason" 1
  exit 1
}

run_pass_step() {
  local step="$1" subject_root="$2" subject_path="$3"
  shift 3
  snapshot_before "$subject_root" "$subject_path" "$step"
  note "running step=$step"
  supervise "$step" "$@"
  inspect_supervisor "$step"
  snapshot_after "$subject_root" "$subject_path" "$step"
  require_unchanged "$step"
  if [ "$LAST_CLASSIFICATION" != pass ] || [ "$LAST_RC" -ne 0 ] || \
     [ "$LAST_CHILD_EXIT" != 0 ]; then
    record_contract_failure "$step" unexpected_command_failure
  fi
  record_step "$step" pass pass/wrapper=0/child=0 \
    "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
    not_applicable pass 0 0 "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
    "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
}

# The real crate suite is one supervised parent obligation.
run_pass_step environment_suite "$ROOT" crates/fln-env \
  env CARGO_TARGET_DIR=target_local cargo test --locked -q -p fln-env

run_structured_positive_step() {
  local step="$1" test_name="$2" schema_prefix="$3" expected_records="$4"
  snapshot_before "$ROOT" crates/fln-env "$step"
  note "running structured producer step=$step"
  supervise "$step" env FLN_ENV_E2E_RUN_ID="$RUN_ID-$step" \
    CARGO_TARGET_DIR=target_local cargo test --locked -q -p fln-env \
    "$test_name" -- --exact --nocapture
  inspect_supervisor "$step"
  snapshot_after "$ROOT" crates/fln-env "$step"
  require_unchanged "$step"
  if [ "$LAST_CLASSIFICATION" != pass ] || [ "$LAST_RC" -ne 0 ] || \
     [ "$LAST_CHILD_EXIT" != 0 ]; then
    record_contract_failure "$step" unexpected_command_failure
  fi
  local actual_records passed_records leaked_records
  actual_records="$(
    awk -v prefix="$schema_prefix" \
      'index($0, prefix) == 1 { count++ } END { print count + 0 }' "$LAST_OUT"
  )"
  passed_records="$(
    awk -v prefix="$schema_prefix" \
      'index($0, prefix) == 1 && index($0, "\"status\":\"pass\"") > 0 { count++ } END { print count + 0 }' \
      "$LAST_OUT"
  )"
  leaked_records="$(
    awk -v prefix="$schema_prefix" \
      'index($0, prefix) == 1 { count++ } END { print count + 0 }' "$LAST_ERR"
  )"
  if [ "$actual_records" -ne "$expected_records" ] || \
     [ "$passed_records" -ne "$expected_records" ] || \
     [ "$leaked_records" -ne 0 ]; then
    record_contract_failure "$step" malformed_or_misrouted_evidence
  fi
  record_step "$step" pass \
    "records=$expected_records/stdout_only/pass/wrapper=0/child=0" \
    "records=$actual_records/stderr_records=$leaked_records/$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
    not_applicable pass 0 0 "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
    "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
}

run_structured_positive_step environment_state \
  extensions::tests::environment_state_e2e_emits_detailed_real_path_evidence \
  '{"schema":"fln.e2e.environment-state","version":1' 4
run_structured_positive_step extension_merge_refusals \
  extensions::tests::extension_merge_refusals_e2e_emit_detailed_real_path_evidence \
  '{"schema":"fln.e2e.extension-merge-refusal","version":1' 2
run_structured_positive_step set_union \
  extensions::tests::set_union_e2e_emits_detailed_real_path_evidence \
  '{"schema":"fln.e2e.set-union","version":1' 4

# Retained overlay for the named mutation kills and the historical collision
# children. Every mutation is restored byte-for-byte before the next phase.
OVERLAY="$ART_DIR/overlay"
mkdir "$OVERLAY"
for crate in fln-core fln-hash fln-env; do
  cp -r "$ROOT/crates/$crate" "$OVERLAY/$crate"
done
cat > "$OVERLAY/Cargo.toml" <<'EOF'
[workspace]
resolver = "3"
members = ["fln-core", "fln-hash", "fln-env"]
EOF
cp "$ROOT/rust-toolchain.toml" "$OVERLAY/rust-toolchain.toml"
cp "$ROOT/Cargo.lock" "$OVERLAY/Cargo.lock"
EXTENSION_STATE_SOURCE="$OVERLAY/fln-env/src/environment.rs"
EXTENSION_STATE_PRISTINE="$ART_DIR/environment.extension-state.pristine.rs"
cp -- "$EXTENSION_STATE_SOURCE" "$EXTENSION_STATE_PRISTINE"
sed -i \
  's/extensions: self.extensions.clone(),/extensions: crate::pmap::PMap::new(),/' \
  "$EXTENSION_STATE_SOURCE"
if cmp -s "$EXTENSION_STATE_SOURCE" "$EXTENSION_STATE_PRISTINE"; then
  set_final internal_fault extension_state_mutation_seed_noop 2
  exit 2
fi

snapshot_before "$OVERLAY" fln-env/src/environment.rs extension_state_mutant
note "running extension-state mutant"
supervise_in "$ART_DIR" extension_state_mutant "$OVERLAY" \
  --semantic-failure-exit 101 --planted \
  env CARGO_TARGET_DIR="$OVERLAY/target" cargo test --locked -q -p fln-env \
  environment::tests::add_decl_preserves_extension_state -- --exact --nocapture
inspect_supervisor extension_state_mutant
snapshot_after "$OVERLAY" fln-env/src/environment.rs extension_state_mutant
require_unchanged extension_state_mutant
if [ "$LAST_CLASSIFICATION" != fail ] || [ "$LAST_RC" -ne 1 ] || \
   [ "$LAST_CHILD_EXIT" != 101 ]; then
  record_contract_failure extension_state_mutant mutant_survived_or_wrong_exit
fi
if ! grep -Fq \
    'environment::tests::add_decl_preserves_extension_state --- FAILED' \
    "$LAST_OUT" || \
   ! grep -Fq 'extension state survives add_decl' "$LAST_ERR"; then
  record_contract_failure extension_state_mutant intended_failure_signature_missing
fi
record_step extension_state_mutant pass \
  mutation-killed/fail/wrapper=1/child=101 \
  "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
  not_applicable fail 1 101 "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
  "$GLOBAL_BEFORE" "$GLOBAL_AFTER"

cp -- "$EXTENSION_STATE_PRISTINE" "$EXTENSION_STATE_SOURCE"
if ! cmp -s "$EXTENSION_STATE_SOURCE" "$EXTENSION_STATE_PRISTINE"; then
  set_final internal_fault extension_state_recovery_not_byte_exact 2
  exit 2
fi
snapshot_before "$OVERLAY" fln-env/src/environment.rs extension_state_recovery
note "running extension-state recovery"
supervise_in "$ART_DIR" extension_state_recovery "$OVERLAY" \
  env CARGO_TARGET_DIR="$OVERLAY/target" cargo test --locked -q -p fln-env \
  environment::tests::add_decl_preserves_extension_state -- --exact --nocapture
inspect_supervisor extension_state_recovery
snapshot_after "$OVERLAY" fln-env/src/environment.rs extension_state_recovery
require_unchanged extension_state_recovery
if [ "$LAST_CLASSIFICATION" != pass ] || [ "$LAST_RC" -ne 0 ] || \
   [ "$LAST_CHILD_EXIT" != 0 ]; then
  record_contract_failure extension_state_recovery recovery_failed
fi
record_step extension_state_recovery pass pass/wrapper=0/child=0 \
  "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
  not_applicable pass 0 0 "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
  "$GLOBAL_BEFORE" "$GLOBAL_AFTER"

SET_UNION_OVERLAY_SOURCE="$OVERLAY/fln-env/src/extensions.rs"
SET_UNION_PRISTINE_SOURCE="$ART_DIR/extensions.set-union.pristine.rs"
cp -- "$SET_UNION_OVERLAY_SOURCE" "$SET_UNION_PRISTINE_SOURCE"
if ! "${PYTHON[@]}" - "$SET_UNION_OVERLAY_SOURCE" <<'PY'
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
source = path.read_bytes()
anchor = b"    merged.push_entry(Arc::clone(&entry.payload)) // FLN_SET_UNION_RAW_APPEND"
replacement = b"    if merged.entries().any(|seen| seen == entry) { merged.clone() } else { merged.push_entry(Arc::clone(&entry.payload)) } // FLN_SET_UNION_RAW_APPEND"
if source.count(anchor) != 1:
    raise SystemExit("SetUnion mutation anchor count is not exactly one")
path.write_bytes(source.replace(anchor, replacement, 1))
PY
then
  set_final internal_fault set_union_mutation_anchor_mismatch 2
  exit 2
fi
if cmp -s "$SET_UNION_OVERLAY_SOURCE" "$SET_UNION_PRISTINE_SOURCE"; then
  set_final internal_fault set_union_mutation_seed_noop 2
  exit 2
fi

snapshot_before "$OVERLAY" fln-env/src/extensions.rs set_union_mutant
note "running SetUnion mutant"
supervise_in "$ART_DIR" set_union_mutant "$OVERLAY" \
  --semantic-failure-exit 101 --planted \
  env FLN_ENV_E2E_RUN_ID="$RUN_ID-set-union-mutant" \
  CARGO_TARGET_DIR="$OVERLAY/target" cargo test --locked -q -p fln-env \
  extensions::tests::set_union_e2e_emits_detailed_real_path_evidence \
  -- --exact --nocapture
inspect_supervisor set_union_mutant
snapshot_after "$OVERLAY" fln-env/src/extensions.rs set_union_mutant
require_unchanged set_union_mutant
if [ "$LAST_CLASSIFICATION" != fail ] || [ "$LAST_RC" -ne 1 ] || \
   [ "$LAST_CHILD_EXIT" != 101 ]; then
  record_contract_failure set_union_mutant mutant_survived_or_wrong_exit
fi
if ! grep -Fq \
    'extensions::tests::set_union_e2e_emits_detailed_real_path_evidence --- FAILED' \
    "$LAST_OUT" || \
   ! grep -Fq 'raw replay must be byte-lossless' "$LAST_ERR"; then
  record_contract_failure set_union_mutant intended_failure_signature_missing
fi
record_step set_union_mutant pass mutation-killed/fail/wrapper=1/child=101 \
  "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
  not_applicable fail 1 101 "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
  "$GLOBAL_BEFORE" "$GLOBAL_AFTER"

cp -- "$SET_UNION_PRISTINE_SOURCE" "$SET_UNION_OVERLAY_SOURCE"
if ! cmp -s "$SET_UNION_OVERLAY_SOURCE" "$SET_UNION_PRISTINE_SOURCE"; then
  set_final internal_fault set_union_recovery_not_byte_exact 2
  exit 2
fi
snapshot_before "$OVERLAY" fln-env/src/extensions.rs set_union_recovery
note "running SetUnion recovery"
supervise_in "$ART_DIR" set_union_recovery "$OVERLAY" \
  env FLN_ENV_E2E_RUN_ID="$RUN_ID-set-union-recovery" \
  CARGO_TARGET_DIR="$OVERLAY/target" cargo test --locked -q -p fln-env \
  extensions::tests::set_union_e2e_emits_detailed_real_path_evidence \
  -- --exact --nocapture
inspect_supervisor set_union_recovery
snapshot_after "$OVERLAY" fln-env/src/extensions.rs set_union_recovery
require_unchanged set_union_recovery
if [ "$LAST_CLASSIFICATION" != pass ] || [ "$LAST_RC" -ne 0 ] || \
   [ "$LAST_CHILD_EXIT" != 0 ]; then
  record_contract_failure set_union_recovery recovery_failed
fi
record_step set_union_recovery pass pass/wrapper=0/child=0 \
  "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
  not_applicable pass 0 0 "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
  "$GLOBAL_BEFORE" "$GLOBAL_AFTER"

run_identity_path_mutant_recovery() {
  local stem="$1" source_rel="$2" seed="$3" test_name="$4"
  local stdout_signature="$5" stderr_signature="$6"
  local overlay_source="$OVERLAY/$source_rel"
  local pristine_source="$ART_DIR/$stem.pristine.rs"
  local mutant_step="${stem}_mutant"
  local recovery_step="${stem}_recovery"

  cp -- "$overlay_source" "$pristine_source"
  if ! "${PYTHON[@]}" - "$overlay_source" "$seed" <<'PY'
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
seed = sys.argv[2]
mutations = {
    "opaque_membership_omission": (
        b"""            ConstantInfo::Opaque(v) => {
                v.value.write_body(&mut w);
                w.bool(v.is_unsafe);
                write_mutual_membership(&mut w, &v.all);
            }""",
        b"""            ConstantInfo::Opaque(v) => {
                v.value.write_body(&mut w);
                w.bool(v.is_unsafe);
            }""",
    ),
    "definition_safe_retag": (
        b"""const fn definition_safety_tag(safety: DefinitionSafety) -> u8 {
    match safety {
        DefinitionSafety::Unsafe => 0,
        DefinitionSafety::Safe => 1,
        DefinitionSafety::Partial => 2,
    }
}""",
        b"""const fn definition_safety_tag(safety: DefinitionSafety) -> u8 {
    match safety {
        DefinitionSafety::Unsafe => 0,
        DefinitionSafety::Safe => 5,
        DefinitionSafety::Partial => 2,
    }
}""",
    ),
    "descriptor_merge_omission": (
        b"""fn write_descriptor_identity(w: &mut CanonWriter, descriptor: &ExtensionDescriptor) {
    descriptor.name.write_body(w);
    w.u8(merge_semantics_tag(descriptor.merge));
    w.u8(checkpoint_semantics_tag(descriptor.checkpoint));
    w.u8(payload_provenance_tag(descriptor.provenance));
}""",
        b"""fn write_descriptor_identity(w: &mut CanonWriter, descriptor: &ExtensionDescriptor) {
    descriptor.name.write_body(w);
    w.u8(checkpoint_semantics_tag(descriptor.checkpoint));
    w.u8(payload_provenance_tag(descriptor.provenance));
}""",
    ),
}
try:
    anchor, replacement = mutations[seed]
except KeyError as error:
    raise SystemExit(f"unknown identity mutation seed: {seed}") from error
source = path.read_bytes()
anchor_count = source.count(anchor)
if anchor_count != 1:
    raise SystemExit(
        f"identity mutation anchor count is not exactly one: "
        f"seed={seed} count={anchor_count}"
    )
path.write_bytes(source.replace(anchor, replacement, 1))
PY
  then
    set_final internal_fault "$mutant_step:mutation_anchor_mismatch" 2
    exit 2
  fi
  if cmp -s "$overlay_source" "$pristine_source"; then
    set_final internal_fault "$mutant_step:mutation_seed_noop" 2
    exit 2
  fi

  snapshot_before "$OVERLAY" "$source_rel" "$mutant_step"
  note "running identity-path mutant step=$mutant_step seed=$seed"
  supervise_in "$ART_DIR" "$mutant_step" "$OVERLAY" \
    --semantic-failure-exit 101 --planted \
    env CARGO_TARGET_DIR="$OVERLAY/target" cargo test --locked -q -p fln-env \
    "$test_name" -- --exact --nocapture
  inspect_supervisor "$mutant_step"
  snapshot_after "$OVERLAY" "$source_rel" "$mutant_step"
  require_unchanged "$mutant_step"
  if [ "$LAST_CLASSIFICATION" != fail ] || [ "$LAST_RC" -ne 1 ] || \
     [ "$LAST_CHILD_EXIT" != 101 ]; then
    record_contract_failure "$mutant_step" mutant_survived_or_wrong_exit
  fi
  if ! grep -Fq "$stdout_signature" "$LAST_OUT" || \
     ! grep -Fq "$stderr_signature" "$LAST_ERR"; then
    record_contract_failure "$mutant_step" intended_failure_signature_missing
  fi
  record_step "$mutant_step" pass mutation-killed/fail/wrapper=1/child=101 \
    "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
    not_applicable fail 1 101 "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
    "$GLOBAL_BEFORE" "$GLOBAL_AFTER"

  cp -- "$pristine_source" "$overlay_source"
  if ! cmp -s "$overlay_source" "$pristine_source"; then
    set_final internal_fault "$recovery_step:recovery_not_byte_exact" 2
    exit 2
  fi
  snapshot_before "$OVERLAY" "$source_rel" "$recovery_step"
  note "running identity-path recovery step=$recovery_step seed=$seed"
  supervise_in "$ART_DIR" "$recovery_step" "$OVERLAY" \
    env CARGO_TARGET_DIR="$OVERLAY/target" cargo test --locked -q -p fln-env \
    "$test_name" -- --exact --nocapture
  inspect_supervisor "$recovery_step"
  snapshot_after "$OVERLAY" "$source_rel" "$recovery_step"
  require_unchanged "$recovery_step"
  if [ "$LAST_CLASSIFICATION" != pass ] || [ "$LAST_RC" -ne 0 ] || \
     [ "$LAST_CHILD_EXIT" != 0 ]; then
    record_contract_failure "$recovery_step" recovery_failed
  fi
  record_step "$recovery_step" pass pass/wrapper=0/child=0 \
    "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
    not_applicable pass 0 0 "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
    "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
}

run_identity_path_mutant_recovery declaration_membership \
  fln-env/src/environment.rs opaque_membership_omission \
  environment::tests::mutual_block_membership_changes_the_content_digest \
  'environment::tests::mutual_block_membership_changes_the_content_digest --- FAILED' \
  'opaque empty membership diverged from the independent canonical model'
run_identity_path_mutant_recovery declaration_tag \
  fln-env/src/environment.rs definition_safe_retag \
  environment::tests::declaration_identity_tag_policy_is_const_exhaustive_and_cast_free \
  'environment::tests::declaration_identity_tag_policy_is_const_exhaustive_and_cast_free --- FAILED' \
  'left: [0, 5, 2]'
run_identity_path_mutant_recovery extension_descriptor \
  fln-env/src/extensions.rs descriptor_merge_omission \
  extensions::tests::descriptor_identity_matrix_matches_model_and_logical_roots \
  'extensions::tests::descriptor_identity_matrix_matches_model_and_logical_roots --- FAILED' \
  'descriptor identity diverged from the independent layout model'

identity_emit_event() {
  local sequence="$IDENTITY_SEQ"
  IDENTITY_SEQ=$((IDENTITY_SEQ + 1))
  "${PYTHON[@]}" "$EVIDENCE" emit --file "$IDENTITY_LOG" \
    --artifact-root "$IDENTITY_ART_DIR" \
    --string schema fln.e2e/2 --string run_id "$IDENTITY_RUN_ID" \
    --string bead "$IDENTITY_BEAD" --string scenario "$IDENTITY_SCENARIO" \
    --integer sequence "$sequence" \
    --integer monotonic_ns "$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')" \
    --string wall_time_utc "$(date -u -Is)" "$@"
}

validate_child_reference() {
  local step="$1" child_rel="$2"
  local child_dir="$ART_DIR/$child_rel"
  snapshot_before "$ART_DIR" "$child_rel" "$step"
  note "validating nested child=$child_rel"
  supervise "$step" "${PYTHON[@]}" "$EVIDENCE" validate-bundle \
    --art-dir "$child_dir" --manifest "$child_dir/manifest.json" \
    --digest "$child_dir/manifest.digest" \
    --commit "$child_dir/bundle.complete.json" \
    --artifact-root "$child_dir"
  inspect_supervisor "$step"
  snapshot_after "$ART_DIR" "$child_rel" "$step"
  require_unchanged "$step"
  if [ "$LAST_CLASSIFICATION" != pass ] || [ "$LAST_RC" -ne 0 ] || \
     [ "$LAST_CHILD_EXIT" != 0 ]; then
    record_contract_failure "$step" child_bundle_validation_failed
  fi
  record_step "$step" pass \
    "child=$child_rel/bundle.complete.json/pass/wrapper=0/child=0" \
    "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
    "$child_rel/run.validation.json" pass 0 0 \
    "$SUBJECT_BEFORE" "$SUBJECT_AFTER" "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
}

run_identity_child() {
  local scenario="$1" child_bead="$2" child_rel="$3" test_name="$4"
  local validator="$5" claim_id="$6"
  IDENTITY_SCENARIO="$scenario"
  IDENTITY_BEAD="$child_bead"
  IDENTITY_RUN_ID="$RUN_ID-$scenario"
  IDENTITY_ART_DIR="$ART_DIR/$child_rel"
  IDENTITY_LOG="$IDENTITY_ART_DIR/run.ndjson"
  IDENTITY_SEQ=0
  local child_start_ns child_input_root child_final_root
  child_start_ns="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
  child_input_root="$(hash_governed)"
  if [ "$child_input_root" != "$INPUT_ROOT" ]; then
    set_final inconclusive "$scenario:governed_inputs_changed" 3
    exit 3
  fi
  if [ -e "$IDENTITY_ART_DIR" ] || [ -L "$IDENTITY_ART_DIR" ]; then
    set_final internal_fault "$scenario:reused_child_directory" 2
    exit 2
  fi
  mkdir "$IDENTITY_ART_DIR"
  "${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ROOT" \
    --vendor-path "$VENDOR_PATH" \
    --output "$IDENTITY_ART_DIR/vendor-binding.json" \
    --artifact-root "$IDENTITY_ART_DIR" || {
      set_final internal_fault "$scenario:vendor_binding_failed" 2
      exit 2
    }
  identity_emit_event --new-log --string event run_start \
    --json-value argv '["scripts/e2e/env_snapshots.sh"]' \
    --string cwd "$ROOT" --append-string claim_ids "$claim_id" \
    --append-string invariant_ids FL-INV-01 \
    --append-string gate_ids PG-5 \
    --string parity_ledger_row not_applicable_internal_environment_identity \
    --string epoch lean-v4.32.0 --string mode sound --string profile e2e \
    --string platform "$(uname -srm)" \
    --json-value host_facts "$HOST_FACTS_JSON" --integer thread_count 32 \
    --json-value thread_matrix '[1,8,32]' \
    --string seed "$scenario-v1" --string cache_state "$CACHE_STATE" \
    --string input_root "$child_input_root" \
    --string vendor_binding vendor-binding.json \
    --json-value budgets "{\"capture_bytes_per_stream\":$CAPTURE_BYTES,\"output_budget_bytes\":$OUTPUT_BUDGET_BYTES,\"step_timeout_ms\":$TIMEOUT_MS,\"kill_grace_ms\":$GRACE_MS}"
  : > "$IDENTITY_ART_DIR/human.log"

  local child_subject_before child_subject_after child_global_before
  local child_global_after validation
  child_subject_before="$(hash_subject "$ROOT" crates/fln-env)"
  child_global_before="$(hash_governed)"
  note "running identity child=$scenario"
  supervise_in "$IDENTITY_ART_DIR" "$scenario" "$ROOT" \
    env FLN_ENV_E2E_RUN_ID="$IDENTITY_RUN_ID" \
    CARGO_TARGET_DIR=target_local cargo test --locked -q -p fln-env \
    "$test_name" -- --exact --nocapture
  inspect_supervisor "$scenario"
  child_subject_after="$(hash_subject "$ROOT" crates/fln-env)"
  child_global_after="$(hash_governed)"
  if [ "$child_subject_before" != "$child_subject_after" ] || \
     [ "$child_global_before" != "$child_input_root" ] || \
     [ "$child_global_after" != "$child_input_root" ]; then
    set_final inconclusive "$scenario:governed_inputs_changed" 3
    exit 3
  fi
  if [ "$LAST_CLASSIFICATION" != pass ] || [ "$LAST_RC" -ne 0 ] || \
     [ "$LAST_CHILD_EXIT" != 0 ]; then
    set_final fail "$scenario:producer_failed" 1
    exit 1
  fi
  validation="$IDENTITY_ART_DIR/$scenario.validation.json"
  "${PYTHON[@]}" "$EVIDENCE" "$validator" --file "$LAST_OUT" \
    --stderr-file "$LAST_ERR" --expected-run-id "$IDENTITY_RUN_ID" \
    --observed-exit "$LAST_CHILD_EXIT" \
    --expected-stdout-artifact "$scenario.out" \
    --expected-stderr-artifact "$scenario.err" \
    --artifact-root "$IDENTITY_ART_DIR" --output "$validation" || {
      set_final fail "$scenario:strict_validation_failed" 1
      exit 1
    }
  identity_emit_event --string event step --string step_id "$scenario" \
    --string assertion pass \
    --string expected "strict-validator/pass/wrapper=0/child=0" \
    --string actual "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
    --string input_root "$child_global_before" \
    --string final_state "$child_global_after" \
    --string validation_artifact "$scenario.validation.json" \
    --string expected_supervisor_classification pass \
    --integer expected_wrapper_exit 0 --integer expected_child_exit 0 \
    --string subject_root "$child_subject_before" \
    --string subject_final_state "$child_subject_after" \
    --json-file supervisor "$LAST_META"
  child_final_root="$(hash_governed)"
  if [ "$child_final_root" != "$child_input_root" ]; then
    set_final inconclusive "$scenario:governed_inputs_changed" 3
    exit 3
  fi
  identity_emit_event --string event run_end --string verdict pass \
    --string reason_code all_obligations_passed --integer process_exit 0 \
    --string active_step "$scenario" \
    --integer duration_ns "$(( $("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())') - child_start_ns ))" \
    --string cleanup_status retained_by_policy \
    --string final_state "$child_final_root" \
    --string logical_root "$child_final_root" \
    --string receipt_root not_applicable_environment_identity_matrix \
    --string first_divergence none --string evidence_manifest manifest.json \
    --string bundle_commit bundle.complete.json \
    --string evidence_state pending_bundle_commit
  printf '[env_snapshots:%s] terminal verdict=pass\n' "$scenario" \
    > "$IDENTITY_ART_DIR/human.log"
  "${PYTHON[@]}" "$EVIDENCE" validate-run --file "$IDENTITY_LOG" \
    --schema fln.e2e/2 --expected-verdict pass \
    --expected-active-stage "$scenario" --artifact-root "$IDENTITY_ART_DIR" \
    --output "$IDENTITY_ART_DIR/run.validation.json"
  "${PYTHON[@]}" "$EVIDENCE" manifest --art-dir "$IDENTITY_ART_DIR" \
    --output "$IDENTITY_ART_DIR/manifest.json" \
    --digest-output "$IDENTITY_ART_DIR/manifest.digest" \
    --run-id "$IDENTITY_RUN_ID" --bead "$IDENTITY_BEAD" \
    --scenario "$IDENTITY_SCENARIO" --verdict pass \
    --input-root "$child_input_root" --final-root "$child_final_root"
  "${PYTHON[@]}" "$EVIDENCE" complete-bundle --art-dir "$IDENTITY_ART_DIR" \
    --manifest "$IDENTITY_ART_DIR/manifest.json" \
    --digest "$IDENTITY_ART_DIR/manifest.digest" \
    --output "$IDENTITY_ART_DIR/bundle.complete.json" \
    --governed-root "$ROOT" "${GOVERNED_ARGS[@]}" \
    --expected-root "$child_final_root" --vendor-path "$VENDOR_PATH"
  "${PYTHON[@]}" "$EVIDENCE" adopt-bundle --art-dir "$IDENTITY_ART_DIR" \
    --manifest "$IDENTITY_ART_DIR/manifest.json" \
    --digest "$IDENTITY_ART_DIR/manifest.digest" \
    --commit "$IDENTITY_ART_DIR/bundle.complete.json" \
    --artifact-root "$IDENTITY_ART_DIR" >/dev/null
  validate_child_reference "$scenario" "$child_rel"
}

run_identity_child declaration_tag_matrix fln-amv.12 \
  declaration-tag-matrix-fln-amv.12 \
  environment::tests::declaration_tag_matrix_e2e_emits_detailed_real_path_evidence \
  validate-declaration-tag-matrix fln-amv.12-declaration-tag-matrix
run_identity_child declaration_membership fln-amv.1 \
  declaration-membership-fln-amv.1 \
  environment::tests::declaration_membership_matrix_e2e_emits_detailed_real_path_evidence \
  validate-declaration-membership fln-amv.1-declaration-membership
run_identity_child extension_descriptor_matrix fln-amv.2 \
  extension-descriptor-matrix-fln-amv.2 \
  extensions::tests::extension_descriptor_matrix_e2e_emits_detailed_real_path_evidence \
  validate-extension-descriptor-matrix fln-amv.2-extension-descriptor-matrix

# ---- nested fln-amv.10 collision evidence bundle --------------------------------------
# Collision detail belongs exclusively to this authoritative fln.e2e/2 child.
# The parent records one supervised validation reference after the child commits.
COLLISION_SCHEMA="fln.e2e/2"
COLLISION_BEAD="fln-amv.10"
COLLISION_SCENARIO="environment_collision"
COLLISION_RUN_ID="$RUN_ID-collision-fln-amv-10"
COLLISION_ART_DIR="$ART_DIR/collision-fln-amv.10"
COLLISION_LOG="$COLLISION_ART_DIR/run.ndjson"
COLLISION_HUMAN="$COLLISION_ART_DIR/human.log"
COLLISION_VENDOR_PATH="vendor/lean4-src"
COLLISION_VENDOR_BINDING="$COLLISION_ART_DIR/vendor-binding.json"
COLLISION_SEQ=0
COLLISION_START_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
COLLISION_CAPTURE_BYTES="${FLN_E2E_CAPTURE_BYTES:-262144}"
COLLISION_OUTPUT_BUDGET_BYTES="${FLN_E2E_OUTPUT_BUDGET_BYTES:-16777216}"
COLLISION_TIMEOUT_MS="${FLN_E2E_TIMEOUT_MS:-300000}"
COLLISION_GRACE_MS="${FLN_E2E_KILL_GRACE_MS:-2000}"
COLLISION_CACHE_STATE="${FLN_E2E_CACHE_STATE:-uncontrolled}"
COLLISION_CARGO_ARGV="cargo test --locked -q -p fln-env pmap::tests::environment_collision_e2e_emits_detailed_real_path_evidence -- --exact --nocapture"
COLLISION_INPUT_PATHS=(
  Cargo.toml Cargo.lock SUITE.lock rust-toolchain.toml
  crates/fln-core crates/fln-hash crates/fln-env
  vendor/NOTICE scripts/check.sh scripts/evidence.py scripts/verify_vendor_tree.sh
  scripts/e2e/env_snapshots.sh .github/workflows/ci.yml
)
COLLISION_HASH_ARGS=()
COLLISION_GOVERNED_ARGS=()
for collision_input_path in "${COLLISION_INPUT_PATHS[@]}"; do
  COLLISION_HASH_ARGS+=(--path "$collision_input_path")
  COLLISION_GOVERNED_ARGS+=(--governed-path "$collision_input_path")
done

collision_note() {
  printf '[env_snapshots:%s] %s\n' "$COLLISION_BEAD" "$*" | tee -a "$COLLISION_HUMAN" >&2
}

collision_emit_event() {
  local sequence="$COLLISION_SEQ"
  COLLISION_SEQ=$((COLLISION_SEQ + 1))
  "${PYTHON[@]}" "$EVIDENCE" emit --file "$COLLISION_LOG" --artifact-root "$COLLISION_ART_DIR" \
    --string schema "$COLLISION_SCHEMA" --string run_id "$COLLISION_RUN_ID" \
    --string bead "$COLLISION_BEAD" --string scenario "$COLLISION_SCENARIO" \
    --integer sequence "$sequence" \
    --integer monotonic_ns "$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')" \
    --string wall_time_utc "$(date -u -Is)" "$@"
}

collision_hash_live() {
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${COLLISION_HASH_ARGS[@]}" \
    --vendor-path "$COLLISION_VENDOR_PATH"
}

collision_hash_subject() {
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$1" --path "$2"
}

collision_file_sha256() {
  "${PYTHON[@]}" - "$1" <<'PY'
import hashlib
import pathlib
import sys

digest = hashlib.sha256()
with pathlib.Path(sys.argv[1]).open("rb") as stream:
    for block in iter(lambda: stream.read(1024 * 1024), b""):
        digest.update(block)
print(digest.hexdigest())
PY
}

collision_meta_field() {
  "${PYTHON[@]}" - "$1" "$2" <<'PY'
import json
import pathlib
import sys

value = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))[sys.argv[2]]
if value is None:
    print("null")
elif value is True:
    print("true")
elif value is False:
    print("false")
else:
    print(value)
PY
}

collision_supervise() {
  local step="$1" cwd="$2" semantic_exit="$3" planted="$4"
  shift 4
  local -a semantic_args=()
  COLLISION_LAST_META="$COLLISION_ART_DIR/$step.meta.json"
  COLLISION_LAST_OUT="$COLLISION_ART_DIR/$step.out"
  COLLISION_LAST_ERR="$COLLISION_ART_DIR/$step.err"
  COLLISION_LAST_READY="$COLLISION_ART_DIR/$step.ready.json"
  if [ "$semantic_exit" != none ]; then
    semantic_args+=(--semantic-failure-exit "$semantic_exit")
  fi
  if [ "$planted" = true ]; then
    semantic_args+=(--planted)
  fi
  collision_note "running step=$step cwd=$cwd"
  set +e
  "${PYTHON[@]}" "$EVIDENCE" run --cwd "$cwd" \
    --metadata "$COLLISION_LAST_META" --stdout "$COLLISION_LAST_OUT" \
    --stderr "$COLLISION_LAST_ERR" --readiness "$COLLISION_LAST_READY" \
    --artifact-root "$COLLISION_ART_DIR" --capture-bytes "$COLLISION_CAPTURE_BYTES" \
    --output-budget-bytes "$COLLISION_OUTPUT_BUDGET_BYTES" \
    --timeout-ms "$COLLISION_TIMEOUT_MS" --grace-ms "$COLLISION_GRACE_MS" \
    --stage-id "$step" "${semantic_args[@]}" -- "$@"
  COLLISION_LAST_RC=$?
  set -e
}

collision_assert_supervisor() {
  local step="$1" expected_class="$2" expected_wrapper="$3" expected_child="$4"
  local expected_planted="$5"
  if [ ! -s "$COLLISION_LAST_META" ]; then
    collision_note "FAIL step=$step: missing supervisor metadata"
    exit 2
  fi
  COLLISION_LAST_CLASS="$(collision_meta_field "$COLLISION_LAST_META" classification)"
  COLLISION_LAST_WRAPPER="$(collision_meta_field "$COLLISION_LAST_META" wrapper_exit)"
  COLLISION_LAST_CHILD="$(collision_meta_field "$COLLISION_LAST_META" child_exit)"
  COLLISION_LAST_PLANTED="$(collision_meta_field "$COLLISION_LAST_META" planted)"
  if [ "$COLLISION_LAST_RC" != "$expected_wrapper" ] || \
     [ "$COLLISION_LAST_CLASS" != "$expected_class" ] || \
     [ "$COLLISION_LAST_WRAPPER" != "$expected_wrapper" ] || \
     [ "$COLLISION_LAST_CHILD" != "$expected_child" ] || \
     [ "$COLLISION_LAST_PLANTED" != "$expected_planted" ]; then
    collision_note "FAIL step=$step: expected $expected_class/wrapper=$expected_wrapper/child=$expected_child/planted=$expected_planted, got $COLLISION_LAST_CLASS/wrapper=$COLLISION_LAST_RC/child=$COLLISION_LAST_CHILD/planted=$COLLISION_LAST_PLANTED"
    exit 1
  fi
}

collision_record_step() {
  local step="$1" expected="$2" actual="$3" validation="$4"
  local expected_class="$5" expected_wrapper="$6" expected_child="$7"
  local subject_root="$8" subject_final_state="$9"
  local global_root="${10}" global_final_state="${11}"
  collision_emit_event --string event step --string step_id "$step" \
    --string assertion pass --string expected "$expected" --string actual "$actual" \
    --string input_root "$global_root" --string final_state "$global_final_state" \
    --string validation_artifact "$validation" \
    --string expected_supervisor_classification "$expected_class" \
    --integer expected_wrapper_exit "$expected_wrapper" \
    --integer expected_child_exit "$expected_child" \
    --string subject_root "$subject_root" \
    --string subject_final_state "$subject_final_state" \
    --json-file supervisor "$COLLISION_LAST_META"
}

collision_assert_unchanged() {
  local step="$1" subject_before="$2" subject_after="$3"
  local global_before="$4" global_after="$5"
  if [ "$subject_before" != "$subject_after" ]; then
    collision_note "FAIL step=$step: subject changed during supervised assertion"
    exit 3
  fi
  if [ "$global_before" != "$COLLISION_INPUT_ROOT" ] || \
     [ "$global_after" != "$COLLISION_INPUT_ROOT" ]; then
    collision_note "FAIL step=$step: governed live input changed"
    exit 3
  fi
}

# Hash the complete live input before creating a child directory that could look
# like committed evidence, then bind the exact pinned Reference tree.
if ! COLLISION_INPUT_ROOT="$(collision_hash_live)"; then
  note "FAIL: cannot hash fln-amv.10 governed inputs"
  exit 2
fi
if [ -e "$COLLISION_ART_DIR" ] || [ -L "$COLLISION_ART_DIR" ]; then
  note "FAIL: refusing reused collision evidence directory $COLLISION_ART_DIR"
  exit 2
fi
mkdir "$COLLISION_ART_DIR"
"${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ROOT" \
  --vendor-path "$COLLISION_VENDOR_PATH" --output "$COLLISION_VENDOR_BINDING" \
  --artifact-root "$COLLISION_ART_DIR" || {
    note "FAIL: cannot bind the pinned Reference tree for fln-amv.10"
    exit 2
  }

COLLISION_LIVE_SUBJECT_SHA="$(collision_file_sha256 "$ROOT/crates/fln-env/src/pmap.rs")"
COLLISION_LIVE_HEAD="$(git -C "$ROOT" rev-parse HEAD)"
collision_emit_event --new-log --string event run_start \
  --json-value argv '["scripts/e2e/env_snapshots.sh"]' \
  --string cwd "$ROOT" \
  --append-string claim_ids fln-amv.10-collision-canonicality \
  --append-string invariant_ids FL-INV-01 \
  --append-string gate_ids PG-5 \
  --string parity_ledger_row not_applicable_internal_data_structure_determinism \
  --string epoch lean-v4.32.0 --string mode sound --string profile e2e \
  --string platform "$(uname -srm)" \
  --json-value host_facts "$("${PYTHON[@]}" -c 'import json,platform; print(json.dumps({"system":platform.system(),"release":platform.release(),"machine":platform.machine(),"python":platform.python_version()},separators=(",",":")))')" \
  --integer thread_count 32 --string seed partition-rotation-v1 \
  --json-value thread_matrix '[1,8,32]' \
  --string cache_state "$COLLISION_CACHE_STATE" \
  --string input_root "$COLLISION_INPUT_ROOT" \
  --string vendor_binding vendor-binding.json \
  --string live_head "$COLLISION_LIVE_HEAD" \
  --string live_subject_sha256 "$COLLISION_LIVE_SUBJECT_SHA" \
  --json-value budgets "{\"capture_bytes_per_stream\":$COLLISION_CAPTURE_BYTES,\"output_budget_bytes\":$COLLISION_OUTPUT_BUDGET_BYTES,\"step_timeout_ms\":$COLLISION_TIMEOUT_MS,\"kill_grace_ms\":$COLLISION_GRACE_MS,\"max_collision_cardinality\":96}"
: > "$COLLISION_HUMAN"

if [ ! -f "$OVERLAY/Cargo.lock" ]; then
  collision_note "FAIL: recovered overlay lacks the Cargo.lock required by --locked"
  exit 2
fi
COLLISION_PRISTINE_SOURCE="$COLLISION_ART_DIR/pmap.pristine.rs"
cp -- "$OVERLAY/fln-env/src/pmap.rs" "$COLLISION_PRISTINE_SOURCE"
COLLISION_PRISTINE_SHA="$(collision_file_sha256 "$COLLISION_PRISTINE_SOURCE")"
if [ "$COLLISION_PRISTINE_SHA" != "$COLLISION_LIVE_SUBJECT_SHA" ]; then
  collision_note "FAIL: recovered overlay pmap.rs is not byte-identical to the live subject"
  exit 3
fi
COLLISION_PRISTINE_SUBJECT_ROOT="$(collision_hash_subject "$OVERLAY" fln-env/src/pmap.rs)"

# Positive: the live subject emits exactly the v2 rows for {1,8,32}.
COLLISION_POSITIVE_SUBJECT_BEFORE="$(collision_hash_subject "$ROOT" crates/fln-env/src/pmap.rs)"
COLLISION_POSITIVE_GLOBAL_BEFORE="$(collision_hash_live)"
collision_supervise collision_positive "$ROOT" none false \
  env FLN_ENV_E2E_RUN_ID="$COLLISION_RUN_ID" \
  FLN_ENV_E2E_STDOUT_ARTIFACT=collision_positive.out \
  FLN_ENV_E2E_STDERR_ARTIFACT=collision_positive.err \
  FLN_ENV_E2E_ARGV="$COLLISION_CARGO_ARGV" \
  FLN_ENV_E2E_CACHE_STATE="$COLLISION_CACHE_STATE" \
  CARGO_TARGET_DIR=target_local \
  cargo test --locked -q -p fln-env \
  pmap::tests::environment_collision_e2e_emits_detailed_real_path_evidence \
  -- --exact --nocapture
collision_assert_supervisor collision_positive pass 0 0 false
COLLISION_POSITIVE_SUBJECT_AFTER="$(collision_hash_subject "$ROOT" crates/fln-env/src/pmap.rs)"
COLLISION_POSITIVE_GLOBAL_AFTER="$(collision_hash_live)"
collision_assert_unchanged collision_positive \
  "$COLLISION_POSITIVE_SUBJECT_BEFORE" "$COLLISION_POSITIVE_SUBJECT_AFTER" \
  "$COLLISION_POSITIVE_GLOBAL_BEFORE" "$COLLISION_POSITIVE_GLOBAL_AFTER"
COLLISION_POSITIVE_VALIDATION="$COLLISION_ART_DIR/collision_positive.validation.json"
"${PYTHON[@]}" "$EVIDENCE" validate-environment-collision \
  --file "$COLLISION_LAST_OUT" --stderr-file "$COLLISION_LAST_ERR" --phase positive \
  --expected-run-id "$COLLISION_RUN_ID" --observed-exit "$COLLISION_LAST_CHILD" \
  --expected-cwd "$ROOT/crates/fln-env" --expected-argv "$COLLISION_CARGO_ARGV" \
  --expected-stdout-artifact collision_positive.out \
  --expected-stderr-artifact collision_positive.err \
  --expected-cache-state "$COLLISION_CACHE_STATE" \
  --artifact-root "$COLLISION_ART_DIR" --output "$COLLISION_POSITIVE_VALIDATION"
collision_record_step collision_positive \
  "environment-collision/1:positive/pass/wrapper=0/child=0/sha256=$COLLISION_LIVE_SUBJECT_SHA" \
  "$COLLISION_LAST_CLASS/wrapper=$COLLISION_LAST_RC/child=$COLLISION_LAST_CHILD/sha256=$COLLISION_LIVE_SUBJECT_SHA" \
  collision_positive.validation.json pass 0 0 \
  "$COLLISION_POSITIVE_SUBJECT_BEFORE" "$COLLISION_POSITIVE_SUBJECT_AFTER" \
  "$COLLISION_POSITIVE_GLOBAL_BEFORE" "$COLLISION_POSITIVE_GLOBAL_AFTER"

# Mutant: change exactly one anchor in the retained overlay and classify Cargo's
# semantic test failure (101) as fail/wrapper=1, never as an internal fault.
if ! "${PYTHON[@]}" - "$OVERLAY/fln-env/src/pmap.rs" <<'PY'
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
source = path.read_bytes()
anchor = b"new_entries.insert(index, entry);"
replacement = b"new_entries.push(entry);"
if source.count(anchor) != 1:
    raise SystemExit("collision mutation anchor count is not exactly one")
path.write_bytes(source.replace(anchor, replacement, 1))
PY
then
  collision_note "FAIL: collision mutation did not match exactly one overlay anchor"
  exit 2
fi
COLLISION_MUTANT_SHA="$(collision_file_sha256 "$OVERLAY/fln-env/src/pmap.rs")"
if [ "$COLLISION_MUTANT_SHA" = "$COLLISION_PRISTINE_SHA" ]; then
  collision_note "FAIL: collision mutation did not change the overlay subject"
  exit 2
fi
COLLISION_MUTANT_SUBJECT_BEFORE="$(collision_hash_subject "$OVERLAY" fln-env/src/pmap.rs)"
COLLISION_MUTANT_GLOBAL_BEFORE="$(collision_hash_live)"
collision_supervise collision_mutant "$OVERLAY" 101 true \
  env FLN_ENV_E2E_RUN_ID="$COLLISION_RUN_ID" \
  FLN_ENV_E2E_STDOUT_ARTIFACT=collision_mutant.out \
  FLN_ENV_E2E_STDERR_ARTIFACT=collision_mutant.err \
  FLN_ENV_E2E_ARGV="$COLLISION_CARGO_ARGV" \
  FLN_ENV_E2E_CACHE_STATE="$COLLISION_CACHE_STATE" \
  CARGO_TARGET_DIR="$OVERLAY/target" \
  cargo test --locked -q -p fln-env \
  pmap::tests::environment_collision_e2e_emits_detailed_real_path_evidence \
  -- --exact --nocapture
collision_assert_supervisor collision_mutant fail 1 101 true
COLLISION_MUTANT_SUBJECT_AFTER="$(collision_hash_subject "$OVERLAY" fln-env/src/pmap.rs)"
COLLISION_MUTANT_GLOBAL_AFTER="$(collision_hash_live)"
collision_assert_unchanged collision_mutant \
  "$COLLISION_MUTANT_SUBJECT_BEFORE" "$COLLISION_MUTANT_SUBJECT_AFTER" \
  "$COLLISION_MUTANT_GLOBAL_BEFORE" "$COLLISION_MUTANT_GLOBAL_AFTER"
COLLISION_MUTANT_VALIDATION="$COLLISION_ART_DIR/collision_mutant.validation.json"
"${PYTHON[@]}" "$EVIDENCE" validate-environment-collision \
  --file "$COLLISION_LAST_OUT" --stderr-file "$COLLISION_LAST_ERR" --phase mutant \
  --expected-run-id "$COLLISION_RUN_ID" --observed-exit "$COLLISION_LAST_CHILD" \
  --expected-stdout-artifact collision_mutant.out \
  --expected-stderr-artifact collision_mutant.err \
  --artifact-root "$COLLISION_ART_DIR" --output "$COLLISION_MUTANT_VALIDATION"
collision_record_step collision_mutant \
  "environment-collision/1:mutant/fail/wrapper=1/child=101/pristine_sha256=$COLLISION_PRISTINE_SHA" \
  "$COLLISION_LAST_CLASS/wrapper=$COLLISION_LAST_RC/child=$COLLISION_LAST_CHILD/mutant_sha256=$COLLISION_MUTANT_SHA" \
  collision_mutant.validation.json fail 1 101 \
  "$COLLISION_MUTANT_SUBJECT_BEFORE" "$COLLISION_MUTANT_SUBJECT_AFTER" \
  "$COLLISION_MUTANT_GLOBAL_BEFORE" "$COLLISION_MUTANT_GLOBAL_AFTER"

# Recovery: restore the retained pristine bytes and require an exact SHA match
# before the independently supervised recovery assertion.
cp -- "$COLLISION_PRISTINE_SOURCE" "$OVERLAY/fln-env/src/pmap.rs"
COLLISION_RECOVERED_SHA="$(collision_file_sha256 "$OVERLAY/fln-env/src/pmap.rs")"
if [ "$COLLISION_RECOVERED_SHA" != "$COLLISION_PRISTINE_SHA" ]; then
  collision_note "FAIL: recovered pmap.rs does not byte-match the pristine overlay"
  exit 3
fi
COLLISION_RECOVERY_SUBJECT_BEFORE="$(collision_hash_subject "$OVERLAY" fln-env/src/pmap.rs)"
if [ "$COLLISION_RECOVERY_SUBJECT_BEFORE" != "$COLLISION_PRISTINE_SUBJECT_ROOT" ]; then
  collision_note "FAIL: recovered pmap.rs tree root differs from the pristine overlay"
  exit 3
fi
COLLISION_RECOVERY_GLOBAL_BEFORE="$(collision_hash_live)"
collision_supervise collision_recovery "$OVERLAY" none false \
  env FLN_ENV_E2E_RUN_ID="$COLLISION_RUN_ID" \
  FLN_ENV_E2E_STDOUT_ARTIFACT=collision_recovery.out \
  FLN_ENV_E2E_STDERR_ARTIFACT=collision_recovery.err \
  FLN_ENV_E2E_ARGV="$COLLISION_CARGO_ARGV" \
  FLN_ENV_E2E_CACHE_STATE="$COLLISION_CACHE_STATE" \
  CARGO_TARGET_DIR="$OVERLAY/target" \
  cargo test --locked -q -p fln-env \
  pmap::tests::environment_collision_e2e_emits_detailed_real_path_evidence \
  -- --exact --nocapture
collision_assert_supervisor collision_recovery pass 0 0 false
COLLISION_RECOVERY_SUBJECT_AFTER="$(collision_hash_subject "$OVERLAY" fln-env/src/pmap.rs)"
COLLISION_RECOVERY_GLOBAL_AFTER="$(collision_hash_live)"
collision_assert_unchanged collision_recovery \
  "$COLLISION_RECOVERY_SUBJECT_BEFORE" "$COLLISION_RECOVERY_SUBJECT_AFTER" \
  "$COLLISION_RECOVERY_GLOBAL_BEFORE" "$COLLISION_RECOVERY_GLOBAL_AFTER"
COLLISION_RECOVERY_VALIDATION="$COLLISION_ART_DIR/collision_recovery.validation.json"
"${PYTHON[@]}" "$EVIDENCE" validate-environment-collision \
  --file "$COLLISION_LAST_OUT" --stderr-file "$COLLISION_LAST_ERR" --phase recovery \
  --expected-run-id "$COLLISION_RUN_ID" --observed-exit "$COLLISION_LAST_CHILD" \
  --expected-cwd "$OVERLAY/fln-env" --expected-argv "$COLLISION_CARGO_ARGV" \
  --expected-stdout-artifact collision_recovery.out \
  --expected-stderr-artifact collision_recovery.err \
  --expected-cache-state "$COLLISION_CACHE_STATE" \
  --artifact-root "$COLLISION_ART_DIR" --output "$COLLISION_RECOVERY_VALIDATION"
collision_record_step collision_recovery \
  "environment-collision/1:recovery/pass/wrapper=0/child=0/sha256=$COLLISION_PRISTINE_SHA" \
  "$COLLISION_LAST_CLASS/wrapper=$COLLISION_LAST_RC/child=$COLLISION_LAST_CHILD/sha256=$COLLISION_RECOVERED_SHA" \
  collision_recovery.validation.json pass 0 0 \
  "$COLLISION_RECOVERY_SUBJECT_BEFORE" "$COLLISION_RECOVERY_SUBJECT_AFTER" \
  "$COLLISION_RECOVERY_GLOBAL_BEFORE" "$COLLISION_RECOVERY_GLOBAL_AFTER"

COLLISION_FINAL_ROOT="$(collision_hash_live)"
if [ "$COLLISION_FINAL_ROOT" != "$COLLISION_INPUT_ROOT" ]; then
  collision_note "FAIL: collision child changed its governed live input"
  exit 3
fi
collision_emit_event --string event run_end --string verdict pass \
  --string reason_code all_obligations_passed --integer process_exit 0 \
  --string active_step collision_recovery \
  --integer duration_ns "$(( $("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())') - COLLISION_START_NS ))" \
  --string cleanup_status retained_by_policy \
  --string final_state "$COLLISION_FINAL_ROOT" \
  --string logical_root "$COLLISION_FINAL_ROOT" \
  --string receipt_root not_applicable_internal_determinism \
  --string first_divergence none \
  --string evidence_manifest manifest.json \
  --string bundle_commit bundle.complete.json \
  --string evidence_state pending_bundle_commit

"${PYTHON[@]}" "$EVIDENCE" validate-run --file "$COLLISION_LOG" \
  --schema "$COLLISION_SCHEMA" --expected-verdict pass \
  --expected-active-stage collision_recovery \
  --artifact-root "$COLLISION_ART_DIR" \
  --output "$COLLISION_ART_DIR/run.validation.json"
"${PYTHON[@]}" "$EVIDENCE" manifest --art-dir "$COLLISION_ART_DIR" \
  --output "$COLLISION_ART_DIR/manifest.json" \
  --digest-output "$COLLISION_ART_DIR/manifest.digest" \
  --run-id "$COLLISION_RUN_ID" --bead "$COLLISION_BEAD" \
  --scenario "$COLLISION_SCENARIO" --verdict pass \
  --input-root "$COLLISION_INPUT_ROOT" --final-root "$COLLISION_FINAL_ROOT"
"${PYTHON[@]}" "$EVIDENCE" complete-bundle --art-dir "$COLLISION_ART_DIR" \
  --manifest "$COLLISION_ART_DIR/manifest.json" \
  --digest "$COLLISION_ART_DIR/manifest.digest" \
  --output "$COLLISION_ART_DIR/bundle.complete.json" \
  --governed-root "$ROOT" "${COLLISION_GOVERNED_ARGS[@]}" \
  --expected-root "$COLLISION_FINAL_ROOT" \
  --vendor-path "$COLLISION_VENDOR_PATH"
"${PYTHON[@]}" "$EVIDENCE" validate-bundle --art-dir "$COLLISION_ART_DIR" \
  --manifest "$COLLISION_ART_DIR/manifest.json" \
  --digest "$COLLISION_ART_DIR/manifest.digest" \
  --commit "$COLLISION_ART_DIR/bundle.complete.json" \
  --artifact-root "$COLLISION_ART_DIR" >/dev/null

validate_child_reference environment_collision collision-fln-amv.10

# ---- nested fln-amv.13 collision resource-bound evidence bundle -----------------------
# Reuse the fail-closed child helpers with a fresh identity and directory. The
# child is disjoint from fln-amv.10: it binds the 1,000-entry resource model,
# kills the inline-promotion threshold mutant, restores exact bytes, and proves
# clean recovery before publishing its own commit marker.
COLLISION_BEAD="fln-amv.13"
COLLISION_SCENARIO="environment_resource_collision"
COLLISION_RUN_ID="$RUN_ID-resource-collision-fln-amv-13"
COLLISION_ART_DIR="$ART_DIR/resource-collision-fln-amv.13"
COLLISION_LOG="$COLLISION_ART_DIR/run.ndjson"
COLLISION_HUMAN="$COLLISION_ART_DIR/human.log"
COLLISION_VENDOR_BINDING="$COLLISION_ART_DIR/vendor-binding.json"
COLLISION_SEQ=0
COLLISION_START_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
COLLISION_TEST="pmap::tests::environment_collision_resource_e2e_emits_detailed_evidence"
COLLISION_CARGO_ARGV="cargo test --locked -q -p fln-env $COLLISION_TEST -- --exact --nocapture"

if ! COLLISION_INPUT_ROOT="$(collision_hash_live)"; then
  note "FAIL: cannot hash fln-amv.13 governed inputs"
  exit 2
fi
if [ -e "$COLLISION_ART_DIR" ] || [ -L "$COLLISION_ART_DIR" ]; then
  note "FAIL: refusing reused collision resource evidence directory $COLLISION_ART_DIR"
  exit 2
fi
mkdir "$COLLISION_ART_DIR"
"${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ROOT" \
  --vendor-path "$COLLISION_VENDOR_PATH" --output "$COLLISION_VENDOR_BINDING" \
  --artifact-root "$COLLISION_ART_DIR" || {
    note "FAIL: cannot bind the pinned Reference tree for fln-amv.13"
    exit 2
  }

COLLISION_LIVE_SUBJECT_SHA="$(collision_file_sha256 "$ROOT/crates/fln-env/src/pmap.rs")"
COLLISION_LIVE_HEAD="$(git -C "$ROOT" rev-parse HEAD)"
collision_emit_event --new-log --string event run_start \
  --json-value argv '["scripts/e2e/env_snapshots.sh"]' \
  --string cwd "$ROOT" \
  --append-string claim_ids fln-amv.13-resource-bounded-collisions \
  --append-string invariant_ids FL-INV-01 \
  --append-string gate_ids PG-5 \
  --string parity_ledger_row not_applicable_internal_data_structure_resource_bound \
  --string epoch lean-v4.32.0 --string mode sound --string profile e2e \
  --string platform "$(uname -srm)" \
  --json-value host_facts "$("${PYTHON[@]}" -c 'import json,platform; print(json.dumps({"system":platform.system(),"release":platform.release(),"machine":platform.machine(),"python":platform.python_version()},separators=(",",":")))')" \
  --integer thread_count 32 --string seed partition-rotation-v1 \
  --json-value thread_matrix '[1,8,32]' \
  --string cache_state "$COLLISION_CACHE_STATE" \
  --string input_root "$COLLISION_INPUT_ROOT" \
  --string vendor_binding vendor-binding.json \
  --string live_head "$COLLISION_LIVE_HEAD" \
  --string live_subject_sha256 "$COLLISION_LIVE_SUBJECT_SHA" \
  --json-value budgets "{\"capture_bytes_per_stream\":$COLLISION_CAPTURE_BYTES,\"output_budget_bytes\":$COLLISION_OUTPUT_BUDGET_BYTES,\"step_timeout_ms\":$COLLISION_TIMEOUT_MS,\"kill_grace_ms\":$COLLISION_GRACE_MS,\"max_collision_cardinality\":1000,\"max_construction_comparisons\":18000,\"max_append_fresh_nodes\":18}"
: > "$COLLISION_HUMAN"

COLLISION_PRISTINE_SOURCE="$COLLISION_ART_DIR/pmap.pristine.rs"
cp -- "$OVERLAY/fln-env/src/pmap.rs" "$COLLISION_PRISTINE_SOURCE"
COLLISION_PRISTINE_SHA="$(collision_file_sha256 "$COLLISION_PRISTINE_SOURCE")"
if [ "$COLLISION_PRISTINE_SHA" != "$COLLISION_LIVE_SUBJECT_SHA" ]; then
  collision_note "FAIL: recovered overlay pmap.rs is not byte-identical to the live resource subject"
  exit 3
fi
COLLISION_PRISTINE_SUBJECT_ROOT="$(collision_hash_subject "$OVERLAY" fln-env/src/pmap.rs)"

# Positive: the live subject emits exactly the v1 rows and pinned roots for
# thread counts 1, 8, and 32.
COLLISION_POSITIVE_SUBJECT_BEFORE="$(collision_hash_subject "$ROOT" crates/fln-env/src/pmap.rs)"
COLLISION_POSITIVE_GLOBAL_BEFORE="$(collision_hash_live)"
collision_supervise resource_positive "$ROOT" none false \
  env FLN_ENV_E2E_RUN_ID="$COLLISION_RUN_ID" \
  FLN_ENV_E2E_STDOUT_ARTIFACT=resource_positive.out \
  FLN_ENV_E2E_STDERR_ARTIFACT=resource_positive.err \
  FLN_ENV_E2E_ARGV="$COLLISION_CARGO_ARGV" \
  FLN_ENV_E2E_CACHE_STATE="$COLLISION_CACHE_STATE" \
  CARGO_TARGET_DIR=target_local \
  cargo test --locked -q -p fln-env \
  pmap::tests::environment_collision_resource_e2e_emits_detailed_evidence \
  -- --exact --nocapture
collision_assert_supervisor resource_positive pass 0 0 false
COLLISION_POSITIVE_SUBJECT_AFTER="$(collision_hash_subject "$ROOT" crates/fln-env/src/pmap.rs)"
COLLISION_POSITIVE_GLOBAL_AFTER="$(collision_hash_live)"
collision_assert_unchanged resource_positive \
  "$COLLISION_POSITIVE_SUBJECT_BEFORE" "$COLLISION_POSITIVE_SUBJECT_AFTER" \
  "$COLLISION_POSITIVE_GLOBAL_BEFORE" "$COLLISION_POSITIVE_GLOBAL_AFTER"
COLLISION_POSITIVE_VALIDATION="$COLLISION_ART_DIR/resource_positive.validation.json"
"${PYTHON[@]}" "$EVIDENCE" validate-environment-resource-collision \
  --file "$COLLISION_LAST_OUT" --stderr-file "$COLLISION_LAST_ERR" --phase positive \
  --expected-run-id "$COLLISION_RUN_ID" --observed-exit "$COLLISION_LAST_CHILD" \
  --expected-cwd "$ROOT/crates/fln-env" --expected-argv "$COLLISION_CARGO_ARGV" \
  --expected-stdout-artifact resource_positive.out \
  --expected-stderr-artifact resource_positive.err \
  --expected-cache-state "$COLLISION_CACHE_STATE" \
  --artifact-root "$COLLISION_ART_DIR" --output "$COLLISION_POSITIVE_VALIDATION"
collision_record_step resource_positive \
  "environment-resource-collision/1:positive/pass/wrapper=0/child=0/sha256=$COLLISION_LIVE_SUBJECT_SHA" \
  "$COLLISION_LAST_CLASS/wrapper=$COLLISION_LAST_RC/child=$COLLISION_LAST_CHILD/sha256=$COLLISION_LIVE_SUBJECT_SHA" \
  resource_positive.validation.json pass 0 0 \
  "$COLLISION_POSITIVE_SUBJECT_BEFORE" "$COLLISION_POSITIVE_SUBJECT_AFTER" \
  "$COLLISION_POSITIVE_GLOBAL_BEFORE" "$COLLISION_POSITIVE_GLOBAL_AFTER"

# Mutant: promote an inline bucket one entry too early. The exact test must fail
# at the cloned-inline-work assertion; both split streams are checked before the
# strict validator accepts the kill.
if ! "${PYTHON[@]}" - "$OVERLAY/fln-env/src/pmap.rs" <<'PY'
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
source = path.read_bytes()
anchor = b"if new_entries.len() <= INLINE_COLLISION_MAX {"
replacement = b"if new_entries.len() < INLINE_COLLISION_MAX {"
if source.count(anchor) != 1:
    raise SystemExit("inline-threshold mutation anchor count is not exactly one")
path.write_bytes(source.replace(anchor, replacement, 1))
PY
then
  collision_note "FAIL: inline-threshold mutation did not match exactly one overlay anchor"
  exit 2
fi
COLLISION_MUTANT_SHA="$(collision_file_sha256 "$OVERLAY/fln-env/src/pmap.rs")"
if [ "$COLLISION_MUTANT_SHA" = "$COLLISION_PRISTINE_SHA" ]; then
  collision_note "FAIL: inline-threshold mutation did not change the overlay subject"
  exit 2
fi
COLLISION_MUTANT_SUBJECT_BEFORE="$(collision_hash_subject "$OVERLAY" fln-env/src/pmap.rs)"
COLLISION_MUTANT_GLOBAL_BEFORE="$(collision_hash_live)"
collision_supervise resource_mutant "$OVERLAY" 101 true \
  env FLN_ENV_E2E_RUN_ID="$COLLISION_RUN_ID" \
  FLN_ENV_E2E_STDOUT_ARTIFACT=resource_mutant.out \
  FLN_ENV_E2E_STDERR_ARTIFACT=resource_mutant.err \
  FLN_ENV_E2E_ARGV="$COLLISION_CARGO_ARGV" \
  FLN_ENV_E2E_CACHE_STATE="$COLLISION_CACHE_STATE" \
  CARGO_TARGET_DIR="$OVERLAY/target" \
  cargo test --locked -q -p fln-env \
  pmap::tests::environment_collision_resource_e2e_emits_detailed_evidence \
  -- --exact --nocapture
collision_assert_supervisor resource_mutant fail 1 101 true
if ! grep -Fq "$COLLISION_TEST --- FAILED" "$COLLISION_LAST_OUT"; then
  collision_note "FAIL: resource mutant stdout lacks the exact failed test identity"
  exit 1
fi
if ! grep -Fq 'left: 28' "$COLLISION_LAST_ERR" || \
   ! grep -Fq 'right: 36' "$COLLISION_LAST_ERR"; then
  collision_note "FAIL: resource mutant stderr lacks the intended inline-threshold assertion"
  exit 1
fi
COLLISION_MUTANT_SUBJECT_AFTER="$(collision_hash_subject "$OVERLAY" fln-env/src/pmap.rs)"
COLLISION_MUTANT_GLOBAL_AFTER="$(collision_hash_live)"
collision_assert_unchanged resource_mutant \
  "$COLLISION_MUTANT_SUBJECT_BEFORE" "$COLLISION_MUTANT_SUBJECT_AFTER" \
  "$COLLISION_MUTANT_GLOBAL_BEFORE" "$COLLISION_MUTANT_GLOBAL_AFTER"
COLLISION_MUTANT_VALIDATION="$COLLISION_ART_DIR/resource_mutant.validation.json"
"${PYTHON[@]}" "$EVIDENCE" validate-environment-resource-collision \
  --file "$COLLISION_LAST_OUT" --stderr-file "$COLLISION_LAST_ERR" --phase mutant \
  --expected-run-id "$COLLISION_RUN_ID" --observed-exit "$COLLISION_LAST_CHILD" \
  --expected-stdout-artifact resource_mutant.out \
  --expected-stderr-artifact resource_mutant.err \
  --artifact-root "$COLLISION_ART_DIR" --output "$COLLISION_MUTANT_VALIDATION"
collision_record_step resource_mutant \
  "environment-resource-collision/1:mutant/fail/wrapper=1/child=101/pristine_sha256=$COLLISION_PRISTINE_SHA" \
  "$COLLISION_LAST_CLASS/wrapper=$COLLISION_LAST_RC/child=$COLLISION_LAST_CHILD/mutant_sha256=$COLLISION_MUTANT_SHA" \
  resource_mutant.validation.json fail 1 101 \
  "$COLLISION_MUTANT_SUBJECT_BEFORE" "$COLLISION_MUTANT_SUBJECT_AFTER" \
  "$COLLISION_MUTANT_GLOBAL_BEFORE" "$COLLISION_MUTANT_GLOBAL_AFTER"

# Recovery: restore the retained pristine bytes before rerunning the exact
# resource test and requiring all pinned roots and bounds again.
cp -- "$COLLISION_PRISTINE_SOURCE" "$OVERLAY/fln-env/src/pmap.rs"
COLLISION_RECOVERED_SHA="$(collision_file_sha256 "$OVERLAY/fln-env/src/pmap.rs")"
if [ "$COLLISION_RECOVERED_SHA" != "$COLLISION_PRISTINE_SHA" ]; then
  collision_note "FAIL: recovered resource pmap.rs does not byte-match the pristine overlay"
  exit 3
fi
COLLISION_RECOVERY_SUBJECT_BEFORE="$(collision_hash_subject "$OVERLAY" fln-env/src/pmap.rs)"
if [ "$COLLISION_RECOVERY_SUBJECT_BEFORE" != "$COLLISION_PRISTINE_SUBJECT_ROOT" ]; then
  collision_note "FAIL: recovered resource pmap.rs tree root differs from the pristine overlay"
  exit 3
fi
COLLISION_RECOVERY_GLOBAL_BEFORE="$(collision_hash_live)"
collision_supervise resource_recovery "$OVERLAY" none false \
  env FLN_ENV_E2E_RUN_ID="$COLLISION_RUN_ID" \
  FLN_ENV_E2E_STDOUT_ARTIFACT=resource_recovery.out \
  FLN_ENV_E2E_STDERR_ARTIFACT=resource_recovery.err \
  FLN_ENV_E2E_ARGV="$COLLISION_CARGO_ARGV" \
  FLN_ENV_E2E_CACHE_STATE="$COLLISION_CACHE_STATE" \
  CARGO_TARGET_DIR="$OVERLAY/target" \
  cargo test --locked -q -p fln-env \
  pmap::tests::environment_collision_resource_e2e_emits_detailed_evidence \
  -- --exact --nocapture
collision_assert_supervisor resource_recovery pass 0 0 false
COLLISION_RECOVERY_SUBJECT_AFTER="$(collision_hash_subject "$OVERLAY" fln-env/src/pmap.rs)"
COLLISION_RECOVERY_GLOBAL_AFTER="$(collision_hash_live)"
collision_assert_unchanged resource_recovery \
  "$COLLISION_RECOVERY_SUBJECT_BEFORE" "$COLLISION_RECOVERY_SUBJECT_AFTER" \
  "$COLLISION_RECOVERY_GLOBAL_BEFORE" "$COLLISION_RECOVERY_GLOBAL_AFTER"
COLLISION_RECOVERY_VALIDATION="$COLLISION_ART_DIR/resource_recovery.validation.json"
"${PYTHON[@]}" "$EVIDENCE" validate-environment-resource-collision \
  --file "$COLLISION_LAST_OUT" --stderr-file "$COLLISION_LAST_ERR" --phase recovery \
  --expected-run-id "$COLLISION_RUN_ID" --observed-exit "$COLLISION_LAST_CHILD" \
  --expected-cwd "$OVERLAY/fln-env" --expected-argv "$COLLISION_CARGO_ARGV" \
  --expected-stdout-artifact resource_recovery.out \
  --expected-stderr-artifact resource_recovery.err \
  --expected-cache-state "$COLLISION_CACHE_STATE" \
  --artifact-root "$COLLISION_ART_DIR" --output "$COLLISION_RECOVERY_VALIDATION"
collision_record_step resource_recovery \
  "environment-resource-collision/1:recovery/pass/wrapper=0/child=0/sha256=$COLLISION_PRISTINE_SHA" \
  "$COLLISION_LAST_CLASS/wrapper=$COLLISION_LAST_RC/child=$COLLISION_LAST_CHILD/sha256=$COLLISION_RECOVERED_SHA" \
  resource_recovery.validation.json pass 0 0 \
  "$COLLISION_RECOVERY_SUBJECT_BEFORE" "$COLLISION_RECOVERY_SUBJECT_AFTER" \
  "$COLLISION_RECOVERY_GLOBAL_BEFORE" "$COLLISION_RECOVERY_GLOBAL_AFTER"

COLLISION_FINAL_ROOT="$(collision_hash_live)"
if [ "$COLLISION_FINAL_ROOT" != "$COLLISION_INPUT_ROOT" ]; then
  collision_note "FAIL: collision resource child changed its governed live input"
  exit 3
fi
collision_emit_event --string event run_end --string verdict pass \
  --string reason_code all_obligations_passed --integer process_exit 0 \
  --string active_step resource_recovery \
  --integer duration_ns "$(( $("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())') - COLLISION_START_NS ))" \
  --string cleanup_status retained_by_policy \
  --string final_state "$COLLISION_FINAL_ROOT" \
  --string logical_root "$COLLISION_FINAL_ROOT" \
  --string receipt_root not_applicable_internal_resource_bound \
  --string first_divergence none \
  --string evidence_manifest manifest.json \
  --string bundle_commit bundle.complete.json \
  --string evidence_state pending_bundle_commit

"${PYTHON[@]}" "$EVIDENCE" validate-run --file "$COLLISION_LOG" \
  --schema "$COLLISION_SCHEMA" --expected-verdict pass \
  --expected-active-stage resource_recovery \
  --artifact-root "$COLLISION_ART_DIR" \
  --output "$COLLISION_ART_DIR/run.validation.json"
"${PYTHON[@]}" "$EVIDENCE" manifest --art-dir "$COLLISION_ART_DIR" \
  --output "$COLLISION_ART_DIR/manifest.json" \
  --digest-output "$COLLISION_ART_DIR/manifest.digest" \
  --run-id "$COLLISION_RUN_ID" --bead "$COLLISION_BEAD" \
  --scenario "$COLLISION_SCENARIO" --verdict pass \
  --input-root "$COLLISION_INPUT_ROOT" --final-root "$COLLISION_FINAL_ROOT"
"${PYTHON[@]}" "$EVIDENCE" complete-bundle --art-dir "$COLLISION_ART_DIR" \
  --manifest "$COLLISION_ART_DIR/manifest.json" \
  --digest "$COLLISION_ART_DIR/manifest.digest" \
  --output "$COLLISION_ART_DIR/bundle.complete.json" \
  --governed-root "$ROOT" "${COLLISION_GOVERNED_ARGS[@]}" \
  --expected-root "$COLLISION_FINAL_ROOT" \
  --vendor-path "$COLLISION_VENDOR_PATH"
"${PYTHON[@]}" "$EVIDENCE" validate-bundle --art-dir "$COLLISION_ART_DIR" \
  --manifest "$COLLISION_ART_DIR/manifest.json" \
  --digest "$COLLISION_ART_DIR/manifest.digest" \
  --commit "$COLLISION_ART_DIR/bundle.complete.json" \
  --artifact-root "$COLLISION_ART_DIR" >/dev/null

validate_child_reference environment_resource_collision \
  resource-collision-fln-amv.13

ACTIVE_STEP=environment_resource_collision
set_final pass all_obligations_passed 0
exit 0
