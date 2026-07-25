#!/usr/bin/env bash
# vellum_naming_no_mock_e2e.sh — real-path E2E for the fln-7gr6 naming contract:
# the suite-wide subsystem-name registry (Quill reserved for the Frankensearch
# lexical engine; the FrankenLean parser/macro subsystem is Vellum), the governed
# current-vocabulary scan, seeded stale-name/collision/interrupted-publication
# mutants (each killed by its named lane for the intended reason, then byte-verified
# restoration and a green recovery), a frozen-fixture determinism byte-compare, and
# a final real-tree recheck. Canonical fln.e2e/2 NDJSON, separately linked
# telemetry, independent validation via evidence.py, retained artifacts.

set -Eeuo pipefail

PYTHON_BIN="$(command -v python3 || true)"
[ -n "$PYTHON_BIN" ] || {
  echo "[vellum_naming] setup failure: python3 is required" >&2
  exit 2
}
PYTHON=("$PYTHON_BIN" -I -S)
HOSTILE_PYTHON_CONFIGURATION=()
while IFS= read -r environment_name; do
  [[ "$environment_name" == PYTHON* ]] \
    && HOSTILE_PYTHON_CONFIGURATION+=("$environment_name")
done < <(compgen -e | LC_ALL=C sort)
if ((${#HOSTILE_PYTHON_CONFIGURATION[@]} > 0)); then
  printf '[vellum_naming] setup failure: sealed_interpreter_hostile_environment names=%s\n' \
    "$(IFS=,; printf '%s' "${HOSTILE_PYTHON_CONFIGURATION[*]}")" >&2
  exit 2
fi
command -v setsid >/dev/null 2>&1 || {
  echo "[vellum_naming] setup failure: setsid is required" >&2
  exit 2
}

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
EVIDENCE="$ROOT/scripts/evidence.py"
SCHEMA="fln.e2e/2"
BEAD="fln-7gr6"
SCENARIO="vellum_naming_no_mock_e2e"
RUN_ID="vellum-naming-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_ROOT="${FLN_E2E_ART_ROOT:-$ROOT/target/e2e}"
ART_DIR="$ART_ROOT/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
HUMAN="$ART_DIR/human.log"
TELEMETRY="$ART_DIR/telemetry.ndjson"
CAPTURE_BYTES="${FLN_E2E_CAPTURE_BYTES:-262144}"
OUTPUT_BUDGET_BYTES="${FLN_E2E_OUTPUT_BUDGET_BYTES:-16777216}"
TIMEOUT_MS="${FLN_E2E_TIMEOUT_MS:-1800000}"
GRACE_MS="${FLN_E2E_KILL_GRACE_MS:-2000}"
# Capped at 30000 by evidence.py's process-identity guards (MAX_PROCESS_IDENTITY_WAIT_MS).
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
# The governed identity of THIS lane: the naming contract's own surfaces. Sibling
# crates and .beads/issues.jsonl are scanned as live inputs but change legitimately
# on the shared multi-agent tree while this lane runs; their identity is enforced
# by the workspace gate (scripts/check.sh), not re-hashed here.
INPUT_PATHS=(
  SUITE.lock rust-toolchain.toml vendor/NOTICE
  ci/SUBSYSTEM_REGISTRY.txt ci/CLOSURE_ALLOWLIST.txt
  README.md AGENTS.md COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md
  crates/fln-conformance/src/naming.rs
  crates/fln-conformance/tests/subsystem_name_registry.rs
  crates/fln-conformance/tests/reserved_name_collision_model.rs
  crates/fln-conformance/tests/vellum_surface_inventory.rs
  crates/fln-conformance/tests/generated_name_drift_guard.rs
  crates/fln-parse/src/lib.rs crates/fln-syntax/src/lib.rs
  crates/fln-core/src/name.rs crates/fln-core/src/diag.rs
  scripts/evidence.py scripts/e2e/vellum_naming_no_mock_e2e.sh
)
SUBJECT_PATHS=(
  ci/SUBSYSTEM_REGISTRY.txt ci/CLOSURE_ALLOWLIST.txt
  README.md AGENTS.md COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md
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

if ! INPUT_ROOT="$("${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
  --vendor-path "$VENDOR_PATH")"; then
  echo "[vellum_naming] setup failure: cannot hash governed inputs" >&2
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

mkdir -p "$(dirname "$ART_DIR")"
if ! mkdir "$ART_DIR" 2>/dev/null; then
  # No trap is armed until after this atomic single-writer claim succeeds.
  echo "[vellum_naming] evidence directory already claimed: $ART_DIR" >&2
  exit 2
fi
"${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ROOT" --vendor-path "$VENDOR_PATH" \
  --output "$VENDOR_BINDING" --artifact-root "$ART_DIR" || {
    echo "[vellum_naming] setup failure: cannot verify the pinned Reference tree" >&2
    exit 2
  }

note() { printf '[vellum_naming] %s\n' "$*" | tee -a "$HUMAN" >&2; }

# Separately linked telemetry stream: coarse per-step timing facts, joined to the
# run by run_id, never mixed into the semantic run.ndjson.
telemetry() { # telemetry <step> <wrapper_exit>
  printf '{"schema":"fln-naming-telemetry/1","run_id":"%s","step":"%s","wrapper_exit":%s,"elapsed_ms":%d}\n' \
    "$RUN_ID" "$1" "$2" \
    "$(( ( $("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())') - START_NS ) / 1000000 ))" \
    >> "$TELEMETRY"
}

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

mark_process_tree_cleanup_unproven() {
  PROCESS_TREE_CLEANUP_UNPROVEN=1
  trap '' HUP INT TERM
  set_final internal_fault process_tree_cleanup_unproven 2
}

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
    if [ -s "$FINALIZATION_DECISION" ]; then
      return 0
    fi
    note "CANCELLED: signal_$FINALIZATION_SIGNAL won evidence bundle decision: $ART_DIR"
    exit "$FINALIZATION_SIGNAL_EXIT"
  fi
}

# shellcheck disable=SC2317
on_exit() {
  local observed_rc="$1" final_root="unavailable" publish_rc=0 hash_rc=0
  local first_divergence=none
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
      --string receipt_root not_applicable_naming_governance \
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
    printf '[vellum_naming] PASS — committed artifacts and retained fixtures: %s\n' \
      "$ART_DIR" >&2
  fi
  exit "$FINAL_EXIT"
}

trap 'on_signal HUP 129' HUP
trap 'on_signal INT 130' INT
trap 'on_signal TERM 143' TERM
trap 'FINALIZER_TRANSITION=1 on_exit "$?"' EXIT

emit_event --new-log --string event run_start \
  --json-value argv '["scripts/e2e/vellum_naming_no_mock_e2e.sh"]' --string cwd "$ROOT" \
  --append-string claim_ids FLN-7GR6-VELLUM-NAMING-CONTRACT \
  --append-string claim_ids FLN-7GR6-RESERVED-NAME-COLLISION-GUARD \
  --append-string invariant_ids D7 --append-string invariant_ids FL-INV-07 \
  --append-string gate_ids G0-4 \
  --string parity_ledger_row not_applicable_naming_governance \
  --string epoch lean-v4.32.0 --string mode sound --string profile e2e \
  --string platform "$(uname -srm)" --integer thread_count 1 \
  --json-value host_facts "$HOST_FACTS_JSON" \
  --string seed deterministic-scan-v1 --string cache_state "${FLN_E2E_CACHE_STATE:-uncontrolled}" \
  --string input_root "$INPUT_ROOT" \
  --string vendor_binding vendor-binding.json \
  --json-value budgets "{\"capture_bytes_per_stream\":$CAPTURE_BYTES,\"output_budget_bytes\":$OUTPUT_BUDGET_BYTES,\"step_timeout_ms\":$TIMEOUT_MS,\"kill_grace_ms\":$GRACE_MS}"
: > "$HUMAN"
: > "$TELEMETRY"

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
  telemetry "$step" "$LAST_RC"
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

# A suite lane: run one named fln-conformance test binary (optionally filtered to
# one assertion and re-rooted at a scratch fixture) and demand an exact verdict.
# Expected-fail lanes must also show the INTENDED reason in the captured output —
# a lane that fails for the wrong reason is a contract failure, not a kill.
suite_step() { # suite_step <step> <subject_root> <naming_root> <suite> <filter|-> <expect: pass|fail> <reason-needle|->
  local step="$1" subject="$2" naming_root="$3" suite="$4" filter="$5" expect="$6" needle="$7"
  local -a filter_args=() env_args=(env)
  if [ "$filter" != - ]; then
    filter_args=("$filter" --exact)
  fi
  if [ "$naming_root" != - ]; then
    env_args+=("FLN_NAMING_ROOT=$naming_root")
  fi
  if [ -n "${FLN_NAMING_REPORT_OUT:-}" ]; then
    env_args+=("FLN_NAMING_REPORT=$FLN_NAMING_REPORT_OUT")
  fi
  local root_label="$naming_root"
  [ "$root_label" = - ] && root_label=live
  snapshot_before "$subject" "$step"
  note "running suite step=$step suite=$suite root=$root_label expected=$expect"
  if [ "$expect" = pass ]; then
    supervise "$step" "${env_args[@]}" cargo test --locked -q -p fln-conformance \
      --test "$suite" -- --nocapture "${filter_args[@]}"
  else
    supervise "$step" --semantic-failure-exit 101 \
      "${env_args[@]}" cargo test --locked -q -p fln-conformance \
      --test "$suite" -- --nocapture "${filter_args[@]}"
  fi
  inspect_supervisor "$step"
  snapshot_after "$subject" "$step"
  local expected_classification expected_wrapper expected_child
  if [ "$expect" = pass ]; then
    expected_classification=pass; expected_wrapper=0; expected_child=0
  else
    expected_classification=fail; expected_wrapper=1; expected_child=101
  fi
  if [ "$LAST_CLASSIFICATION" != "$expected_classification" ] || \
     [ "$LAST_RC" -ne "$expected_wrapper" ] || \
     [ "$LAST_CHILD_EXIT" != "$expected_child" ]; then
    record_contract_failure "$step" \
      "suite_contract_expected_${expected_classification}_${expected_wrapper}_${expected_child}" \
      "$SUBJECT_BEFORE" "$SUBJECT_AFTER" "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
  fi
  # libtest prints panic text to stderr under --nocapture; check both captures.
  if [ "$needle" != - ] && ! grep -qF -- "$needle" "$LAST_OUT" "$LAST_ERR"; then
    record_contract_failure "$step" "intended_reason_missing:$needle" \
      "$SUBJECT_BEFORE" "$SUBJECT_AFTER" "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
  fi
  if [ "$SUBJECT_BEFORE" != "$SUBJECT_AFTER" ] || \
     [ "$GLOBAL_BEFORE" != "$GLOBAL_AFTER" ]; then
    note "INCONCLUSIVE step=$step: governed_inputs_changed"
    set_final inconclusive "$step:governed_inputs_changed" 3
    exit 3
  fi
  record_step "$step" pass \
    "$suite:$expect/wrapper=$expected_wrapper/child=$expected_child" \
    "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
    "${LAST_OUT#"$ART_DIR"/}" "$expected_classification" "$expected_wrapper" \
    "$expected_child" "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
    "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
}

# Byte-verified restore of one seeded scratch file from the live tree.
# The positional parameters are intentionally expanded by the supervised child.
# shellcheck disable=SC2016
restore_file() { # restore_file <step> <relpath> <scratch_root>
  local step="$1" relpath="$2" scratch="$3"
  run_pass_step "$step" "$ROOT" \
    bash -c 'set -euo pipefail; cp -- "$1/$3" "$2/$3"; cmp -s -- "$1/$3" "$2/$3"' \
    vellum-restore "$ROOT" "$scratch" "$relpath"
}

# ---- phase 1: the real tree, all four named suites --------------------------------
suite_step registry_gate "$ROOT" - subsystem_name_registry - pass -
suite_step collision_model "$ROOT" - reserved_name_collision_model - pass -
suite_step drift_guard "$ROOT" - generated_name_drift_guard - pass -
FLN_NAMING_REPORT_OUT="$ART_DIR/scan-live.report.ndjson"
suite_step surface_scan "$ROOT" - vellum_surface_inventory - pass -
FLN_NAMING_REPORT_OUT=""
if [ ! -s "$ART_DIR/scan-live.report.ndjson" ]; then
  note "FAIL: the live scan published no canonical report"
  set_final fail surface_scan:missing_canonical_report 1
  exit 1
fi

# ---- phase 2: frozen scratch fixture --------------------------------------------
SCRATCH_ROOT="$ART_DIR/fixtures"
mkdir "$SCRATCH_ROOT"
SEEDED="$SCRATCH_ROOT/seeded"
mkdir "$SEEDED"
# One supervised copy (before/after source hashes) prevents a hybrid fixture. The
# scanner-visible universe is copied; build products and the Reference tree are not.
# The positional parameters are intentionally expanded by the supervised child.
# shellcheck disable=SC2016
run_pass_step copy_fixture "$ROOT" \
  bash -c 'set -euo pipefail; tar -C "$1" -cf - ci contracts crates scripts .github .beads/issues.jsonl README.md AGENTS.md COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md ABI_CONTRACT.md OLEAN_CONTRACT.md KERNEL_CONTRACT.md | tar -C "$2" -xf -' \
  vellum-copy "$ROOT" "$SEEDED"
suite_step scratch_baseline "$SEEDED" "$SEEDED" vellum_surface_inventory \
  the_real_tree_has_no_stale_reserved_names pass -

# ---- phase 3: seeded mutants, each killed for its intended reason ----------------
# m1: a stale doc reference (no owner citation) — the inventory lane kills it.
printf '\nThe Quill parser feeds the elaborator.\n' >> "$SEEDED/README.md"
suite_step seeded_stale_doc "$SEEDED" "$SEEDED" vellum_surface_inventory \
  the_real_tree_has_no_stale_reserved_names fail "stale reserved-name references"
restore_file restore_stale_doc README.md "$SEEDED"
suite_step recovery_stale_doc "$SEEDED" "$SEEDED" vellum_surface_inventory \
  the_real_tree_has_no_stale_reserved_names pass -

# m2: a conflicting registry re-registration — the registry lane kills it.
printf 'row Quill | franken_lean | parser engine | - | - | active | conflicting re-registration\n' \
  >> "$SEEDED/ci/SUBSYSTEM_REGISTRY.txt"
suite_step seeded_registry_conflict "$SEEDED" "$SEEDED" subsystem_name_registry \
  the_real_registry_parses_and_validates fail "name-collision"
restore_file restore_registry_conflict ci/SUBSYSTEM_REGISTRY.txt "$SEEDED"
suite_step recovery_registry_conflict "$SEEDED" "$SEEDED" subsystem_name_registry \
  the_real_registry_parses_and_validates pass -

# m3: a lowercase drift in a generated artifact label — the drift lane kills it.
"${PYTHON[@]}" - "$SEEDED/ci/CLOSURE_ALLOWLIST.txt" <<'PY'
import pathlib, sys
path = pathlib.Path(sys.argv[1])
text = path.read_text(encoding="utf-8")
mutated = text.replace(
    "reason=§21 crate map: Vellum parser engine",
    "reason=§21 crate map: quill parser engine",
)
if mutated == text:
    raise SystemExit("seed was a no-op")
path.write_text(mutated, encoding="utf-8")
PY
suite_step seeded_generated_drift "$SEEDED" "$SEEDED" generated_name_drift_guard \
  real_ci_artifacts_are_drift_free fail "ci artifact drift"
restore_file restore_generated_drift ci/CLOSURE_ALLOWLIST.txt "$SEEDED"
suite_step recovery_generated_drift "$SEEDED" "$SEEDED" generated_name_drift_guard \
  real_ci_artifacts_are_drift_free pass -

# m4: an interrupted candidate publication — typed stale-candidate, then exact
# recovery: quarantine the candidate INTO the evidence bundle (never silent
# adoption), prove the published registry byte-intact, and gate green.
head -c 512 "$SEEDED/ci/SUBSYSTEM_REGISTRY.txt" \
  > "$SEEDED/ci/SUBSYSTEM_REGISTRY.txt.candidate"
suite_step seeded_stale_candidate "$SEEDED" "$SEEDED" subsystem_name_registry \
  the_real_registry_parses_and_validates fail "stale-candidate"
mkdir "$ART_DIR/quarantine"
# The positional parameters are intentionally expanded by the supervised child.
# shellcheck disable=SC2016
run_pass_step quarantine_candidate "$ROOT" \
  bash -c 'set -euo pipefail; mv -- "$1" "$2"; test ! -e "$1"; test -s "$2"' \
  vellum-quarantine "$SEEDED/ci/SUBSYSTEM_REGISTRY.txt.candidate" \
  "$ART_DIR/quarantine/SUBSYSTEM_REGISTRY.txt.candidate"
# shellcheck disable=SC2016
run_pass_step verify_publication_intact "$ROOT" \
  bash -c 'set -euo pipefail; cmp -s -- "$1/ci/SUBSYSTEM_REGISTRY.txt" "$2/ci/SUBSYSTEM_REGISTRY.txt"' \
  vellum-verify "$ROOT" "$SEEDED"
suite_step recovery_stale_candidate "$SEEDED" "$SEEDED" subsystem_name_registry \
  the_real_registry_parses_and_validates pass -

# ---- phase 4: determinism — two scans of the frozen fixture, byte-identical ------
FLN_NAMING_REPORT_OUT="$ART_DIR/scan-a.report.ndjson"
suite_step determinism_scan_a "$SEEDED" "$SEEDED" vellum_surface_inventory \
  the_real_tree_has_no_stale_reserved_names pass -
FLN_NAMING_REPORT_OUT="$ART_DIR/scan-b.report.ndjson"
suite_step determinism_scan_b "$SEEDED" "$SEEDED" vellum_surface_inventory \
  the_real_tree_has_no_stale_reserved_names pass -
FLN_NAMING_REPORT_OUT=""
# The positional parameters are intentionally expanded by the supervised child.
# shellcheck disable=SC2016
run_pass_step determinism_byte_compare "$ROOT" \
  bash -c 'set -euo pipefail; cmp -s -- "$1" "$2"; test -s "$1"' \
  vellum-determinism "$ART_DIR/scan-a.report.ndjson" "$ART_DIR/scan-b.report.ndjson"

# ---- phase 5: final real recheck -------------------------------------------------
suite_step final_real_recheck "$ROOT" - vellum_surface_inventory - pass -

ACTIVE_STEP=complete
set_final pass all_scenarios_satisfied 0
exit 0
