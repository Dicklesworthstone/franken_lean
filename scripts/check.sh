#!/usr/bin/env bash
# scripts/check.sh — the single FrankenLean quality gate.
#
# Stages are append-only obligations: evidence harness self-test, fmt, check, clippy,
# tests, structural policy, exact Reference tree, and UBS.  Each command runs under a
# bounded supervisor that drains stdout/stderr to EOF, preserves useful head+tail
# captures, applies a monotonic timeout and total-output budget, and cancels the whole
# child process group.  The published fln.check/2 NDJSON has exactly one final terminal
# record plus a write-once SHA-256 artifact manifest.
#
# Exit taxonomy: 0 pass; 1 stage failure; 2 setup/evidence/internal fault;
# 3 resource exhaustion or timeout (inconclusive); 129/130/143 HUP/INT/TERM cancellation.

set -Eeuo pipefail

case "${1:-}" in
  --help|-h)
    sed -n '2,17p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
    exit 0
    ;;
  --self-test|"") ;;
  *) echo "unknown argument: $1 (see --help)" >&2; exit 2 ;;
esac

command -v python3 >/dev/null 2>&1 || {
  echo "[check] setup failure: python3 is required by the evidence harness" >&2
  exit 2
}
command -v setsid >/dev/null 2>&1 || {
  echo "[check] setup failure: setsid is required by the evidence finalizer" >&2
  exit 2
}

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO"
EVIDENCE="$REPO/scripts/evidence.py"
SCHEMA="fln.check/2"
SCENARIO="quality_gate"
BEAD="franken_lean-rur"
RUN_ID="check-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_ROOT="${FLN_CHECK_ART_ROOT:-$REPO/target/check}"
ART_DIR="${FLN_CHECK_ART_DIR:-$ART_ROOT/$RUN_ID}"
NDJSON="$ART_DIR/run.ndjson"
HUMAN="$ART_DIR/human.log"
CAPTURE_BYTES="${FLN_CHECK_CAPTURE_BYTES:-262144}"
OUTPUT_BUDGET_BYTES="${FLN_CHECK_OUTPUT_BUDGET_BYTES:-67108864}"
STAGE_TIMEOUT_MS="${FLN_CHECK_STAGE_TIMEOUT_MS:-1200000}"
KILL_GRACE_MS="${FLN_CHECK_KILL_GRACE_MS:-2000}"
PLANT="${FLN_CHECK_PLANT:-}"
if [ -n "${FLN_CHECK_PROFILE:-}" ]; then
  PROFILE="$FLN_CHECK_PROFILE"
elif [ "${1:-}" = --self-test ]; then
  PROFILE=self-test-driver
elif [ -n "$PLANT" ]; then
  PROFILE=self-test-plant
elif [ "${CI:-}" = true ]; then
  PROFILE=ci
else
  PROFILE=local
fi
THREAD_COUNT="${FLN_CHECK_THREAD_COUNT:-1}"
SEED="${FLN_CHECK_SEED:-none}"
CACHE_STATE="${FLN_CHECK_CACHE_STATE:-uncontrolled}"
START_NS="$(python3 -c 'import time; print(time.monotonic_ns())')"
SEQ=0
ACTIVE_STAGE="setup"
ACTIVE_RUNNER_PID=""
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
FINALIZER_PID=""
FINALIZATION_SIGNAL=""
FINALIZATION_SIGNAL_EXIT=0
FINAL_ROOT_FILE="$ART_DIR/final-root.txt"
EVENT_COMMAND=()
INPUT_PATHS=(
  Cargo.toml Cargo.lock SUITE.lock rust-toolchain.toml ci crates tools
  vendor/NOTICE
  scripts/check.sh scripts/evidence.py scripts/verify_vendor_tree.sh
  scripts/e2e/structure_gate.sh scripts/e2e/closure_audit.sh
  scripts/e2e/structural_gate.sh scripts/e2e/core_observables.sh
  scripts/e2e/hash_identity.sh
  scripts/extract/gen_core_fixtures.sh scripts/extract/gen_core_fixtures.lean
  scripts/extract/convert_blake3_vectors.py
  .github/workflows/ci.yml
)
HASH_ARGS=()
GOVERNED_ARGS=()
for input_path in "${INPUT_PATHS[@]}"; do
  HASH_ARGS+=(--path "$input_path")
  GOVERNED_ARGS+=(--governed-path "$input_path")
done

UBS_SCOPE="${FLN_UBS_SCOPE:-changed}"
[ "${CI:-}" = true ] && UBS_SCOPE="${FLN_UBS_SCOPE:-all-tracked}"
UBS_INVENTORY="$ART_DIR/ubs-inventory.json"
VENDOR_PATH="vendor/lean4-src"
VENDOR_BINDING="$ART_DIR/vendor-binding.json"
mkdir -p "$(dirname "$ART_DIR")"
if [ -e "$ART_DIR" ] || [ -L "$ART_DIR" ]; then
  echo "[check] setup failure: refusing reused evidence directory: $ART_DIR" >&2
  exit 2
fi
mkdir "$ART_DIR"
python3 "$EVIDENCE" ubs-inventory --root "$REPO" --scope "$UBS_SCOPE" \
  --output "$UBS_INVENTORY" --artifact-root "$ART_DIR" || {
    echo "[check] setup failure: cannot inventory UBS inputs" >&2
    exit 2
  }
python3 "$EVIDENCE" vendor-binding --root "$REPO" --vendor-path "$VENDOR_PATH" \
  --output "$VENDOR_BINDING" --artifact-root "$ART_DIR" || {
    echo "[check] setup failure: cannot verify the pinned Reference tree" >&2
    exit 2
  }
INPUT_ROOT="$(python3 "$EVIDENCE" hash-tree --root "$REPO" "${HASH_ARGS[@]}" \
  --inventory "$UBS_INVENTORY" --vendor-path "$VENDOR_PATH")" || {
    echo "[check] setup failure: cannot hash governed inputs" >&2
    exit 2
  }
HOST_FACTS_JSON="$(python3 - <<'PY'
import json, platform
print(json.dumps({
    "machine": platform.machine(),
    "python": platform.python_version(),
    "release": platform.release(),
    "system": platform.system(),
}, sort_keys=True, separators=(",", ":")))
PY
)"

RUN_ARGV_JSON="$(python3 - "${BASH_SOURCE[0]}" "${1:-}" <<'PY'
import json, sys
argv = [sys.argv[1]]
if sys.argv[2]:
    argv.append(sys.argv[2])
print(json.dumps(argv, separators=(",", ":")))
PY
)"

build_event_command() {
  local sequence="$SEQ"
  SEQ=$((SEQ + 1))
  EVENT_COMMAND=(python3 "$EVIDENCE" emit --file "$NDJSON" --artifact-root "$ART_DIR" \
    --string schema "$SCHEMA" \
    --string run_id "$RUN_ID" \
    --string bead "$BEAD" \
    --string scenario "$SCENARIO" \
    --integer sequence "$sequence" \
    --integer monotonic_ns "$(python3 -c 'import time; print(time.monotonic_ns())')" \
    --string wall_time_utc "$(date -u -Is)" \
    "$@")
}

emit_event() {
  build_event_command "$@"
  "${EVENT_COMMAND[@]}"
}

note() {
  printf '[check] %s\n' "$*" | tee -a "$HUMAN" >&2
}

set_final() {
  FINAL_SET=1
  FINAL_VERDICT="$1"
  FINAL_REASON="$2"
  FINAL_EXIT="$3"
}

# Called from the EXIT-trap finalizer.
# shellcheck disable=SC2317
build_terminal_command() {
  local final_root="$1" first_divergence=none
  if [ "$FINAL_VERDICT" != pass ]; then first_divergence="$FINAL_REASON"; fi
  build_event_command \
    --string event run_end \
    --string verdict "$FINAL_VERDICT" \
    --string reason_code "$FINAL_REASON" \
    --integer process_exit "$FINAL_EXIT" \
    --string active_stage "$ACTIVE_STAGE" \
    --integer duration_ns "$(( $(python3 -c 'import time; print(time.monotonic_ns())') - START_NS ))" \
    --string cleanup_status retained_by_policy \
    --string final_state "$final_root" \
    --string logical_root "$final_root" \
    --string receipt_root not_applicable_structural_gate \
    --string first_divergence "$first_divergence" \
    --string evidence_manifest manifest.json \
    --string bundle_commit bundle.complete.json \
    --string evidence_state pending_bundle_commit
}

# Invoked from signal handling; bounded so evidence publication cannot hang forever.
# shellcheck disable=SC2317
stop_active_runner() {
  local name="$1" pid="$ACTIVE_RUNNER_PID" state cleanup_rc=0
  [ -n "$pid" ] || return 0
  kill -s "$name" "$pid" 2>/dev/null || true
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
        if ! python3 "$EVIDENCE" emergency-kill --readiness "$ACTIVE_READINESS" \
          --expected-wrapper-pid "$pid" --expected-stage-id "$ACTIVE_STAGE" \
          >/dev/null 2>&1; then
          cleanup_rc=1
        fi
      else
        cleanup_rc=1
      fi
    fi
  fi
  if [ "$cleanup_rc" -ne 0 ]; then
    ACTIVE_RUNNER_PID=""
    ACTIVE_READINESS=""
    return "$cleanup_rc"
  fi
  wait "$pid" 2>/dev/null || true
  ACTIVE_RUNNER_PID=""
  ACTIVE_READINESS=""
  return "$cleanup_rc"
}

# Invoked indirectly by trap.
# shellcheck disable=SC2317
on_signal() {
  local name="$1" exit_code="$2"
  trap '' HUP INT TERM
  if [ "$SPAWNING" -eq 1 ] && [ -z "$ACTIVE_RUNNER_PID" ]; then
    PENDING_SIGNAL="$name"
    PENDING_SIGNAL_EXIT="$exit_code"
    trap 'on_signal HUP 129' HUP
    trap 'on_signal INT 130' INT
    trap 'on_signal TERM 143' TERM
    return 0
  fi
  if [ -n "$ACTIVE_RUNNER_PID" ]; then
    if ! stop_active_runner "$name"; then
      set_final internal_fault process_tree_cleanup_unproven 2
      exit 2
    fi
  fi
  set_final cancelled "signal_$name" "$exit_code"
  exit "$exit_code"
}

# Invoked only while the EXIT finalizer is active. A signal before the bundle marker
# interrupts the current publication command and leaves the evidence uncommitted.
# shellcheck disable=SC2317
on_finalizer_signal() {
  local name="$1" exit_code="$2"
  if [ -z "$FINALIZATION_SIGNAL" ]; then
    FINALIZATION_SIGNAL="$name"
    FINALIZATION_SIGNAL_EXIT="$exit_code"
  fi
  if [ -n "$FINALIZER_PID" ]; then
    kill -s "$name" -- "-$FINALIZER_PID" 2>/dev/null || true
    kill -s "$name" "$FINALIZER_PID" 2>/dev/null || true
  fi
}

# shellcheck disable=SC2317
run_finalizer_command() {
  local rc=0 state
  [ -z "$FINALIZATION_SIGNAL" ] || return 125
  setsid -- "$@" &
  FINALIZER_PID=$!
  while true; do
    wait "$FINALIZER_PID" && rc=0 || rc=$?
    if [ ! -r "/proc/$FINALIZER_PID/stat" ]; then break; fi
    state="$(awk '{print $3}' "/proc/$FINALIZER_PID/stat" 2>/dev/null || printf X)"
    if [ "$state" = Z ]; then
      wait "$FINALIZER_PID" && rc=0 || rc=$?
      break
    fi
    if [ -n "$FINALIZATION_SIGNAL" ]; then
      kill -s "$FINALIZATION_SIGNAL" -- "-$FINALIZER_PID" 2>/dev/null || true
    fi
  done
  FINALIZER_PID=""
  return "$rc"
}

# shellcheck disable=SC2317
abort_if_finalizer_signalled() {
  if [ -n "$FINALIZATION_SIGNAL" ]; then
    note "CANCELLED: signal_$FINALIZATION_SIGNAL before evidence bundle commit: $ART_DIR"
    exit "$FINALIZATION_SIGNAL_EXIT"
  fi
}

# Invoked indirectly by trap.
# shellcheck disable=SC2317
on_exit() {
  local observed_rc="$1" final_root="unavailable" publish_rc=0 hash_rc=0 bundle_rc=0
  trap - EXIT
  trap 'on_finalizer_signal HUP 129' HUP
  trap 'on_finalizer_signal INT 130' INT
  trap 'on_finalizer_signal TERM 143' TERM
  set +e
  if [ "$FINALIZING" -ne 0 ]; then
    exit 2
  fi
  FINALIZING=1
  if [ "$FINAL_SET" -eq 0 ]; then
    if [ "$observed_rc" -eq 0 ]; then
      set_final internal_fault uncommitted_success 2
    else
      set_final internal_fault unexpected_shell_exit 2
    fi
  fi
  run_finalizer_command python3 "$EVIDENCE" hash-tree --root "$REPO" \
    "${HASH_ARGS[@]}" --inventory "$UBS_INVENTORY" --vendor-path "$VENDOR_PATH" \
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
  if [ "$TERMINAL_EMITTED" -eq 0 ]; then
    build_terminal_command "$final_root"
    if run_finalizer_command "${EVENT_COMMAND[@]}"; then
      TERMINAL_EMITTED=1
    else
      publish_rc=2
    fi
    abort_if_finalizer_signalled
  fi
  if [ "$publish_rc" -eq 0 ]; then
    run_finalizer_command python3 "$EVIDENCE" validate-run \
      --file "$NDJSON" --schema "$SCHEMA" --expected-verdict "$FINAL_VERDICT" \
      --artifact-root "$ART_DIR" --output "$ART_DIR/run.validation.json" || publish_rc=2
    abort_if_finalizer_signalled
  fi
  if [ "$publish_rc" -eq 0 ]; then
    run_finalizer_command python3 "$EVIDENCE" manifest \
      --art-dir "$ART_DIR" \
      --output "$ART_DIR/manifest.json" \
      --digest-output "$ART_DIR/manifest.digest" \
      --run-id "$RUN_ID" --bead "$BEAD" --scenario quality_gate \
      --verdict "$FINAL_VERDICT" --input-root "$INPUT_ROOT" --final-root "$final_root" \
      || publish_rc=2
    abort_if_finalizer_signalled
  fi
  if [ "$publish_rc" -eq 0 ]; then
    run_finalizer_command python3 "$EVIDENCE" complete-bundle --art-dir "$ART_DIR" \
      --manifest "$ART_DIR/manifest.json" --digest "$ART_DIR/manifest.digest" \
      --output "$ART_DIR/bundle.complete.json" --governed-root "$REPO" \
      "${GOVERNED_ARGS[@]}" --expected-root "$final_root" \
      --inventory "$UBS_INVENTORY" --vendor-path "$VENDOR_PATH" || bundle_rc=$?
    if [ "$bundle_rc" -eq 0 ] && [ -e "$ART_DIR/bundle.complete.json" ]; then
      # Marker publication is the linearization point. From here, signals are
      # post-commit and validation decides whether that marker is complete.
      trap '' HUP INT TERM
      python3 "$EVIDENCE" validate-bundle --art-dir "$ART_DIR" \
        --manifest "$ART_DIR/manifest.json" --digest "$ART_DIR/manifest.digest" \
        --commit "$ART_DIR/bundle.complete.json" --artifact-root "$ART_DIR" \
        >/dev/null || publish_rc=2
    else
      abort_if_finalizer_signalled
      publish_rc=2
    fi
  fi
  if [ "$publish_rc" -ne 0 ]; then
    note "INTERNAL FAULT: evidence bundle did not publish completely: $ART_DIR"
    exit 2
  fi
  if [ "$FINAL_VERDICT" = pass ]; then
    printf '[check] PASS — all obligations green; committed evidence: %s\n' "$ART_DIR" >&2
  else
    printf '[check] %s — reason=%s; committed evidence: %s\n' \
      "$FINAL_VERDICT" "$FINAL_REASON" "$ART_DIR" >&2
  fi
  exit "$FINAL_EXIT"
}

trap 'on_signal HUP 129' HUP
trap 'on_signal INT 130' INT
trap 'on_signal TERM 143' TERM
trap 'on_exit $?' EXIT

emit_event \
  --new-log \
  --string event run_start \
  --json-value argv "$RUN_ARGV_JSON" \
  --string cwd "$REPO" \
  --append-string claim_ids FLN-W1-SCAFFOLD \
  --append-string claim_ids FLN-QUALITY-GATE \
  --append-string invariant_ids FL-INV-01 \
  --append-string invariant_ids FL-INV-07 \
  --append-string invariant_ids D1 \
  --append-string invariant_ids D3 \
  --append-string gate_ids W1 \
  --append-string gate_ids G0-10 \
  --string parity_ledger_row not_applicable_structural_governance \
  --string epoch lean-v4.32.0 \
  --string mode sound \
  --string profile "$PROFILE" \
  --string platform "$(uname -srm)" \
  --json-value host_facts "$HOST_FACTS_JSON" \
  --integer thread_count "$THREAD_COUNT" \
  --string seed "$SEED" \
  --string cache_state "$CACHE_STATE" \
  --string input_root "$INPUT_ROOT" \
  --string ubs_inventory ubs-inventory.json \
  --string vendor_binding vendor-binding.json \
  --json-value budgets "{\"capture_bytes_per_stream\":$CAPTURE_BYTES,\"output_budget_bytes\":$OUTPUT_BUDGET_BYTES,\"stage_timeout_ms\":$STAGE_TIMEOUT_MS,\"kill_grace_ms\":$KILL_GRACE_MS}" \
  --string rustc "$(rustc --version 2>/dev/null || printf unknown)" \
  --string planted "$PLANT"
: > "$HUMAN"

read_meta_field() {
  python3 - "$1" "$2" <<'PY'
import json, pathlib, sys
value = json.loads(pathlib.Path(sys.argv[1]).read_text())
field = value[sys.argv[2]]
if isinstance(field, bool):
    print("true" if field else "false")
elif field is None:
    print("null")
else:
    print(field)
PY
}

run_stage() {
  local name="$1"; shift
  local meta="$ART_DIR/$name.meta.json" out="$ART_DIR/$name.out" err="$ART_DIR/$name.err"
  local ready="$ART_DIR/$name.ready.json"
  local wrapper_rc classification reason recorded_wrapper planted=false
  local -a argv=("$@") semantic_args=()
  ACTIVE_STAGE="$name"
  if [ "$PLANT" = "$name" ]; then
    argv=(false)
    planted=true
    semantic_args=(--semantic-failure-exit 1)
  else
    case "$name" in
      shellcheck|fmt|structure-guard|vendor-tree|ubs)
        semantic_args=(--semantic-failure-exit 1)
        ;;
      check|clippy|test)
        semantic_args=(--semantic-failure-exit 101)
        ;;
    esac
  fi
  note "stage=$name: ${argv[*]}"
  local -a runner=(python3 "$EVIDENCE" run
    --cwd "$REPO"
    --metadata "$meta"
    --stdout "$out"
    --stderr "$err"
    --readiness "$ready"
    --artifact-root "$ART_DIR"
    --capture-bytes "$CAPTURE_BYTES"
    --output-budget-bytes "$OUTPUT_BUDGET_BYTES"
    --timeout-ms "$STAGE_TIMEOUT_MS"
    --grace-ms "$KILL_GRACE_MS"
    --stage-id "$name" "${semantic_args[@]}")
  [ "$planted" = true ] && runner+=(--planted)
  runner+=(-- "${argv[@]}")
  SPAWNING=1
  "${runner[@]}" &
  ACTIVE_RUNNER_PID=$!
  ACTIVE_READINESS="$ready"
  SPAWNING=0
  if [ -n "$PENDING_SIGNAL" ]; then
    local pending_name="$PENDING_SIGNAL" pending_exit="$PENDING_SIGNAL_EXIT"
    PENDING_SIGNAL=""
    stop_active_runner "$pending_name"
    set_final cancelled "signal_$pending_name" "$pending_exit"
    exit "$pending_exit"
  fi
  if wait "$ACTIVE_RUNNER_PID"; then
    wrapper_rc=0
  else
    wrapper_rc=$?
  fi
  ACTIVE_RUNNER_PID=""
  ACTIVE_READINESS=""
  if [ ! -f "$meta" ]; then
    emit_event --string event stage --string stage "$name" \
      --string outcome internal_fault --string reason_code missing_supervisor_metadata \
      --string expected exit_zero --string actual metadata_unavailable \
      --boolean supervisor_available false --integer wrapper_exit "$wrapper_rc"
    set_final internal_fault missing_supervisor_metadata 2
    exit 2
  fi
  classification="$(read_meta_field "$meta" classification)"
  reason="$(read_meta_field "$meta" reason_code)"
  recorded_wrapper="$(read_meta_field "$meta" wrapper_exit)"
  emit_event \
    --string event stage \
    --string stage "$name" \
    --string outcome "$classification" \
    --string reason_code "$reason" \
    --string expected exit_zero \
    --string actual "$classification" \
    --integer wrapper_exit "$wrapper_rc" \
    --json-file supervisor "$meta"
  if [ "$recorded_wrapper" != "$wrapper_rc" ]; then
    set_final internal_fault "$name:wrapper_exit_mismatch" 2
    exit 2
  fi
  if [ "$wrapper_rc" -eq 0 ] && [ "$classification" = pass ]; then
    note "ok stage=$name"
    return 0
  fi
  note "$classification stage=$name reason=$reason wrapper_exit=$wrapper_rc"
  note "captured stderr tail follows ($name)"
  tail -n 40 "$err" >&2 || true
  case "$wrapper_rc" in
    1) set_final fail "$name:$reason" 1; exit 1 ;;
    3) set_final inconclusive "$name:$reason" 3; exit 3 ;;
    4) set_final cancelled "$name:$reason" 4; exit 4 ;;
    *) set_final internal_fault "$name:$reason" 2; exit 2 ;;
  esac
}

skip_stage() {
  local name="$1" reason="$2"
  ACTIVE_STAGE="$name"
  emit_event --string event stage --string stage "$name" --string outcome skipped \
    --string reason_code typed_limitation --string expected not_applicable \
    --string actual skipped --string limitation "$reason"
  echo "[check] skip stage=$name: $reason" >&2
}

self_test() {
  local failures=0 stage rc child="$ART_DIR" child_pid
  for stage in evidence-self-test shellcheck fmt check clippy test structure-guard vendor-tree ubs; do
    echo "[check:self-test] planting failure in stage=$stage" >&2
    child="$ART_DIR/selftest-$stage"
    SPAWNING=1
    FLN_CHECK_PLANT="$stage" FLN_CHECK_ART_DIR="$child" \
      FLN_CHECK_PROFILE=self-test-plant bash "${BASH_SOURCE[0]}" \
      > "$ART_DIR/selftest-$stage.console.out" \
      2> "$ART_DIR/selftest-$stage.console.err" &
    child_pid=$!
    ACTIVE_RUNNER_PID="$child_pid"
    ACTIVE_READINESS=""
    SPAWNING=0
    if [ -n "$PENDING_SIGNAL" ]; then
      local pending_name="$PENDING_SIGNAL" pending_exit="$PENDING_SIGNAL_EXIT"
      PENDING_SIGNAL=""
      stop_active_runner "$pending_name"
      set_final cancelled "signal_$pending_name" "$pending_exit"
      exit "$pending_exit"
    fi
    if wait "$child_pid"; then rc=0; else rc=$?; fi
    ACTIVE_RUNNER_PID=""
    if [ "$rc" -eq 1 ] && python3 "$EVIDENCE" validate-run \
      --file "$child/run.ndjson" --schema "$SCHEMA" --expected-verdict fail \
      --expected-active-stage "$stage" --expected-planted-stage "$stage" \
      --artifact-root "$ART_DIR" --output "$ART_DIR/selftest-$stage.validation.json" \
      && python3 "$EVIDENCE" validate-bundle --art-dir "$child" \
        --manifest "$child/manifest.json" --digest "$child/manifest.digest" \
        --commit "$child/bundle.complete.json" --artifact-root "$child" >/dev/null; then
      echo "[check:self-test] ok — planted stage=$stage was caught and terminal" >&2
      emit_event --string event self_test --string stage "$stage" \
        --boolean ok true --integer planted_exit "$rc" --string artifact "selftest-$stage"
    else
      echo "[check:self-test] FAIL — stage=$stage exit=$rc" >&2
      failures=$((failures + 1))
      emit_event --string event self_test --string stage "$stage" \
        --boolean ok false --integer planted_exit "$rc" --string artifact "selftest-$stage"
    fi
  done

  echo "[check:self-test] sending TERM during child run initialization" >&2
  child="$ART_DIR/selftest-cancel-term"
  SPAWNING=1
  FLN_CHECK_ART_DIR="$child" FLN_CHECK_PROFILE=self-test-cancellation \
    bash "${BASH_SOURCE[0]}" \
    > "$ART_DIR/selftest-cancel-term.console.out" \
    2> "$ART_DIR/selftest-cancel-term.console.err" &
  child_pid=$!
  ACTIVE_RUNNER_PID="$child_pid"
  ACTIVE_READINESS=""
  SPAWNING=0
  if [ -n "$PENDING_SIGNAL" ]; then
    local pending_name="$PENDING_SIGNAL" pending_exit="$PENDING_SIGNAL_EXIT"
    PENDING_SIGNAL=""
    stop_active_runner "$pending_name"
    set_final cancelled "signal_$pending_name" "$pending_exit"
    exit "$pending_exit"
  fi
  for _ in $(seq 1 500); do
    if compgen -G "$child/*.ready.json" >/dev/null; then break; fi
    sleep 0.02
  done
  if ! compgen -G "$child/*.ready.json" >/dev/null; then
    kill -TERM "$child_pid" 2>/dev/null || true
    wait "$child_pid" 2>/dev/null || true
    rc=2
  else
    kill -TERM "$child_pid" 2>/dev/null || true
    if wait "$child_pid"; then rc=0; else rc=$?; fi
  fi
  ACTIVE_RUNNER_PID=""
  if [ "$rc" -eq 143 ] && python3 "$EVIDENCE" validate-run \
    --file "$child/run.ndjson" --schema "$SCHEMA" --expected-verdict cancelled \
    --artifact-root "$ART_DIR" --output "$ART_DIR/selftest-cancel-term.validation.json" \
    && python3 "$EVIDENCE" validate-bundle --art-dir "$child" \
      --manifest "$child/manifest.json" --digest "$child/manifest.digest" \
      --commit "$child/bundle.complete.json" --artifact-root "$child" >/dev/null; then
    echo "[check:self-test] ok — TERM produced one validated cancelled terminal" >&2
    emit_event --string event self_test --string stage cancel-term \
      --boolean ok true --integer planted_exit "$rc" --string artifact selftest-cancel-term
  else
    echo "[check:self-test] FAIL — TERM child exit=$rc" >&2
    failures=$((failures + 1))
    emit_event --string event self_test --string stage cancel-term \
      --boolean ok false --integer planted_exit "$rc" --string artifact selftest-cancel-term
  fi
  if [ "$failures" -eq 0 ]; then
    set_final pass self_test_complete 0
    exit 0
  fi
  set_final fail self_test_failure 1
  echo "[check:self-test] FAIL — $failures planted stage(s) escaped" >&2
  exit 1
}

if [ "${1:-}" = "--self-test" ]; then
  self_test
fi

# --locked makes Cargo.lock drift a failure instead of silently rewriting it.
run_stage evidence-self-test python3 scripts/evidence.py self-test \
  --art-dir "$ART_DIR/evidence-self-test"
run_stage shellcheck shellcheck scripts/check.sh scripts/verify_vendor_tree.sh \
  scripts/e2e/structure_gate.sh scripts/e2e/closure_audit.sh scripts/e2e/structural_gate.sh \
  scripts/e2e/core_observables.sh scripts/extract/gen_core_fixtures.sh \
  scripts/e2e/hash_identity.sh
run_stage fmt cargo fmt --check
run_stage check cargo check --locked --all-targets
run_stage clippy cargo clippy --locked --all-targets -- -D warnings
run_stage test cargo test --locked
run_stage structure-guard cargo run -q --locked -p structure-guard -- --root "$REPO" --robot
run_stage vendor-tree bash scripts/verify_vendor_tree.sh

# The exact file set was materialized before run_start and is part of INPUT_ROOT.
python3 "$EVIDENCE" validate-ubs-inventory --root "$REPO" \
  --inventory "$UBS_INVENTORY" >/dev/null
UBS_COUNT="$(read_meta_field "$UBS_INVENTORY" count)"
if [ "$PLANT" = ubs ]; then
  run_stage ubs ubs --version
elif command -v ubs >/dev/null 2>&1; then
  if [ "$UBS_COUNT" -gt 0 ]; then
    run_stage ubs python3 "$EVIDENCE" exec-ubs-inventory \
      --root "$REPO" --inventory "$UBS_INVENTORY" -- ubs --ci
    python3 "$EVIDENCE" validate-ubs-inventory --root "$REPO" \
      --inventory "$UBS_INVENTORY" >/dev/null
  else
    skip_stage ubs "validated zero-file project-authored $UBS_SCOPE UBS scope"
  fi
elif [ "${CI:-}" = true ] || [ "${FLN_REQUIRE_UBS:-0}" = 1 ]; then
  run_stage ubs ubs --version
else
  skip_stage ubs "ubs binary not on PATH (local typed limitation; CI is fail-closed)"
fi

ACTIVE_STAGE="complete"
set_final pass all_stages_green 0
exit 0
