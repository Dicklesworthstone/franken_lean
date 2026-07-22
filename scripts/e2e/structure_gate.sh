#!/usr/bin/env bash
# Real-path E2E for fln-8mj's structural policy. Every child is bounded and its
# structure-guard/2 output is parsed as JSON with an exact ordered finding contract.
# Negative fixtures are immutable evidence; recovery uses independent clean fixtures.

set -Eeuo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
EVIDENCE="$ROOT/scripts/evidence.py"
SCHEMA="fln.e2e/2"
BEAD="fln-8mj"
SCENARIO="structure_gate"
RUN_ID="structure-gate-$(date -u +%Y%m%dT%H%M%SZ)-$$"
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
READY_WAIT_MS="${FLN_E2E_READY_WAIT_MS:-5000}"
START_NS="$(python3 -c 'import time; print(time.monotonic_ns())')"
SEQ=0
ACTIVE_STEP="setup"
ACTIVE_RUNNER_PID=""
ACTIVE_READINESS=""
SPAWNING=0
PENDING_SIGNAL=""
PENDING_SIGNAL_EXIT=0
LAST_META=""
LAST_READY=""
FINAL_SET=0
FINAL_VERDICT="internal_fault"
FINAL_REASON="uncommitted_exit"
FINAL_EXIT=2
TERMINAL_EMITTED=0
FINALIZING=0
INPUT_PATHS=(
  Cargo.toml Cargo.lock SUITE.lock rust-toolchain.toml ci crates tools
  vendor/NOTICE
  scripts/check.sh scripts/evidence.py scripts/verify_vendor_tree.sh
  scripts/e2e/structure_gate.sh scripts/e2e/closure_audit.sh
  scripts/e2e/structural_gate.sh .github/workflows/ci.yml
)
SUBJECT_PATHS=(Cargo.toml Cargo.lock SUITE.lock rust-toolchain.toml ci crates tools)
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

note() {
  printf '[structure_gate] %s\n' "$*" | tee -a "$HUMAN" >&2
}

emit_event() {
  local sequence="$SEQ"
  SEQ=$((SEQ + 1))
  python3 "$EVIDENCE" emit --file "$LOG" --artifact-root "$ART_DIR" \
    --string schema "$SCHEMA" --string run_id "$RUN_ID" --string bead "$BEAD" \
    --string scenario "$SCENARIO" --integer sequence "$sequence" \
    --integer monotonic_ns "$(python3 -c 'import time; print(time.monotonic_ns())')" \
    --string wall_time_utc "$(date -u -Is)" "$@"
}

set_final() { FINAL_SET=1; FINAL_VERDICT="$1"; FINAL_REASON="$2"; FINAL_EXIT="$3"; }

# Invoked from signal handling; success means the wrapper is absent or a zombie,
# so a following shell wait cannot become an unbounded teardown operation.
# shellcheck disable=SC2317
bounded_pid_exit_wait() {
  local pid="$1" limit_ms="$2" state
  local ticks=$(( (limit_ms + 19) / 20 )) index
  for ((index = 0; index < ticks; index += 1)); do
    if [ ! -r "/proc/$pid/stat" ]; then return 0; fi
    state="$(awk '{print $3}' "/proc/$pid/stat" 2>/dev/null || printf X)"
    if [ "$state" = Z ]; then return 0; fi
    sleep 0.02
  done
  return 1
}

# Invoked from signal handling; bounded readiness waiting prevents a signal from
# killing the Python wrapper before it has installed handlers and published its PGID.
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

# Invoked from signal handling; bounded so publication cannot hang indefinitely.
# shellcheck disable=SC2317
stop_active_runner() {
  local name="$1" pid="$ACTIVE_RUNNER_PID"
  [ -n "$pid" ] || return 0
  bounded_readiness_wait "$pid" "$ACTIVE_READINESS" "$READY_WAIT_MS" || true
  kill -s "$name" "$pid" 2>/dev/null || true
  if ! bounded_pid_exit_wait "$pid" "$((READY_WAIT_MS + 3 * GRACE_MS))"; then
    if [ -s "$ACTIVE_READINESS" ]; then
      python3 "$EVIDENCE" emergency-kill --readiness "$ACTIVE_READINESS" \
        --expected-wrapper-pid "$pid" --expected-stage-id "$ACTIVE_STEP" \
        >/dev/null 2>&1 || true
    fi
    kill -KILL "$pid" 2>/dev/null || true
    bounded_pid_exit_wait "$pid" "$GRACE_MS" || true
  fi
  if bounded_pid_exit_wait "$pid" 20; then wait "$pid" 2>/dev/null || true; fi
  ACTIVE_RUNNER_PID=""
  ACTIVE_READINESS=""
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
  if [ -n "$ACTIVE_RUNNER_PID" ]; then stop_active_runner "$name"; fi
  set_final cancelled "signal_$name" "$exit_code"
  exit "$exit_code"
}

# Invoked indirectly by trap.
# shellcheck disable=SC2317
on_exit() {
  local observed_rc="$1" final_root="unavailable" first_divergence="none"
  local publish_rc=0 hash_rc=0
  trap - EXIT; trap '' HUP INT TERM; set +e
  if [ "$FINALIZING" -ne 0 ]; then exit 2; fi
  FINALIZING=1
  if [ "$FINAL_SET" -eq 0 ]; then
    set_final internal_fault "$([ "$observed_rc" -eq 0 ] && printf uncommitted_success || printf unexpected_shell_exit)" 2
  fi
  final_root="$(python3 "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path "$VENDOR_PATH" 2>/dev/null)" \
    || hash_rc=$?
  if [ "$hash_rc" -ne 0 ]; then
    final_root="unavailable"
    set_final internal_fault final_workspace_hash_unavailable 2
  elif [ "$FINAL_VERDICT" = pass ] && [ "$final_root" != "$INPUT_ROOT" ]; then
    set_final fail final_workspace_changed 1
  fi
  if [ "$FINAL_VERDICT" != pass ]; then first_divergence="$FINAL_REASON"; fi
  if [ "$TERMINAL_EMITTED" -eq 0 ]; then
    if emit_event --string event run_end --string verdict "$FINAL_VERDICT" \
      --string reason_code "$FINAL_REASON" --integer process_exit "$FINAL_EXIT" \
      --string active_step "$ACTIVE_STEP" \
      --integer duration_ns "$(( $(python3 -c 'import time; print(time.monotonic_ns())') - START_NS ))" \
      --string cleanup_status retained_by_policy --string final_state "$final_root" \
      --string logical_root "$final_root" --string receipt_root "$final_root" \
      --string first_divergence "$first_divergence" \
      --string evidence_manifest manifest.json \
      --string bundle_commit bundle.complete.json \
      --string evidence_state pending_bundle_commit; then
      TERMINAL_EMITTED=1
    else
      publish_rc=2
    fi
  fi
  if [ "$publish_rc" -eq 0 ]; then
    python3 "$EVIDENCE" validate-run --file "$LOG" --schema "$SCHEMA" \
      --expected-verdict "$FINAL_VERDICT" --artifact-root "$ART_DIR" \
      --output "$ART_DIR/run.validation.json" || publish_rc=2
  fi
  if [ "$publish_rc" -eq 0 ]; then
    python3 "$EVIDENCE" manifest --art-dir "$ART_DIR" \
      --output "$ART_DIR/manifest.json" --digest-output "$ART_DIR/manifest.digest" \
      --run-id "$RUN_ID" --bead "$BEAD" --scenario "$SCENARIO" \
      --verdict "$FINAL_VERDICT" --input-root "$INPUT_ROOT" --final-root "$final_root" \
      || publish_rc=2
  fi
  if [ "$publish_rc" -eq 0 ]; then
    python3 "$EVIDENCE" complete-bundle --art-dir "$ART_DIR" \
      --manifest "$ART_DIR/manifest.json" --digest "$ART_DIR/manifest.digest" \
      --output "$ART_DIR/bundle.complete.json" --governed-root "$ROOT" \
      "${GOVERNED_ARGS[@]}" --expected-root "$final_root" \
      --vendor-path "$VENDOR_PATH" || publish_rc=2
  fi
  if [ "$publish_rc" -eq 0 ]; then
    python3 "$EVIDENCE" validate-bundle --art-dir "$ART_DIR" \
      --manifest "$ART_DIR/manifest.json" --digest "$ART_DIR/manifest.digest" \
      --commit "$ART_DIR/bundle.complete.json" --artifact-root "$ART_DIR" \
      >/dev/null || publish_rc=2
  fi
  if [ "$publish_rc" -ne 0 ]; then
    note "INTERNAL FAULT: incomplete bundle $ART_DIR"
    exit 2
  fi
  if [ "$FINAL_VERDICT" = pass ]; then
    printf '[structure_gate] PASS — committed artifacts and retained fixtures: %s\n' \
      "$ART_DIR" >&2
  fi
  exit "$FINAL_EXIT"
}

# Hash the complete governed input before creating an artifact directory. A broken
# preflight therefore cannot leave a directory that resembles a typed evidence run.
if ! INPUT_ROOT="$(python3 "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
  --vendor-path "$VENDOR_PATH")"; then
  echo "[structure_gate] setup failure: cannot hash governed inputs" >&2
  exit 2
fi
mkdir -p "$(dirname "$ART_DIR")"
if [ -e "$ART_DIR" ] || [ -L "$ART_DIR" ]; then
  echo "[structure_gate] refusing reused evidence directory: $ART_DIR" >&2
  exit 2
fi
mkdir "$ART_DIR"
python3 "$EVIDENCE" vendor-binding --root "$ROOT" --vendor-path "$VENDOR_PATH" \
  --output "$VENDOR_BINDING" --artifact-root "$ART_DIR" || {
    echo "[structure_gate] setup failure: cannot verify the pinned Reference tree" >&2
    exit 2
  }

# From the first artifact write onward every exit is typed. In particular, the
# human log is initialized only after run_start has committed successfully.
trap 'on_signal HUP 129' HUP
trap 'on_signal INT 130' INT
trap 'on_signal TERM 143' TERM
trap 'on_exit $?' EXIT

emit_event --new-log --string event run_start \
  --json-value argv '["scripts/e2e/structure_gate.sh"]' \
  --string cwd "$ROOT" \
  --append-string claim_ids FLN-W1-SCAFFOLD \
  --append-string claim_ids FLN-D3-STRUCTURAL-LAWS \
  --append-string invariant_ids FL-INV-01 \
  --append-string invariant_ids FL-INV-07 \
  --append-string invariant_ids D1 \
  --append-string invariant_ids D3 \
  --append-string gate_ids W1 \
  --append-string gate_ids G0-10 \
  --string parity_ledger_row not_applicable_structural_governance \
  --string epoch lean-v4.32.0 --string mode sound --string profile e2e \
  --string platform "$(uname -srm)" \
  --json-value host_facts "$(python3 -c 'import json,platform; print(json.dumps({"system":platform.system(),"release":platform.release(),"machine":platform.machine(),"python":platform.python_version()},separators=(",",":")))')" \
  --integer thread_count 1 \
  --string seed deterministic-fixture-v1 --string cache_state "${FLN_E2E_CACHE_STATE:-uncontrolled}" \
  --string input_root "$INPUT_ROOT" \
  --string vendor_binding vendor-binding.json \
  --json-value budgets "{\"capture_bytes_per_stream\":$CAPTURE_BYTES,\"output_budget_bytes\":$OUTPUT_BUDGET_BYTES,\"step_timeout_ms\":$TIMEOUT_MS,\"kill_grace_ms\":$GRACE_MS,\"readiness_wait_ms\":$READY_WAIT_MS}"

: > "$HUMAN"

read_meta_field() {
  python3 - "$1" "$2" <<'PY'
import json, pathlib, sys
value = json.loads(pathlib.Path(sys.argv[1]).read_text())[sys.argv[2]]
print("null" if value is None else value)
PY
}

read_meta_resource_field() {
  python3 - "$1" "$2" <<'PY'
import json, pathlib, sys
value = json.loads(pathlib.Path(sys.argv[1]).read_text())["resource"][sys.argv[2]]
if value is True:
    print("true")
elif value is False:
    print("false")
elif value is None:
    print("null")
else:
    print(value)
PY
}

hash_governed() {
  python3 "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path "$VENDOR_PATH"
}

hash_subject() {
  local subject="$1"
  if [ -f "$subject/Cargo.toml" ]; then
    python3 "$EVIDENCE" hash-tree --root "$subject" "${SUBJECT_HASH_ARGS[@]}"
  else
    python3 "$EVIDENCE" hash-tree --root "$subject" --path .
  fi
}

launch_supervisor() {
  local step="$1" capture_bytes="$2" output_budget="$3" timeout_ms="$4"
  shift 4
  local -a semantic_args=()
  while [ "${1:-}" = --semantic-failure-exit ]; do
    semantic_args+=(--semantic-failure-exit "$2")
    shift 2
  done
  LAST_META="$ART_DIR/$step.meta.json"
  LAST_OUT="$ART_DIR/$step.out"
  LAST_ERR="$ART_DIR/$step.err"
  LAST_READY="$ART_DIR/$step.ready.json"
  ACTIVE_STEP="$step"
  ACTIVE_READINESS="$LAST_READY"
  SPAWNING=1
  python3 "$EVIDENCE" run --cwd "$ROOT" --metadata "$LAST_META" \
    --stdout "$LAST_OUT" --stderr "$LAST_ERR" --readiness "$LAST_READY" \
    --artifact-root "$ART_DIR" --capture-bytes "$capture_bytes" \
    --output-budget-bytes "$output_budget" --timeout-ms "$timeout_ms" \
    --grace-ms "$GRACE_MS" --stage-id "$step" "${semantic_args[@]}" -- "$@" &
  ACTIVE_RUNNER_PID=$!
  SPAWNING=0
  if [ -n "$PENDING_SIGNAL" ]; then
    local pending_name="$PENDING_SIGNAL" pending_exit="$PENDING_SIGNAL_EXIT"
    PENDING_SIGNAL=""
    stop_active_runner "$pending_name"
    set_final cancelled "signal_$pending_name" "$pending_exit"
    exit "$pending_exit"
  fi
}

await_supervisor() {
  if wait "$ACTIVE_RUNNER_PID"; then LAST_RC=0; else LAST_RC=$?; fi
  ACTIVE_RUNNER_PID=""
  ACTIVE_READINESS=""
}

supervise() {
  local step="$1"
  shift
  launch_supervisor "$step" "$CAPTURE_BYTES" "$OUTPUT_BUDGET_BYTES" "$TIMEOUT_MS" "$@"
  await_supervisor
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
  local step="$1" expected_classification
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
    0) expected_classification=pass ;;
    1) expected_classification=fail ;;
    2) expected_classification=internal_fault ;;
    3) expected_classification=inconclusive ;;
    4) expected_classification=cancelled ;;
    *)
      set_final internal_fault "$step:unknown_wrapper_exit_$LAST_RC" 2
      exit 2
      ;;
  esac
  if [ "$LAST_META_WRAPPER" != "$LAST_RC" ] || \
     [ "$LAST_CLASSIFICATION" != "$expected_classification" ]; then
    set_final internal_fault "$step:supervisor_envelope_disagreement" 2
    exit 2
  fi
}

propagate_supervisor_taxonomy() {
  local step="$1" permitted_wrapper="$2"
  case "$LAST_RC" in
    2)
      set_final internal_fault "$step:$LAST_REASON" 2
      exit 2
      ;;
    3)
      if [ "$permitted_wrapper" != 3 ]; then
        set_final inconclusive "$step:$LAST_REASON" 3
        exit 3
      fi
      ;;
    4)
      if [ "$permitted_wrapper" != 4 ]; then
        set_final cancelled "$step:$LAST_REASON" 4
        exit 4
      fi
      ;;
  esac
}

record_contract_failure() {
  local step="$1" reason="$2" expected_class="$3" expected_wrapper="$4"
  local expected_child="$5" subject_before="$6" subject_after="$7"
  local global_before="$8" global_after="$9"
  note "FAIL step=$step: $reason"
  record_step "$step" fail "$reason" \
    "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" not_applicable \
    "$expected_class" "$expected_wrapper" "$expected_child" \
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
  propagate_supervisor_taxonomy "$step" none
  snapshot_after "$subject" "$step"
  if [ "$LAST_RC" -ne 0 ]; then
    record_contract_failure "$step" unexpected_command_failure pass 0 0 \
      "$SUBJECT_BEFORE" "$SUBJECT_AFTER" "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
  fi
  if [ "$SUBJECT_BEFORE" != "$SUBJECT_AFTER" ] || \
     [ "$GLOBAL_BEFORE" != "$GLOBAL_AFTER" ]; then
    record_contract_failure "$step" governed_inputs_changed pass 0 0 \
      "$SUBJECT_BEFORE" "$SUBJECT_AFTER" "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
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
  propagate_supervisor_taxonomy "$step" none
  snapshot_after "$fixture_root" "$step"
  if [ "$LAST_CLASSIFICATION" != "$expected_classification" ] || \
     [ "$LAST_RC" -ne "$expected_wrapper" ] || \
     [ "$LAST_CHILD_EXIT" != "$expected_exit" ]; then
    record_contract_failure "$step" \
      "supervisor_contract_expected_${expected_classification}_${expected_wrapper}_${expected_exit}" \
      "$expected_classification" "$expected_wrapper" "$expected_exit" \
      "$SUBJECT_BEFORE" "$SUBJECT_AFTER" "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
  fi
  if [ "$SUBJECT_BEFORE" != "$SUBJECT_AFTER" ] || \
     [ "$GLOBAL_BEFORE" != "$GLOBAL_AFTER" ]; then
    record_contract_failure "$step" governed_inputs_changed \
      "$expected_classification" "$expected_wrapper" "$expected_exit" \
      "$SUBJECT_BEFORE" "$SUBJECT_AFTER" "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
  fi
  if ! python3 "$EVIDENCE" validate-guard --file "$LAST_OUT" \
    --expected-exit "$expected_exit" --expected-verdict "$expected_verdict" \
    --expected-root "$fixture_root" --observed-exit "$LAST_CHILD_EXIT" \
    --artifact-root "$ART_DIR" "${validate_args[@]}" --output "$validation"; then
    record_contract_failure "$step" structure-guard/2_exact_contract_mismatch \
      "$expected_classification" "$expected_wrapper" "$expected_exit" \
      "$SUBJECT_BEFORE" "$SUBJECT_AFTER" "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
  fi
  record_step "$step" pass \
    "structure-guard/2:$expected_verdict/wrapper=$expected_wrapper/child=$expected_exit" \
    "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
    "${validation#"$ART_DIR"/}" "$expected_classification" "$expected_wrapper" \
    "$expected_exit" "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
    "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
}

copy_fixture() {
  local step="$1" destination="$2" copied_root
  snapshot_before "$ROOT" "$step"
  mkdir "$destination"
  note "running step=$step: supervised source copy to $destination"
  supervise "$step" cp -R -- "$ROOT/ci" "$ROOT/crates" "$ROOT/tools" \
    "$ROOT/Cargo.toml" "$ROOT/Cargo.lock" "$ROOT/SUITE.lock" \
    "$ROOT/rust-toolchain.toml" "$destination/"
  inspect_supervisor "$step"
  propagate_supervisor_taxonomy "$step" none
  snapshot_after "$ROOT" "$step"
  if ! copied_root="$(hash_subject "$destination")"; then
    set_final internal_fault "$step:copied_fixture_hash_unavailable" 2
    exit 2
  fi
  if [ "$LAST_RC" -ne 0 ]; then
    record_contract_failure "$step" source_copy_failed pass 0 0 \
      "$SUBJECT_BEFORE" "$SUBJECT_AFTER" "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
  fi
  if [ "$SUBJECT_BEFORE" != "$SUBJECT_AFTER" ] || \
     [ "$GLOBAL_BEFORE" != "$GLOBAL_AFTER" ] || \
     [ "$copied_root" != "$SUBJECT_BEFORE" ]; then
    record_contract_failure "$step" source_copy_hash_mismatch pass 0 0 \
      "$SUBJECT_BEFORE" "$SUBJECT_AFTER" "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
  fi
  record_step "$step" pass "source_copy=$SUBJECT_BEFORE" \
    "fixture_copy=$copied_root" not_applicable pass 0 0 \
    "$SUBJECT_BEFORE" "$SUBJECT_AFTER" "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
}

resource_exhaustion_step() {
  local step="$1" subject="$2"
  snapshot_before "$subject" "$step"
  note "running step=$step: force a typed output-budget exhaustion"
  launch_supervisor "$step" 256 256 "$TIMEOUT_MS" \
    "$FROZEN_GUARD" --root "$subject" --robot
  await_supervisor
  inspect_supervisor "$step"
  propagate_supervisor_taxonomy "$step" 3
  snapshot_after "$subject" "$step"
  if [ "$LAST_RC" -ne 3 ]; then
    record_contract_failure "$step" expected_output_budget_inconclusive \
      inconclusive 3 0 "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
      "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
  fi
  if [ "$LAST_REASON" != output_budget_exhausted ]; then
    set_final inconclusive "$step:unexpected_$LAST_REASON" 3
    exit 3
  fi
  if [ "$LAST_CHILD_EXIT" != 0 ]; then
    set_final inconclusive "$step:unexpected_child_$LAST_CHILD_EXIT" 3
    exit 3
  fi
  if [ "$SUBJECT_BEFORE" != "$SUBJECT_AFTER" ] || \
     [ "$GLOBAL_BEFORE" != "$GLOBAL_AFTER" ]; then
    set_final internal_fault "$step:governed_inputs_changed" 2
    exit 2
  fi
  record_step "$step" pass inconclusive/output_budget_exhausted/wrapper=3/child=0 \
    "$LAST_CLASSIFICATION/$LAST_REASON/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
    not_applicable inconclusive 3 0 "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
    "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
}

cancel_arm_ready() {
  local runner_pid="$1" pid_path="$2"
  local ticks=$(( (READY_WAIT_MS + 19) / 20 )) index
  for ((index = 0; index < ticks; index += 1)); do
    if [ -s "$LAST_READY" ] && [ -s "$pid_path" ]; then return 0; fi
    if ! kill -0 "$runner_pid" 2>/dev/null; then return 1; fi
    sleep 0.02
  done
  return 1
}

cancelled_pids_are_dead() {
  python3 - "$1" <<'PY'
import os
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
values = path.read_text(encoding="ascii").splitlines()
if len(values) != 2 or any(not value.isdecimal() for value in values):
    raise SystemExit("malformed cancellation PID evidence")
for raw in values:
    pid = int(raw)
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        continue
    stat = pathlib.Path(f"/proc/{pid}/stat")
    if stat.exists() and stat.read_text(encoding="ascii").split()[2] == "Z":
        continue
    raise SystemExit(f"live cancelled process: {pid}")
PY
}

cancellation_step() {
  local step="$1" subject="$2" pid_path="$3" parent_program="$4"
  local runner_pid term_sent kill_sent
  snapshot_before "$subject" "$step"
  note "running step=$step: readiness-triggered process-tree cancellation"
  launch_supervisor "$step" 4096 65536 "$TIMEOUT_MS" \
    python3 -c "$parent_program" "$pid_path"
  runner_pid="$ACTIVE_RUNNER_PID"
  if ! cancel_arm_ready "$runner_pid" "$pid_path"; then
    kill -TERM "$runner_pid" 2>/dev/null || true
    await_supervisor
    set_final internal_fault "$step:cancellation_fixture_not_ready" 2
    exit 2
  fi
  kill -TERM "$runner_pid"
  await_supervisor
  inspect_supervisor "$step"
  propagate_supervisor_taxonomy "$step" 4
  snapshot_after "$subject" "$step"
  if [ "$LAST_RC" -ne 4 ]; then
    record_contract_failure "$step" expected_typed_cancellation \
      cancelled 4 null "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
      "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
  fi
  if [ "$LAST_REASON" != signal_SIGTERM ] || [ "$LAST_CHILD_EXIT" != null ]; then
    set_final cancelled "$step:unexpected_${LAST_REASON}_child_${LAST_CHILD_EXIT}" 4
    exit 4
  fi
  term_sent="$(read_meta_resource_field "$LAST_META" term_sent)"
  kill_sent="$(read_meta_resource_field "$LAST_META" kill_sent)"
  if [ "$term_sent" != true ] || [ "$kill_sent" != true ]; then
    set_final internal_fault "$step:term_ignoring_setsid_descendant_not_proven" 2
    exit 2
  fi
  if ! cancelled_pids_are_dead "$pid_path"; then
    set_final internal_fault "$step:process_tree_survived" 2
    exit 2
  fi
  if [ "$SUBJECT_BEFORE" != "$SUBJECT_AFTER" ] || \
     [ "$GLOBAL_BEFORE" != "$GLOBAL_AFTER" ]; then
    set_final internal_fault "$step:governed_inputs_changed" 2
    exit 2
  fi
  record_step "$step" pass cancelled/process_tree_contained/wrapper=4/child=null \
    "$LAST_CLASSIFICATION/$LAST_REASON/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
    not_applicable cancelled 4 null "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
    "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
}

run_pass_step build_guard "$ROOT" \
  --semantic-failure-exit 101 \
  env CARGO_TARGET_DIR="$BUILD_TARGET" cargo build --locked -p structure-guard --quiet
BUILT_GUARD="$BUILD_TARGET/debug/structure-guard"
run_pass_step verify_built_guard "$ROOT" test -x "$BUILT_GUARD"
mkdir "$ART_DIR/bin"
run_pass_step freeze_guard "$ROOT" cp -- "$BUILT_GUARD" "$FROZEN_GUARD"
run_pass_step verify_frozen_guard "$ROOT" test -x "$FROZEN_GUARD"

guard_step real_workspace "$ROOT" 0 pass

SCRATCH_ROOT="$ART_DIR/fixtures"
mkdir "$SCRATCH_ROOT"

SETUP_ERROR_ROOT="$SCRATCH_ROOT/setup-error"
mkdir "$SETUP_ERROR_ROOT"
guard_step robot_setup_failure "$SETUP_ERROR_ROOT" 2 setup_error

UNACKNOWLEDGED="$SCRATCH_ROOT/unacknowledged"
copy_fixture copy_unacknowledged "$UNACKNOWLEDGED"
printf 'fln-kernel = { path = "../fln-kernel" }\n' >> "$UNACKNOWLEDGED/crates/fln-core/Cargo.toml"
guard_step seeded_unacknowledged "$UNACKNOWLEDGED" 1 fail \
  FLN-STRUCT-005@crates/fln-core/Cargo.toml \
  FLN-STRUCT-007@crates/fln-core/Cargo.toml

ACKNOWLEDGED="$SCRATCH_ROOT/acknowledged"
copy_fixture copy_acknowledged "$ACKNOWLEDGED"
printf 'fln-kernel = { path = "../fln-kernel" }\n' >> "$ACKNOWLEDGED/crates/fln-core/Cargo.toml"
printf 'edge fln-core -> fln-kernel\n' >> "$ACKNOWLEDGED/ci/WORKSPACE_GRAPH.txt"
guard_step seeded_acknowledged "$ACKNOWLEDGED" 1 fail \
  FLN-STRUCT-007@crates/fln-core/Cargo.toml

RECOVERED="$SCRATCH_ROOT/recovered"
copy_fixture copy_dependency_recovery "$RECOVERED"
guard_step dependency_recovery "$RECOVERED" 0 pass

UNLEDGERED="$SCRATCH_ROOT/unledgered"
copy_fixture copy_unledgered "$UNLEDGERED"
printf '\n#[allow(unsafe_code)]\nfn seeded_unledgered_site() {}\n' \
  >> "$UNLEDGERED/crates/fln-unsafe-abi/src/lib.rs"
guard_step seeded_unledgered "$UNLEDGERED" 1 fail \
  FLN-STRUCT-013@crates/fln-unsafe-abi/src/lib.rs

LEDGERED="$SCRATCH_ROOT/ledgered"
copy_fixture copy_ledgered_recovery "$LEDGERED"
printf '\n// UNSAFE-LEDGER: FLN-UL-9001\n#[allow(unsafe_code)]\nfn seeded_ledgered_site() {}\n' \
  >> "$LEDGERED/crates/fln-unsafe-abi/src/lib.rs"
printf 'row FLN-UL-9001 | crates/fln-unsafe-abi/src/lib.rs | e2e fixture invariant | this scenario | safe fallback path | result never enters a checked declaration\n' \
  >> "$LEDGERED/ci/UNSAFE_LEDGER.txt"
guard_step ledger_recovery "$LEDGERED" 0 pass

EXPORTED="$SCRATCH_ROOT/exported"
copy_fixture copy_exported "$EXPORTED"
printf '\npub fn seeded_public_export<T>() -> T { panic!("not executed") }\n' \
  >> "$EXPORTED/crates/fln-unsafe-abi/src/lib.rs"
guard_step seeded_export "$EXPORTED" 1 fail \
  FLN-STRUCT-022@crates/fln-unsafe-abi/src/lib.rs

RESTRICTED="$SCRATCH_ROOT/restricted"
copy_fixture copy_export_recovery "$RESTRICTED"
printf '\npub(crate) fn seeded_crate_local_api() {}\n' \
  >> "$RESTRICTED/crates/fln-unsafe-abi/src/lib.rs"
guard_step export_recovery "$RESTRICTED" 0 pass

# A real guard invocation that exceeds a deliberately tiny output budget is typed
# inconclusive. The same frozen binary immediately recovers under the normal budget.
resource_exhaustion_step resource_exhaustion "$ROOT"
guard_step resource_recovery "$ROOT" 0 pass

# Cancellation waits for both supervisor readiness and a fixture handshake. The
# grandchild installs SIGTERM immunity before publishing its PID and starts a new
# session, so a successful result proves descendant discovery beyond one process group.
CANCEL_PIDS="$ART_DIR/cancel-pids.txt"
CANCEL_PROGRAM='import subprocess,sys,time; child="import os,pathlib,signal,sys,time;signal.signal(signal.SIGTERM,signal.SIG_IGN);pathlib.Path(sys.argv[1]).write_text(str(os.getppid())+chr(10)+str(os.getpid())+chr(10),encoding=\"ascii\");time.sleep(60)";subprocess.Popen([sys.executable,"-c",child,sys.argv[1]],start_new_session=True);time.sleep(60)'
cancellation_step cancellation "$ROOT" "$CANCEL_PIDS" "$CANCEL_PROGRAM"
guard_step cancellation_recovery "$ROOT" 0 pass

guard_step final_real_recheck "$ROOT" 0 pass

ACTIVE_STEP=complete
set_final pass all_scenarios_satisfied 0
exit 0
