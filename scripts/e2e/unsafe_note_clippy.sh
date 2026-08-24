#!/usr/bin/env bash
# Bidirectional D3 unsafe-note debt gate. Clippy remains the sole classifier:
# this lane canonicalizes its reported site set and compares it with the
# checked-in declaration in both directions, then proves both mismatch
# directions with planted artifacts and clean recovery.

set -Eeuo pipefail

PYTHON_BIN="$(command -v python3 || true)"
[ -n "$PYTHON_BIN" ] || {
  echo "[unsafe_note_clippy] setup failure: python3 is required" >&2
  exit 2
}
PYTHON=("$PYTHON_BIN" -I -S)
HOSTILE_PYTHON_CONFIGURATION=()
while IFS= read -r environment_name; do
  [[ "$environment_name" == PYTHON* ]] \
    && HOSTILE_PYTHON_CONFIGURATION+=("$environment_name")
done < <(compgen -e | LC_ALL=C sort)
if ((${#HOSTILE_PYTHON_CONFIGURATION[@]} > 0)); then
  printf '[unsafe_note_clippy] setup failure: sealed_interpreter_hostile_environment names=%s\n' \
    "$(IFS=,; printf '%s' "${HOSTILE_PYTHON_CONFIGURATION[*]}")" >&2
  exit 2
fi
for tool in cargo sha256sum; do
  command -v "$tool" >/dev/null 2>&1 || {
    printf '[unsafe_note_clippy] setup failure: %s is required\n' "$tool" >&2
    exit 2
  }
done

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
cd "$ROOT"
EVIDENCE="$ROOT/scripts/evidence.py"
DECLARED="$ROOT/ci/UNSAFE_NOTE_CLIPPY_SITES.txt"
SCHEMA="fln.e2e/2"
BEAD="franken_lean-d3-safety-note-clippy-diff-lane-5dkw"
SCENARIO="unsafe_note_clippy"
# The build gate, taken by this lane rather than by whoever launched it — bead
# franken_lean-gate-lock-producer-optional-o2vz. Same shape as closure_audit.sh:
# sits before the EXIT finalizer is installed, so a contention `exit 3` writes no
# evidence. Not in INPUT_PATHS (a governed-set row build_gate_governed_sets.rs pins
# would move); SC1091 disabled because check.sh's shellcheck stage checks the
# library directly.
# shellcheck source=scripts/lib/gate_lock.sh
# shellcheck disable=SC1091
. "$ROOT/scripts/lib/gate_lock.sh"
fln_gate_acquire "$SCENARIO"
RUN_ID="unsafe-note-clippy-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_ROOT="${FLN_E2E_ART_ROOT:-$ROOT/target/e2e}"
ART_DIR="$ART_ROOT/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
HUMAN="$ART_DIR/human.log"
RAW_REPORT="$ART_DIR/clippy-report.jsonl"
OBSERVED="$ART_DIR/observed-sites.txt"
UNDECLARED_OBSERVED="$ART_DIR/undeclared-observed-sites.txt"
STALE_DECLARED="$ART_DIR/stale-declared-sites.txt"
VENDOR_PATH="vendor/lean4-src"
VENDOR_BINDING="$ART_DIR/vendor-binding.json"
BUILD_TARGET="${CARGO_TARGET_DIR:-$ROOT/target/cargo}/e2e-unsafe-note-clippy"
CAPTURE_BYTES="${FLN_E2E_CAPTURE_BYTES:-262144}"
OUTPUT_BUDGET_BYTES="${FLN_E2E_OUTPUT_BUDGET_BYTES:-16777216}"
TIMEOUT_MS="${FLN_E2E_TIMEOUT_MS:-600000}"
GRACE_MS="${FLN_E2E_KILL_GRACE_MS:-2000}"
START_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
SEQ=0
ACTIVE_STEP=setup
FINAL_SET=0
FINAL_VERDICT=internal_fault
FINAL_REASON=uncommitted_exit
FINAL_EXIT=2
TERMINAL_EMITTED=0

INPUT_PATHS=(
  Cargo.toml Cargo.lock SUITE.lock rust-toolchain.toml
  ci/UNSAFE_NOTE_CLIPPY_SITES.txt ci/VERIFICATION_MANIFEST.jsonl
  crates/fln-unsafe-abi crates/fln-unsafe-region crates/fln-unsafe-jit
  scripts/e2e/unsafe_note_clippy.sh scripts/evidence.py scripts/check.sh
  .github/workflows/ci.yml
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
  echo "[unsafe_note_clippy] setup failure: cannot hash governed inputs" >&2
  exit 2
fi
DECLARED_ROOT="sha256:$(sha256sum "$DECLARED" | cut -d' ' -f1)"

note() {
  printf '[unsafe_note_clippy] %s\n' "$*" | tee -a "$HUMAN" >&2
}

emit_event() {
  local sequence="$SEQ"
  SEQ=$((SEQ + 1))
  "${PYTHON[@]}" "$EVIDENCE" emit --file "$LOG" --artifact-root "$ART_DIR" \
    --string schema "$SCHEMA" --string run_id "$RUN_ID" --string bead "$BEAD" \
    --string scenario "$SCENARIO" --integer sequence "$sequence" \
    --integer monotonic_ns "$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')" \
    --string wall_time_utc "$(date -u -Is)" "$@"
}

set_final() {
  FINAL_SET=1
  FINAL_VERDICT="$1"
  FINAL_REASON="$2"
  FINAL_EXIT="$3"
}

hash_governed() {
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path "$VENDOR_PATH"
}

read_meta() {
  "${PYTHON[@]}" - "$1" "$2" <<'PY'
import json
import pathlib
import sys

value = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))[sys.argv[2]]
print("null" if value is None else value)
PY
}

finalize() {
  local observed_rc="$1" final_root validation_rc=0 bundle_rc=0
  trap - EXIT HUP INT TERM
  # Journal the release first; `|| true` because `set -e` is in force.
  fln_gate_release_note "$SCENARIO" || true
  set +e
  if [ "$FINAL_SET" -eq 0 ]; then
    if [ "$observed_rc" -eq 0 ]; then
      set_final internal_fault uncommitted_success 2
    else
      set_final internal_fault unexpected_shell_exit 2
    fi
  fi
  final_root="$(hash_governed)" || {
    final_root=unavailable
    set_final internal_fault final_workspace_hash_unavailable 2
  }
  if [ "$FINAL_VERDICT" = pass ] && [ "$final_root" != "$INPUT_ROOT" ]; then
    set_final inconclusive governed_inputs_changed 3
  fi
  local first_divergence=none
  [ "$FINAL_VERDICT" = pass ] || first_divergence="$FINAL_REASON"
  if [ "$TERMINAL_EMITTED" -eq 0 ]; then
    emit_event --string event run_end --string verdict "$FINAL_VERDICT" \
      --string reason_code "$FINAL_REASON" --integer process_exit "$FINAL_EXIT" \
      --string active_step "$ACTIVE_STEP" \
      --integer duration_ns "$(( $("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())') - START_NS ))" \
      --string cleanup_status retained_by_policy --string final_state "$final_root" \
      --string logical_root "$final_root" --string receipt_root "$DECLARED_ROOT" \
      --string first_divergence "$first_divergence" \
      --string evidence_manifest manifest.json \
      --string bundle_commit bundle.complete.json \
      --string evidence_state pending_bundle_commit || validation_rc=2
    TERMINAL_EMITTED=1
  fi
  if [ "$validation_rc" -eq 0 ]; then
    "${PYTHON[@]}" "$EVIDENCE" validate-run --file "$LOG" --schema "$SCHEMA" \
      --expected-verdict "$FINAL_VERDICT" --artifact-root "$ART_DIR" \
      --output "$ART_DIR/run.validation.json" || validation_rc=2
  fi
  if [ "$validation_rc" -eq 0 ]; then
    "${PYTHON[@]}" "$EVIDENCE" manifest --art-dir "$ART_DIR" \
      --output "$ART_DIR/manifest.json" --digest-output "$ART_DIR/manifest.digest" \
      --run-id "$RUN_ID" --bead "$BEAD" --scenario "$SCENARIO" \
      --verdict "$FINAL_VERDICT" --input-root "$INPUT_ROOT" --final-root "$final_root" \
      || validation_rc=2
  fi
  if [ "$validation_rc" -eq 0 ]; then
    "${PYTHON[@]}" "$EVIDENCE" complete-bundle --art-dir "$ART_DIR" \
      --manifest "$ART_DIR/manifest.json" --digest "$ART_DIR/manifest.digest" \
      --output "$ART_DIR/bundle.complete.json" --governed-root "$ROOT" \
      "${GOVERNED_ARGS[@]}" --vendor-path "$VENDOR_PATH" \
      --expected-root "$final_root" || bundle_rc=$?
    "${PYTHON[@]}" "$EVIDENCE" adopt-bundle --art-dir "$ART_DIR" \
      --manifest "$ART_DIR/manifest.json" --digest "$ART_DIR/manifest.digest" \
      --commit "$ART_DIR/bundle.complete.json" --artifact-root "$ART_DIR" \
      >/dev/null || bundle_rc=2
  fi
  if [ "$validation_rc" -ne 0 ] || [ "$bundle_rc" -ne 0 ]; then
    printf '[unsafe_note_clippy] INTERNAL FAULT: evidence bundle incomplete: %s\n' \
      "$ART_DIR" >&2
    exit 2
  fi
  printf '[unsafe_note_clippy] %s reason=%s evidence=%s\n' \
    "$FINAL_VERDICT" "$FINAL_REASON" "$ART_DIR" >&2
  if ! "${PYTHON[@]}" "$EVIDENCE" validate-bundle --art-dir "$ART_DIR" \
      --manifest "$ART_DIR/manifest.json" --digest "$ART_DIR/manifest.digest" \
      --commit "$ART_DIR/bundle.complete.json" --artifact-root "$ART_DIR" \
      >/dev/null; then
    printf '[unsafe_note_clippy] INTERNAL FAULT: terminal bundle mutated: %s\n' \
      "$ART_DIR" >&2
    exit 2
  fi
  exit "$FINAL_EXIT"
}

on_signal() {
  local name="$1" code="$2"
  set_final cancelled "signal_$name" "$code"
  exit "$code"
}

trap 'on_signal HUP 129' HUP
trap 'on_signal INT 130' INT
trap 'on_signal TERM 143' TERM
trap 'finalize "$?"' EXIT

mkdir -p "$(dirname "$ART_DIR")"
if ! mkdir "$ART_DIR" 2>/dev/null; then
  trap - EXIT
  echo "[unsafe_note_clippy] evidence directory already claimed: $ART_DIR" >&2
  exit 2
fi
: > "$HUMAN"
"${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ROOT" --vendor-path "$VENDOR_PATH" \
  --output "$VENDOR_BINDING" --artifact-root "$ART_DIR"

emit_event --new-log --string event run_start \
  --json-value argv '["scripts/e2e/unsafe_note_clippy.sh"]' \
  --string cwd "$ROOT" \
  --append-string claim_ids FLN-D3-UNSAFE-NOTE-SITE-SET \
  --append-string invariant_ids D3 --append-string gate_ids W1 \
  --string parity_ledger_row not_applicable_static_unsafe_boundary_census \
  --string epoch lean-v4.32.0 --string mode sound --string profile e2e \
  --string platform "$(uname -srm)" --integer thread_count 1 \
  --json-value host_facts "$("${PYTHON[@]}" -c 'import json,platform; print(json.dumps({"system":platform.system(),"release":platform.release(),"machine":platform.machine(),"python":platform.python_version()},sort_keys=True,separators=(",",":")))')" \
  --string seed "$DECLARED_ROOT" \
  --string cache_state "${FLN_E2E_CACHE_STATE:-unspecified}" \
  --string input_root "$INPUT_ROOT" \
  --string vendor_binding vendor-binding.json \
  --producer-binding-root "$ROOT" "${GOVERNED_ARGS[@]}" \
  --json-value budgets "{\"capture_bytes_per_stream\":$CAPTURE_BYTES,\"output_budget_bytes\":$OUTPUT_BUDGET_BYTES,\"step_timeout_ms\":$TIMEOUT_MS,\"kill_grace_ms\":$GRACE_MS}"

run_step() {
  local step="$1" expected_class="$2" expected_wrapper="$3" expected_child="$4"
  local pattern_one="$5" pattern_two="$6"
  shift 6
  ACTIVE_STEP="$step"
  local before after meta out err ready validation wrapper actual_class actual_child
  local assertion=pass
  meta="$ART_DIR/$step.meta.json"
  out="$ART_DIR/$step.out"
  err="$ART_DIR/$step.err"
  ready="$ART_DIR/$step.ready.json"
  validation="$ART_DIR/$step.validation.json"
  before="$(hash_governed)"
  local -a semantic=()
  if [ "$expected_class" = fail ]; then
    semantic=(--semantic-failure-exit "$expected_child")
  fi
  set +e
  "${PYTHON[@]}" "$EVIDENCE" run --cwd "$ROOT" --metadata "$meta" \
    --stdout "$out" --stderr "$err" --readiness "$ready" \
    --artifact-root "$ART_DIR" --capture-bytes "$CAPTURE_BYTES" \
    --output-budget-bytes "$OUTPUT_BUDGET_BYTES" --timeout-ms "$TIMEOUT_MS" \
    --grace-ms "$GRACE_MS" --stage-id "$step" "${semantic[@]}" -- "$@"
  wrapper=$?
  set -e
  "${PYTHON[@]}" "$EVIDENCE" validate-supervisor --file "$meta" \
    --expected-stage-id "$step" --artifact-root "$ART_DIR" --output "$validation"
  after="$(hash_governed)"
  actual_class="$(read_meta "$meta" classification)"
  actual_child="$(read_meta "$meta" child_exit)"
  if [ "$wrapper" -ne "$expected_wrapper" ] \
      || [ "$actual_class" != "$expected_class" ] \
      || [ "$actual_child" != "$expected_child" ] \
      || [ "$before" != "$INPUT_ROOT" ] \
      || [ "$after" != "$INPUT_ROOT" ]; then
    assertion=fail
  fi
  if [ "$pattern_one" != - ] \
      && ! grep -Fq -- "$pattern_one" "$out" "$err"; then
    assertion=fail
  fi
  if [ "$pattern_two" != - ] \
      && ! grep -Fq -- "$pattern_two" "$out" "$err"; then
    assertion=fail
  fi
  emit_event --string event step --string step_id "$step" \
    --string assertion "$assertion" \
    --string expected "$expected_class/exit=$expected_wrapper/child=$expected_child" \
    --string actual "$actual_class/exit=$wrapper/child=$actual_child" \
    --string input_root "$before" --string final_state "$after" \
    --string validation_artifact "$(basename "$validation")" \
    --string expected_supervisor_classification "$expected_class" \
    --integer expected_wrapper_exit "$expected_wrapper" \
    --integer expected_child_exit "$expected_child" \
    --string subject_root "$before" --string subject_final_state "$after" \
    --json-file supervisor "$meta"
  if [ "$assertion" != pass ]; then
    set_final fail "$step:assertion_failed" 1
    exit 1
  fi
}

# shellcheck disable=SC2016
capture_command='
set -euo pipefail
root="$1"
raw="$2"
observed="$3"
artifact_root="$4"
target="$5"
CARGO_TARGET_DIR="$target" cargo clippy --locked \
  -p fln-unsafe-abi -p fln-unsafe-region -p fln-unsafe-jit \
  --all-targets --message-format=json -- \
  --cap-lints warn -W clippy::undocumented_unsafe_blocks > "$raw"
python3 -I -S "$root/scripts/evidence.py" unsafe-note-clippy-sites \
  --operation extract --root "$root" --report "$raw" \
  --output "$observed" --artifact-root "$artifact_root"
'

# shellcheck disable=SC2016
mutant_compare_command='
set -euo pipefail
root="$1"
operation="$2"
source="$3"
mutant="$4"
declared="$5"
observed="$6"
artifact_root="$7"
python3 -I -S "$root/scripts/evidence.py" unsafe-note-clippy-sites \
  --operation "$operation" --declared "$source" \
  --output "$mutant" --artifact-root "$artifact_root"
python3 -I -S "$root/scripts/evidence.py" unsafe-note-clippy-sites \
  --operation compare --declared "$declared" --observed "$observed"
'

note "capturing Clippy's exact undocumented-unsafe site set"
run_step clippy_report pass 0 0 \
  'unsafe-note clippy extract:' 'unique sites' \
  /bin/bash -c "$capture_command" _ \
  "$ROOT" "$RAW_REPORT" "$OBSERVED" "$ART_DIR" "$BUILD_TARGET"

run_step baseline_match pass 0 0 \
  'unsafe-note clippy match:' 'sites' \
  "${PYTHON[@]}" "$EVIDENCE" unsafe-note-clippy-sites \
  --operation compare --declared "$DECLARED" --observed "$OBSERVED"

run_step undeclared_site_mutant fail 1 101 \
  'undeclared clippy site:' 'planted_undeclared_site' \
  /bin/bash -c "$mutant_compare_command" _ \
  "$ROOT" add-observed "$OBSERVED" "$UNDECLARED_OBSERVED" \
  "$DECLARED" "$UNDECLARED_OBSERVED" "$ART_DIR"

run_step undeclared_site_recovery pass 0 0 \
  'unsafe-note clippy match:' 'sites' \
  "${PYTHON[@]}" "$EVIDENCE" unsafe-note-clippy-sites \
  --operation compare --declared "$DECLARED" --observed "$OBSERVED"

run_step stale_declaration_mutant fail 1 101 \
  'stale declared clippy site:' 'planted_stale_site' \
  /bin/bash -c "$mutant_compare_command" _ \
  "$ROOT" add-stale "$DECLARED" "$STALE_DECLARED" \
  "$STALE_DECLARED" "$OBSERVED" "$ART_DIR"

run_step stale_declaration_recovery pass 0 0 \
  'unsafe-note clippy match:' 'sites' \
  "${PYTHON[@]}" "$EVIDENCE" unsafe-note-clippy-sites \
  --operation compare --declared "$DECLARED" --observed "$OBSERVED"

set_final pass all_unsafe_note_clippy_obligations_passed 0
