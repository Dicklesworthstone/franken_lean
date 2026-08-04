#!/usr/bin/env bash
# Real pinned Reference-vs-Reference Tribunal lane (bead fln-euo).
#
# The domain worker below runs the real C1/D1 slice twice, compares it with the
# immutable epoch baseline, detects and surfaces every named divergence level,
# checks the non-authoritative process-outcome boundary in both directions, and
# proves recovery.  The parent routes every worker through the shared bounded
# supervisor and publishes one failure-atomic fln.e2e/2 bundle.

set -Eeuo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"

worker_fault() {
  printf '[ref_vs_ref worker] internal fault: %s\n' "$*" >&2
  exit 2
}

worker_fail() {
  printf '[ref_vs_ref worker] semantic failure: %s\n' "$*" >&2
  exit 101
}

load_reference_pin() {
  local -a rows=()
  local field
  mapfile -t rows < <(grep -E '^reference ' "$ROOT/SUITE.lock")
  [ "${#rows[@]}" -eq 1 ] || worker_fault "SUITE.lock must have one Reference row"
  PIN_TAG=""
  PIN_COMMIT=""
  for field in ${rows[0]}; do
    case "$field" in
      tag=*) PIN_TAG="${field#tag=}" ;;
      commit=*) PIN_COMMIT="${field#commit=}" ;;
    esac
  done
  [[ "$PIN_TAG" =~ ^v[0-9]+\.[0-9]+\.[0-9]+([.-][A-Za-z0-9.-]+)?$ ]] \
    || worker_fault "Reference tag is malformed"
  [[ "$PIN_COMMIT" =~ ^[0-9a-f]{40}$ ]] \
    || worker_fault "Reference commit is malformed"
  LEAN="$HOME/.elan/toolchains/leanprover--lean4---$PIN_TAG/bin/lean"
  EPOCH_DIR="$ROOT/tribunal/epochs/$PIN_TAG"
  CORPUS_ELAB_REL="vendor/lean4-src/tests/elab"
  CORPUS_ELAB_FAIL_REL="vendor/lean4-src/tests/elab_fail"
}

slice_files() {
  awk '$1 ~ /^(c1(-quirk)?|d1)$/ { print $1 " " $2 }' \
    "$EPOCH_DIR/MANIFEST.txt"
}

slice_count() {
  slice_files | awk 'END { print NR + 0 }'
}

corpus_path() {
  case "$1" in
    d1) printf '%s/%s' "$CORPUS_ELAB_FAIL_REL" "$2" ;;
    *) printf '%s/%s' "$CORPUS_ELAB_REL" "$2" ;;
  esac
}

oracle_env() {
  env -u LEAN_PATH -u LEAN_SYSROOT LC_ALL=C TZ=UTC "$@"
}

require_artifact_child() {
  case "$1" in
    "$WORKER_ART_DIR"/*) ;;
    *) worker_fault "artifact path escapes the run root: $1" ;;
  esac
}

run_slice() {
  local destination="$1" family file rc count=0
  require_artifact_child "$destination"
  [ ! -e "$destination" ] || worker_fault "slice destination already exists"
  mkdir "$destination"
  while read -r family file; do
    if [ -z "$family" ] || [ -z "$file" ]; then
      worker_fault "epoch manifest contains a malformed slice row"
    fi
    case "$file" in
      */*|*..*) worker_fault "unsafe slice filename: $file" ;;
    esac
    set +e
    (
      cd "$ROOT"
      oracle_env "$LEAN" "$(corpus_path "$family" "$file")"
    ) > "$destination/$file.stdout" 2> "$destination/$file.stderr"
    rc=$?
    set -e
    printf 'exit %s\n' "$rc" > "$destination/$file.exit"
    count=$((count + 1))
  done < <(slice_files)
  [ "$count" -gt 0 ] || worker_fault "epoch slice is empty"
  printf 'slice=%s files=%s\n' "$(basename "$destination")" "$count"
}

record_plant_digest() {
  local name="$1"
  require_artifact_child "$WORKER_ART_DIR/$name"
  sha256sum "$WORKER_ART_DIR/$name" \
    | awk -v artifact="$name" '{ print $1 "  " artifact }' \
    >> "$WORKER_ART_DIR/plant-digests.txt"
}

find_plant_target() {
  local family file
  PLANT_STDOUT=""
  PLANT_FAMILY=""
  while read -r family file; do
    if [ -s "$WORKER_ART_DIR/run-a/$file.stdout" ]; then
      PLANT_STDOUT="$file"
      PLANT_FAMILY="$family"
      return 0
    fi
  done < <(slice_files)
  worker_fault "the slice has no nonempty stdout plant target"
}

detect_plant() {
  local level="$1" marker="$2" diff_rc
  local plant_dir="$WORKER_ART_DIR/plant-$level"
  local diff_path="$WORKER_ART_DIR/plant-$level.diff"
  require_artifact_child "$plant_dir"
  [ ! -e "$plant_dir" ] || worker_fault "plant directory already exists: $level"
  cp -R "$WORKER_ART_DIR/run-a" "$plant_dir"
  PLANT_DIR="$plant_dir"
  case "$level" in
    line)
      printf 'PLANT-LINE: a whole replaced line\n' \
        > "$PLANT_DIR/$PLANT_STDOUT.stdout"
      ;;
    subline)
      local first_byte
      first_byte="$(head -c 1 "$PLANT_DIR/$PLANT_STDOUT.stdout")"
      {
        printf 'PLANT-SUBLINE-%s' "$first_byte"
        tail -c +2 "$PLANT_DIR/$PLANT_STDOUT.stdout"
      } > "$PLANT_DIR/subline.tmp"
      mv "$PLANT_DIR/subline.tmp" "$PLANT_DIR/$PLANT_STDOUT.stdout"
      ;;
    diagnostic)
      printf 'PLANT-DIAGNOSTIC: error: fabricated diagnostic\n' \
        >> "$PLANT_DIR/$PLANT_STDOUT.stderr"
      ;;
    exit)
      printf 'exit 117 PLANT-EXIT\n' > "$PLANT_DIR/$PLANT_STDOUT.exit"
      ;;
    *) worker_fault "unknown plant level: $level" ;;
  esac
  set +e
  diff -ur "$WORKER_ART_DIR/run-b" "$PLANT_DIR" > "$diff_path" 2>&1
  diff_rc=$?
  set -e
  case "$diff_rc" in
    0) worker_fail "planted $level divergence was not detected" ;;
    1) ;;
    *) worker_fault "diff failed while checking $level divergence" ;;
  esac
  grep -Fq "$marker" "$diff_path" \
    || worker_fail "$level divergence did not surface its planted body"
  record_plant_digest "plant-$level.diff"
  printf 'plant=%s detected marker=%s\n' "$level" "$marker"
}

classify_oracle_rc() {
  case "$1" in
    124|125|137|139) printf 'non-authoritative' ;;
    *) printf 'authoritative' ;;
  esac
}

run_worker() {
  local step="$1" count diff_rc killed_rc first_file seeded
  load_reference_pin
  WORKER_ART_DIR="${FLN_REF_ART_DIR:-}"
  [ -n "$WORKER_ART_DIR" ] || worker_fault "FLN_REF_ART_DIR is absent"
  WORKER_ART_DIR="$(cd "$WORKER_ART_DIR" && pwd -P)" \
    || worker_fault "artifact root is not a directory"
  cd "$ROOT"

  case "$step" in
    oracle_binding)
      [ -x "$LEAN" ] || worker_fault "pinned Reference binary is absent"
      [ -f "$EPOCH_DIR/MANIFEST.txt" ] || worker_fault "epoch lab is absent"
      "$LEAN" --version | grep -Fq "$PIN_COMMIT" \
        || worker_fault "Reference binary does not match SUITE.lock"
      count="$(slice_count)"
      [ "$count" -gt 0 ] || worker_fault "epoch slice is empty"
      printf 'oracle_binding tag=%s commit=%s files=%s\n' \
        "$PIN_TAG" "$PIN_COMMIT" "$count"
      ;;
    reference_run_a)
      run_slice "$WORKER_ART_DIR/run-a"
      ;;
    reference_run_b)
      run_slice "$WORKER_ART_DIR/run-b"
      ;;
    determinism)
      set +e
      diff -ur "$WORKER_ART_DIR/run-a" "$WORKER_ART_DIR/run-b" \
        > "$WORKER_ART_DIR/ref-vs-ref.diff" 2>&1
      diff_rc=$?
      set -e
      case "$diff_rc" in
        0) printf 'reference semantic trees are byte-identical\n' ;;
        1) worker_fail "Reference diverged from itself" ;;
        *) worker_fault "determinism diff failed" ;;
      esac
      ;;
    baseline)
      set +e
      diff -ur "$EPOCH_DIR/transcripts" "$WORKER_ART_DIR/run-a" \
        > "$WORKER_ART_DIR/baseline.diff" 2>&1
      diff_rc=$?
      set -e
      case "$diff_rc" in
        0) printf 'published epoch baseline matched\n' ;;
        1) worker_fail "live Reference behavior differs from the epoch baseline" ;;
        *) worker_fault "baseline diff failed" ;;
      esac
      ;;
    seeded_divergence_artifact)
      first_file="$(slice_files | awk 'NR == 1 { print $2 }')"
      [ -n "$first_file" ] || worker_fault "no artifact-level plant target"
      seeded="$WORKER_ART_DIR/seeded"
      cp -R "$WORKER_ART_DIR/run-a" "$seeded"
      printf 'PLANTED-DIVERGENCE: this body must remain visible\n' \
        >> "$seeded/$first_file.stdout"
      set +e
      diff -ur "$WORKER_ART_DIR/run-b" "$seeded" \
        > "$WORKER_ART_DIR/seeded.diff" 2>&1
      diff_rc=$?
      set -e
      case "$diff_rc" in
        0) worker_fail "artifact divergence was not detected" ;;
        1) ;;
        *) worker_fault "artifact divergence diff failed" ;;
      esac
      grep -Fq 'PLANTED-DIVERGENCE' "$WORKER_ART_DIR/seeded.diff" \
        || worker_fail "artifact divergence body was normalized away"
      : > "$WORKER_ART_DIR/plant-digests.txt"
      record_plant_digest seeded.diff
      printf 'plant=artifact detected marker=PLANTED-DIVERGENCE\n'
      ;;
    seeded_divergence_line)
      find_plant_target
      detect_plant line PLANT-LINE
      ;;
    seeded_divergence_subline)
      find_plant_target
      detect_plant subline PLANT-SUBLINE
      ;;
    seeded_divergence_diagnostic)
      find_plant_target
      detect_plant diagnostic PLANT-DIAGNOSTIC
      ;;
    seeded_divergence_exit)
      find_plant_target
      detect_plant exit PLANT-EXIT
      ;;
    non_authoritative_outcome)
      find_plant_target
      set +e
      (
        cd "$ROOT"
        oracle_env timeout -s KILL 0.01 \
          "$LEAN" "$(corpus_path "$PLANT_FAMILY" "$PLANT_STDOUT")"
      ) > /dev/null 2>&1
      killed_rc=$?
      set -e
      [ "$(classify_oracle_rc "$killed_rc")" = non-authoritative ] \
        || worker_fail "killed oracle rc=$killed_rc classified authoritative"
      [ "$(classify_oracle_rc 1)" = authoritative ] \
        || worker_fail "genuine rc=1 classified non-authoritative"
      printf 'killed_rc=%s classification=non-authoritative control_rc=1 authoritative\n' \
        "$killed_rc"
      ;;
    recovery)
      diff -ur "$WORKER_ART_DIR/run-a" "$WORKER_ART_DIR/run-b" \
        > /dev/null 2>&1 \
        || worker_fail "pristine semantic trees do not recover"
      printf 'recovery restored the pristine byte-identical trees\n'
      ;;
    *) worker_fault "unknown worker step: $step" ;;
  esac
}

if [ "${1:-}" = "--worker" ]; then
  [ "$#" -eq 2 ] || worker_fault "usage: ref_vs_ref.sh --worker <step>"
  run_worker "$2"
  exit 0
fi

PYTHON_BIN="$(command -v python3 || true)"
[ -n "$PYTHON_BIN" ] || {
  echo "[ref_vs_ref] setup failure: python3 is required" >&2
  exit 2
}
PYTHON=("$PYTHON_BIN" -I -S)
HOSTILE_PYTHON_CONFIGURATION=()
while IFS= read -r environment_name; do
  [[ "$environment_name" == PYTHON* ]] \
    && HOSTILE_PYTHON_CONFIGURATION+=("$environment_name")
done < <(compgen -e | LC_ALL=C sort)
if ((${#HOSTILE_PYTHON_CONFIGURATION[@]} > 0)); then
  printf '[ref_vs_ref] setup failure: sealed_interpreter_hostile_environment names=%s\n' \
    "$(IFS=,; printf '%s' "${HOSTILE_PYTHON_CONFIGURATION[*]}")" >&2
  exit 2
fi
for required_command in setsid sha256sum diff timeout awk grep env; do
  command -v "$required_command" >/dev/null 2>&1 || {
    printf '[ref_vs_ref] setup failure: %s is required\n' "$required_command" >&2
    exit 2
  }
done

cd "$ROOT"
load_reference_pin
EVIDENCE="$ROOT/scripts/evidence.py"
DOMAIN_VALIDATOR="$ROOT/scripts/tribunal/validate_ref_vs_ref_bundle.py"
SCHEMA="fln.e2e/2"
BEAD="fln-euo"
SCENARIO="reference_reference_no_mock_e2e"
RUN_ID="ref-vs-ref-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_ROOT="${FLN_E2E_ART_ROOT:-$ROOT/target/e2e}"
ART_DIR="$ART_ROOT/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
HUMAN="$ART_DIR/human.log"
VENDOR_PATH="vendor/lean4-src"
VENDOR_BINDING="$ART_DIR/vendor-binding.json"
PRETERMINAL_VALIDATION="$ART_DIR/reference.preterminal.validation.json"
FINAL_VALIDATION="$ART_DIR/reference.final.validation.json"
CAPTURE_BYTES="${FLN_E2E_CAPTURE_BYTES:-262144}"
OUTPUT_BUDGET_BYTES="${FLN_E2E_OUTPUT_BUDGET_BYTES:-16777216}"
TIMEOUT_MS="${FLN_E2E_TIMEOUT_MS:-600000}"
GRACE_MS="${FLN_E2E_KILL_GRACE_MS:-2000}"
READY_WAIT_MS="${FLN_E2E_READY_WAIT_MS:-30000}"
case "$READY_WAIT_MS" in
  ''|*[!0-9]*)
    echo "[ref_vs_ref] setup failure: FLN_E2E_READY_WAIT_MS must be numeric" >&2
    exit 2
    ;;
esac
if [ "$READY_WAIT_MS" -gt 30000 ]; then
  READY_WAIT_MS=30000
fi
START_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
SEQ=0
RUN_STARTED=0
ART_DIR_CLAIMED=0
FINAL_SET=0
FINAL_VERDICT=internal_fault
FINAL_REASON=uncommitted_exit
FINAL_EXIT=2
FINALIZING=0
GATE_RELEASE_NOTED=0
ACTIVE_STEP=preflight
ACTIVE_RUNNER_PID=""
ACTIVE_RUNNER_START_TICKS=""
ACTIVE_READINESS=""
EVENT_COMMAND=()

INPUT_PATHS=(
  SUITE.lock
  rust-toolchain.toml
  ci/VERIFICATION_MANIFEST.jsonl
  scripts/evidence.py
  scripts/lib/gate_lock.sh
  scripts/tribunal/ref_vs_ref.sh
  scripts/tribunal/validate_ref_vs_ref_bundle.py
  scripts/tribunal/gen_epoch_manifest.sh
  tribunal/epoch-lab
  "tribunal/epochs/$PIN_TAG"
  .github/workflows/contract-drift.yml
  vendor/NOTICE
)
SUBJECT_PATHS=(
  SUITE.lock
  scripts/tribunal/ref_vs_ref.sh
  scripts/tribunal/validate_ref_vs_ref_bundle.py
  tribunal/epoch-lab
  "tribunal/epochs/$PIN_TAG"
)
HASH_ARGS=()
GOVERNED_ARGS=()
SUBJECT_HASH_ARGS=()
for input_path in "${INPUT_PATHS[@]}"; do
  HASH_ARGS+=(--path "$input_path")
  GOVERNED_ARGS+=(--governed-path "$input_path")
done
for subject_path in "${SUBJECT_PATHS[@]}"; do
  SUBJECT_HASH_ARGS+=(--path "$subject_path")
done

# shellcheck source=scripts/lib/gate_lock.sh
# shellcheck disable=SC1091
. "$ROOT/scripts/lib/gate_lock.sh"
trap 'fln_gate_release_note "$SCENARIO"' EXIT
fln_gate_acquire "$SCENARIO"

if ! INPUT_ROOT="$(
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path "$VENDOR_PATH"
)"; then
  echo "[ref_vs_ref] setup failure: cannot hash governed inputs" >&2
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
  printf '[ref_vs_ref] %s\n' "$*" | tee -a "$HUMAN" >&2
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

gate_release_note_once() {
  if [ "$GATE_RELEASE_NOTED" -eq 0 ]; then
    fln_gate_release_note "$SCENARIO"
    GATE_RELEASE_NOTED=1
  fi
}

read_json_field() {
  "${PYTHON[@]}" - "$1" "$2" <<'PY'
import json
import pathlib
import sys

value = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))[sys.argv[2]]
print("null" if value is None else value)
PY
}

hash_governed() {
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path "$VENDOR_PATH"
}

hash_subject() {
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${SUBJECT_HASH_ARGS[@]}"
}

terminate_unreleased_runner() {
  local pid="$1"
  setsid -- "${PYTHON[@]}" "$EVIDENCE" kill-direct-child --pid "$pid" \
    --expected-parent-pid "$$" --wait-ms 5000 || return 1
  wait "$pid" 2>/dev/null || true
}

bounded_readiness_wait() {
  local pid="$1" ready_path="$2" limit_ms="$3" state
  local ticks=$(( (limit_ms + 19) / 20 )) index
  for ((index = 0; index < ticks; index += 1)); do
    if [ -s "$ready_path" ]; then
      return 0
    fi
    if [ ! -r "/proc/$pid/stat" ]; then
      return 1
    fi
    state="$(awk '{print $3}' "/proc/$pid/stat" 2>/dev/null || printf X)"
    if [ "$state" = Z ]; then
      return 1
    fi
    sleep 0.02
  done
  return 1
}

stop_active_runner() {
  local signal_name="$1" state
  if [ -z "$ACTIVE_RUNNER_PID" ]; then
    return 0
  fi
  if bounded_readiness_wait \
      "$ACTIVE_RUNNER_PID" "$ACTIVE_READINESS" "$READY_WAIT_MS" \
      && [ -n "$ACTIVE_RUNNER_START_TICKS" ]; then
    "${PYTHON[@]}" "$EVIDENCE" signal-bound-process \
      --pid "$ACTIVE_RUNNER_PID" \
      --expected-start-ticks "$ACTIVE_RUNNER_START_TICKS" \
      --signal "$signal_name" >/dev/null 2>&1 || true
  fi
  for _ in $(seq 1 500); do
    if [ ! -r "/proc/$ACTIVE_RUNNER_PID/stat" ]; then
      break
    fi
    state="$(awk '{print $3}' "/proc/$ACTIVE_RUNNER_PID/stat" 2>/dev/null || printf X)"
    if [ "$state" = Z ]; then
      break
    fi
    sleep 0.02
  done
  if [ -r "/proc/$ACTIVE_RUNNER_PID/stat" ]; then
    state="$(awk '{print $3}' "/proc/$ACTIVE_RUNNER_PID/stat" 2>/dev/null || printf X)"
    if [ "$state" != Z ]; then
      "${PYTHON[@]}" "$EVIDENCE" emergency-kill --readiness "$ACTIVE_READINESS" \
        --expected-wrapper-pid "$ACTIVE_RUNNER_PID" \
        --expected-stage-id "$ACTIVE_STEP" >/dev/null 2>&1 || return 1
    fi
  fi
  wait "$ACTIVE_RUNNER_PID" 2>/dev/null || true
  ACTIVE_RUNNER_PID=""
  ACTIVE_RUNNER_START_TICKS=""
  ACTIVE_READINESS=""
}

# shellcheck disable=SC2317
on_signal() {
  local signal_name="$1" exit_code="$2"
  trap '' HUP INT TERM
  if ! stop_active_runner "$signal_name"; then
    set_final internal_fault process_tree_cleanup_unproven 2
    exit 2
  fi
  set_final cancelled "signal_$signal_name" "$exit_code"
  exit "$exit_code"
}

# shellcheck disable=SC2317
publish_early_partial() {
  local observed_rc="$1"
  trap '' HUP INT TERM
  trap - EXIT
  if [ "$FINAL_SET" -eq 0 ]; then
    set_final internal_fault \
      "$([ "$observed_rc" -eq 0 ] && printf early_uncommitted_success || printf early_unexpected_exit)" \
      2
  fi
  if [ "$ART_DIR_CLAIMED" -eq 1 ] && [ -d "$ART_DIR" ]; then
    "${PYTHON[@]}" "$EVIDENCE" publish-partial-bundle --art-dir "$ART_DIR" \
      --run-id "$RUN_ID" --bead "$BEAD" --scenario "$SCENARIO" \
      --step "$ACTIVE_STEP" --reason "$FINAL_REASON" \
      --classification "$FINAL_VERDICT" \
      --argv-json '["scripts/tribunal/ref_vs_ref.sh"]' --cwd "$ROOT" \
      >/dev/null 2>&1 || true
  fi
  gate_release_note_once
  exit "$FINAL_EXIT"
}

# shellcheck disable=SC2317
on_exit() {
  local observed_rc="$1" final_root=unavailable first_divergence=none
  local receipt_root=unavailable publish_rc=0
  trap '' HUP INT TERM
  trap - EXIT
  set +e
  if [ "$RUN_STARTED" -eq 0 ]; then
    publish_early_partial "$observed_rc"
  fi
  if [ "$FINALIZING" -ne 0 ]; then
    gate_release_note_once
    exit 2
  fi
  FINALIZING=1
  if [ "$FINAL_SET" -eq 0 ]; then
    set_final internal_fault \
      "$([ "$observed_rc" -eq 0 ] && printf uncommitted_success || printf unexpected_shell_exit)" \
      2
  fi
  if final_root="$(hash_governed)"; then
    if [ "$FINAL_VERDICT" = pass ] && [ "$final_root" != "$INPUT_ROOT" ]; then
      set_final inconclusive governed_inputs_changed 3
    fi
  else
    set_final internal_fault final_workspace_hash_unavailable 2
    final_root=unavailable
  fi
  if [ -s "$PRETERMINAL_VALIDATION" ]; then
    receipt_root="$(read_json_field "$PRETERMINAL_VALIDATION" semantic_root)" \
      || receipt_root=unavailable
  fi
  if [ "$FINAL_VERDICT" != pass ]; then
    first_divergence="$FINAL_REASON"
  fi
  emit_event --string event run_end --string verdict "$FINAL_VERDICT" \
    --string reason_code "$FINAL_REASON" --integer process_exit "$FINAL_EXIT" \
    --string active_step "$ACTIVE_STEP" \
    --integer duration_ns "$(( $("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())') - START_NS ))" \
    --string cleanup_status retained_by_policy --string final_state "$final_root" \
    --string logical_root "$final_root" --string receipt_root "$receipt_root" \
    --string first_divergence "$first_divergence" \
    --string evidence_manifest manifest.json \
    --string bundle_commit bundle.complete.json \
    --string evidence_state pending_bundle_commit || publish_rc=2
  if [ "$publish_rc" -eq 0 ] && [ "$FINAL_VERDICT" = pass ]; then
    "${PYTHON[@]}" "$DOMAIN_VALIDATOR" --phase final --log "$LOG" \
      --run-id "$RUN_ID" --art-dir "$ART_DIR" --output "$FINAL_VALIDATION" \
      || publish_rc=2
  fi
  if [ "$publish_rc" -eq 0 ]; then
    "${PYTHON[@]}" "$EVIDENCE" validate-run --file "$LOG" --schema "$SCHEMA" \
      --expected-verdict "$FINAL_VERDICT" --artifact-root "$ART_DIR" \
      --output "$ART_DIR/run.validation.json" || publish_rc=2
  fi
  if [ "$publish_rc" -eq 0 ]; then
    "${PYTHON[@]}" "$EVIDENCE" manifest --art-dir "$ART_DIR" \
      --output "$ART_DIR/manifest.json" \
      --digest-output "$ART_DIR/manifest.digest" \
      --run-id "$RUN_ID" --bead "$BEAD" --scenario "$SCENARIO" \
      --verdict "$FINAL_VERDICT" --input-root "$INPUT_ROOT" \
      --final-root "$final_root" || publish_rc=2
  fi
  if [ "$publish_rc" -eq 0 ]; then
    "${PYTHON[@]}" "$EVIDENCE" complete-bundle --art-dir "$ART_DIR" \
      --manifest "$ART_DIR/manifest.json" \
      --digest "$ART_DIR/manifest.digest" \
      --output "$ART_DIR/bundle.complete.json" \
      --governed-root "$ROOT" "${GOVERNED_ARGS[@]}" \
      --expected-root "$final_root" --vendor-path "$VENDOR_PATH" \
      || publish_rc=2
  fi
  if [ "$publish_rc" -eq 0 ]; then
    "${PYTHON[@]}" "$EVIDENCE" adopt-bundle --art-dir "$ART_DIR" \
      --manifest "$ART_DIR/manifest.json" \
      --digest "$ART_DIR/manifest.digest" \
      --commit "$ART_DIR/bundle.complete.json" \
      --artifact-root "$ART_DIR" >/dev/null || publish_rc=2
  fi
  if [ "$publish_rc" -eq 0 ]; then
    "${PYTHON[@]}" "$EVIDENCE" validate-bundle --art-dir "$ART_DIR" \
      --manifest "$ART_DIR/manifest.json" \
      --digest "$ART_DIR/manifest.digest" \
      --commit "$ART_DIR/bundle.complete.json" \
      --artifact-root "$ART_DIR" >/dev/null || publish_rc=2
  fi
  if [ "$publish_rc" -ne 0 ]; then
    printf '[ref_vs_ref] INTERNAL FAULT: incomplete evidence bundle: %s\n' \
      "$ART_DIR" >&2
    gate_release_note_once
    exit 2
  fi
  printf '[ref_vs_ref] %s reason=%s evidence=%s\n' \
    "$FINAL_VERDICT" "$FINAL_REASON" "$ART_DIR" >&2
  gate_release_note_once
  exit "$FINAL_EXIT"
}

trap 'on_signal HUP 129' HUP
trap 'on_signal INT 130' INT
trap 'on_signal TERM 143' TERM
trap 'on_exit "$?"' EXIT

ACTIVE_STEP=artifact_directory_creation
mkdir -p "$(dirname "$ART_DIR")"
if ! mkdir "$ART_DIR" 2>/dev/null; then
  trap - EXIT
  echo "[ref_vs_ref] evidence directory already claimed: $ART_DIR" >&2
  gate_release_note_once
  exit 2
fi
ART_DIR_CLAIMED=1
ACTIVE_STEP=vendor_binding
"${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ROOT" \
  --vendor-path "$VENDOR_PATH" --output "$VENDOR_BINDING" \
  --artifact-root "$ART_DIR" || {
    set_final internal_fault early_vendor_binding_failure 2
    exit 2
  }
ACTIVE_STEP=run_start_emission
emit_event --new-log --string event run_start \
  --json-value argv '["scripts/tribunal/ref_vs_ref.sh"]' --string cwd "$ROOT" \
  --append-string claim_ids FLN-TRIBUNAL-REFERENCE-REFERENCE-NO-MOCK \
  --append-string invariant_ids D7 \
  --append-string invariant_ids D8 \
  --append-string invariant_ids FL-INV-01 \
  --append-string invariant_ids FL-INV-07 \
  --append-string gate_ids W1-tribunal-bootstrap \
  --string parity_ledger_row not_applicable_oracle_harness_self_consistency \
  --string epoch "$PIN_TAG" --string mode faithful --string profile e2e \
  --string platform "$(uname -srm)" --integer thread_count 1 \
  --json-value host_facts "$HOST_FACTS_JSON" \
  --string seed "reference-reference-$PIN_COMMIT" \
  --string cache_state "${FLN_E2E_CACHE_STATE:-uncontrolled}" \
  --string input_root "$INPUT_ROOT" --string vendor_binding vendor-binding.json \
  --producer-binding-root "$ROOT" "${GOVERNED_ARGS[@]}" \
  --json-value budgets "{\"capture_bytes_per_stream\":$CAPTURE_BYTES,\"output_budget_bytes\":$OUTPUT_BUDGET_BYTES,\"step_timeout_ms\":$TIMEOUT_MS,\"kill_grace_ms\":$GRACE_MS,\"max_slice_files\":1024,\"max_retained_artifact_bytes\":16777216}" \
  || {
    set_final internal_fault early_run_start_emission_failure 2
    exit 2
  }
: > "$HUMAN"
RUN_STARTED=1

supervise() {
  local step="$1"
  shift
  LAST_META="$ART_DIR/$step.meta.json"
  LAST_OUT="$ART_DIR/$step.out"
  LAST_ERR="$ART_DIR/$step.err"
  LAST_READY="$ART_DIR/$step.ready.json"
  local launch_ready="$ART_DIR/$step.launch.ready.json"
  local launch_release="$ART_DIR/$step.launch.release.json"
  ACTIVE_STEP="$step"
  setsid -- "${PYTHON[@]}" "$EVIDENCE" run --cwd "$ROOT" \
    --metadata "$LAST_META" --stdout "$LAST_OUT" --stderr "$LAST_ERR" \
    --readiness "$LAST_READY" --launch-ready "$launch_ready" \
    --launch-release "$launch_release" --artifact-root "$ART_DIR" \
    --capture-bytes "$CAPTURE_BYTES" \
    --output-budget-bytes "$OUTPUT_BUDGET_BYTES" \
    --timeout-ms "$TIMEOUT_MS" --grace-ms "$GRACE_MS" \
    --stage-id "$step" --semantic-failure-exit 101 -- "$@" &
  ACTIVE_RUNNER_PID=$!
  if ! ACTIVE_RUNNER_START_TICKS="$(
    setsid -- "${PYTHON[@]}" "$EVIDENCE" process-start-ticks \
      --pid "$ACTIVE_RUNNER_PID" --expected-parent-pid "$$" \
      --wait-ms "$READY_WAIT_MS" --session-leader 2>/dev/null
  )"; then
    terminate_unreleased_runner "$ACTIVE_RUNNER_PID" || true
    ACTIVE_RUNNER_PID=""
    set_final internal_fault active_runner_identity_unproven 2
    exit 2
  fi
  ACTIVE_READINESS="$LAST_READY"
  if ! setsid -- "${PYTHON[@]}" "$EVIDENCE" release-process-launch \
      --ready "$launch_ready" --output "$launch_release" \
      --artifact-root "$ART_DIR" --stage-id "$step" \
      --pid "$ACTIVE_RUNNER_PID" \
      --expected-start-ticks "$ACTIVE_RUNNER_START_TICKS" \
      --expected-parent-pid "$$" --wait-ms "$READY_WAIT_MS"; then
    stop_active_runner TERM || true
    set_final internal_fault active_runner_launch_unproven 2
    exit 2
  fi
  if wait "$ACTIVE_RUNNER_PID"; then
    LAST_RC=0
  else
    LAST_RC=$?
  fi
  ACTIVE_RUNNER_PID=""
  ACTIVE_RUNNER_START_TICKS=""
  ACTIVE_READINESS=""
}

inspect_supervisor() {
  local step="$1" expected_class
  if [ ! -s "$LAST_META" ]; then
    set_final internal_fault "$step:missing_supervisor_metadata" 2
    exit 2
  fi
  LAST_CLASSIFICATION="$(read_json_field "$LAST_META" classification)"
  LAST_REASON="$(read_json_field "$LAST_META" reason_code)"
  LAST_META_WRAPPER="$(read_json_field "$LAST_META" wrapper_exit)"
  LAST_CHILD_EXIT="$(read_json_field "$LAST_META" child_exit)"
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
  if [ "$LAST_META_WRAPPER" != "$LAST_RC" ] \
      || [ "$LAST_CLASSIFICATION" != "$expected_class" ]; then
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
  local step="$1" expected="$2" actual="$3" validation="$4"
  local subject_before="$5" subject_after="$6"
  local global_before="$7" global_after="$8"
  emit_event --string event step --string step_id "$step" \
    --string assertion pass --string expected "$expected" \
    --string actual "$actual" --string input_root "$global_before" \
    --string final_state "$global_after" \
    --string validation_artifact "$validation" \
    --string expected_supervisor_classification pass \
    --integer expected_wrapper_exit 0 --integer expected_child_exit 0 \
    --string subject_root "$subject_before" \
    --string subject_final_state "$subject_after" \
    --json-file supervisor "$LAST_META"
}

record_failure() {
  local step="$1" reason="$2"
  note "FAIL step=$step: $reason"
  emit_event --string event step --string step_id "$step" \
    --string assertion fail --string expected "$reason" \
    --string actual "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
    --string input_root "$GLOBAL_BEFORE" --string final_state "$GLOBAL_AFTER" \
    --string validation_artifact not_applicable \
    --string expected_supervisor_classification pass \
    --integer expected_wrapper_exit 0 --integer expected_child_exit 0 \
    --string subject_root "$SUBJECT_BEFORE" \
    --string subject_final_state "$SUBJECT_AFTER" \
    --json-file supervisor "$LAST_META"
  set_final fail "$step:$reason" 1
  exit 1
}

snapshot_before() {
  local step="$1"
  SUBJECT_BEFORE="$(hash_subject)" || {
    set_final internal_fault "$step:subject_pre_hash_unavailable" 2
    exit 2
  }
  GLOBAL_BEFORE="$(hash_governed)" || {
    set_final internal_fault "$step:global_pre_hash_unavailable" 2
    exit 2
  }
}

snapshot_after() {
  local step="$1"
  SUBJECT_AFTER="$(hash_subject)" || {
    set_final internal_fault "$step:subject_post_hash_unavailable" 2
    exit 2
  }
  GLOBAL_AFTER="$(hash_governed)" || {
    set_final internal_fault "$step:global_post_hash_unavailable" 2
    exit 2
  }
  if [ "$SUBJECT_BEFORE" != "$SUBJECT_AFTER" ] \
      || [ "$GLOBAL_BEFORE" != "$GLOBAL_AFTER" ]; then
    note "INCONCLUSIVE step=$step: governed_inputs_changed"
    set_final inconclusive "$step:governed_inputs_changed" 3
    exit 3
  fi
}

run_step() {
  local step="$1" expectation="$2" required_pattern="$3" validation_mode="$4"
  shift 4
  local supervisor_validation="$ART_DIR/$step.supervisor.validation.json"
  local validation_artifact
  snapshot_before "$step"
  note "running step=$step"
  supervise "$step" "$@"
  inspect_supervisor "$step"
  snapshot_after "$step"
  "${PYTHON[@]}" "$EVIDENCE" validate-supervisor --file "$LAST_META" \
    --expected-stage-id "$step" --artifact-root "$ART_DIR" \
    --output "$supervisor_validation" \
    || record_failure "$step" independent_supervisor_validation_failed
  if [ "$LAST_CLASSIFICATION" != pass ] || [ "$LAST_RC" -ne 0 ] \
      || [ "$LAST_CHILD_EXIT" != 0 ]; then
    record_failure "$step" supervisor_contract_mismatch
  fi
  if [ "$required_pattern" != - ] \
      && ! grep -Fq -- "$required_pattern" "$LAST_OUT" "$LAST_ERR"; then
    record_failure "$step" intended_reason_missing_from_capture
  fi
  case "$validation_mode" in
    supervisor) validation_artifact="${supervisor_validation#"$ART_DIR"/}" ;;
    preterminal)
      [ -s "$PRETERMINAL_VALIDATION" ] \
        || record_failure "$step" preterminal_validation_artifact_absent
      validation_artifact="${PRETERMINAL_VALIDATION#"$ART_DIR"/}"
      ;;
    *) record_failure "$step" unknown_validation_mode ;;
  esac
  record_step "$step" "$expectation" \
    "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
    "$validation_artifact" "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
    "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
}

run_worker_step() {
  local step="$1" expectation="$2" pattern="$3"
  run_step "$step" "$expectation" "$pattern" supervisor \
    env FLN_REF_ART_DIR="$ART_DIR" \
    "$ROOT/scripts/tribunal/ref_vs_ref.sh" --worker "$step"
}

run_worker_step oracle_binding \
  "SUITE.lock pin, installed binary, epoch lab and nonempty slice agree" \
  "oracle_binding tag=$PIN_TAG commit=$PIN_COMMIT"
run_worker_step reference_run_a \
  "the real pinned Reference records every C1/D1 slice artifact" \
  "slice=run-a files="
run_worker_step reference_run_b \
  "a second real pinned Reference run records the same slice" \
  "slice=run-b files="
run_worker_step determinism \
  "the two semantic transcript trees are byte-identical" \
  "reference semantic trees are byte-identical"
run_worker_step baseline \
  "the live semantic tree matches the immutable epoch baseline" \
  "published epoch baseline matched"
run_worker_step seeded_divergence_artifact \
  "an artifact-level planted body is detected and surfaced" \
  "plant=artifact detected"
run_worker_step seeded_divergence_line \
  "a line-level planted body is detected and surfaced" \
  "plant=line detected"
run_worker_step seeded_divergence_subline \
  "a sub-line planted body is detected and surfaced" \
  "plant=subline detected"
run_worker_step seeded_divergence_diagnostic \
  "a diagnostic planted body is detected and surfaced" \
  "plant=diagnostic detected"
run_worker_step seeded_divergence_exit \
  "an exit-level planted body is detected and surfaced" \
  "plant=exit detected"
run_worker_step non_authoritative_outcome \
  "a killed oracle is non-authoritative while genuine rc=1 stays authoritative" \
  "classification=non-authoritative control_rc=1 authoritative"
run_worker_step recovery \
  "the pristine semantic trees remain byte-identical after every scratch plant" \
  "recovery restored"

run_step bundle_validation \
  "an independent parser accepts the closed preterminal roster and retained plants" \
  "preterminal validation passed" preterminal \
  "${PYTHON[@]}" "$DOMAIN_VALIDATOR" --phase preterminal --log "$LOG" \
  --run-id "$RUN_ID" --art-dir "$ART_DIR" --output "$PRETERMINAL_VALIDATION"

ACTIVE_STEP=bundle_validation
set_final pass all_reference_reference_obligations_satisfied 0
exit 0
