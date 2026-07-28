#!/usr/bin/env bash
# W4 Vellum lexer no-mock evidence lane. The existing lexer suites are run as
# named targets with anti-vacuity floors, then a local artifact-only driver
# exercises the public lexer against three real files. Canonical semantic
# NDJSON and bounded telemetry are written separately and scripts/evidence.py
# independently validates both before the bundle can be committed.

set -Eeuo pipefail

PYTHON_BIN="$(command -v python3 || true)"
[ -n "$PYTHON_BIN" ] || {
  echo "[lexer_no_mock_e2e] setup failure: python3 is required" >&2
  exit 2
}
PYTHON=("$PYTHON_BIN" -I -S)
HOSTILE_PYTHON_CONFIGURATION=()
while IFS= read -r environment_name; do
  [[ "$environment_name" == PYTHON* ]] \
    && HOSTILE_PYTHON_CONFIGURATION+=("$environment_name")
done < <(compgen -e | LC_ALL=C sort)
if ((${#HOSTILE_PYTHON_CONFIGURATION[@]} > 0)); then
  printf '[lexer_no_mock_e2e] setup failure: sealed_interpreter_hostile_environment names=%s\n' \
    "$(IFS=,; printf '%s' "${HOSTILE_PYTHON_CONFIGURATION[*]}")" >&2
  exit 2
fi
for required_command in cargo setsid sha256sum; do
  command -v "$required_command" >/dev/null 2>&1 || {
    echo "[lexer_no_mock_e2e] setup failure: $required_command is required" >&2
    exit 2
  }
done

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
cd "$ROOT"
EVIDENCE="$ROOT/scripts/evidence.py"
SCHEMA="fln.e2e/2"
BEAD="franken_lean-jbru"
SCENARIO="lexer_no_mock_e2e"
RUN_ID="lexer-no-mock-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_ROOT="${FLN_E2E_ART_ROOT:-$ROOT/target/e2e}"
ART_DIR="$ART_ROOT/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
HUMAN="$ART_DIR/human.log"
VENDOR_PATH="vendor/lean4-src"
VENDOR_BINDING="$ART_DIR/vendor-binding.json"
DRIVER_DIR="$ART_DIR/real-file-driver"
DRIVER_BIN="${CARGO_TARGET_DIR:-$ROOT/target/cargo}/e2e-lexer-no-mock/debug/fln-lexer-e2e-driver"
BUILD_TARGET="${CARGO_TARGET_DIR:-$ROOT/target/cargo}/e2e-lexer-no-mock"
CAPTURE_BYTES="${FLN_E2E_CAPTURE_BYTES:-262144}"
OUTPUT_BUDGET_BYTES="${FLN_E2E_OUTPUT_BUDGET_BYTES:-16777216}"
TIMEOUT_MS="${FLN_E2E_TIMEOUT_MS:-300000}"
GRACE_MS="${FLN_E2E_KILL_GRACE_MS:-2000}"
READY_WAIT_MS="${FLN_E2E_READY_WAIT_MS:-30000}"
case "$READY_WAIT_MS" in
  ''|*[!0-9]*)
    echo "[lexer_no_mock_e2e] setup failure: FLN_E2E_READY_WAIT_MS must be numeric" >&2
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
  Cargo.toml
  Cargo.lock
  SUITE.lock
  rust-toolchain.toml
  ci/VERIFICATION_MANIFEST.jsonl
  crates/fln-core
  crates/fln-syntax
  scripts/e2e/lexer_no_mock_e2e.sh
  scripts/evidence.py
  scripts/check.sh
  scripts/lib/gate_lock.sh
  vendor/NOTICE
  .github/workflows/ci.yml
)
SUBJECT_PATHS=(
  crates/fln-syntax
  scripts/evidence.py
  scripts/e2e/lexer_no_mock_e2e.sh
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

# SC1091: the library is checked directly as its own input to check.sh's shellcheck stage.
# shellcheck source=scripts/lib/gate_lock.sh
# shellcheck disable=SC1091
. "$ROOT/scripts/lib/gate_lock.sh"
trap 'fln_gate_release_note "$SCENARIO"' EXIT
fln_gate_acquire "$SCENARIO"

if ! INPUT_ROOT="$(
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path "$VENDOR_PATH"
)"; then
  echo "[lexer_no_mock_e2e] setup failure: cannot hash governed inputs" >&2
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
  printf '[lexer_no_mock_e2e] %s\n' "$*" | tee -a "$HUMAN" >&2
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

read_meta_field() {
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
    state="$(
      awk '{print $3}' "/proc/$ACTIVE_RUNNER_PID/stat" 2>/dev/null || printf X
    )"
    if [ "$state" = Z ]; then
      break
    fi
    sleep 0.02
  done
  if [ -r "/proc/$ACTIVE_RUNNER_PID/stat" ]; then
    state="$(
      awk '{print $3}' "/proc/$ACTIVE_RUNNER_PID/stat" 2>/dev/null || printf X
    )"
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
      --argv-json '["scripts/e2e/lexer_no_mock_e2e.sh"]' --cwd "$ROOT" \
      >/dev/null 2>&1 || true
  fi
  gate_release_note_once
  exit "$FINAL_EXIT"
}

# shellcheck disable=SC2317
on_exit() {
  local observed_rc="$1" final_root=unavailable first_divergence=none
  local publish_rc=0
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
      set_final inconclusive final_workspace_changed 3
    fi
  else
    set_final internal_fault final_workspace_hash_unavailable 2
    final_root=unavailable
  fi
  if [ "$FINAL_VERDICT" != pass ]; then
    first_divergence="$FINAL_REASON"
  fi
  emit_event --string event run_end --string verdict "$FINAL_VERDICT" \
    --string reason_code "$FINAL_REASON" --integer process_exit "$FINAL_EXIT" \
    --string active_step "$ACTIVE_STEP" \
    --integer duration_ns "$(( $("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())') - START_NS ))" \
    --string cleanup_status retained_by_policy --string final_state "$final_root" \
    --string logical_root "$final_root" \
    --string receipt_root not_applicable_lexer_semantic_schema \
    --string first_divergence "$first_divergence" \
    --string evidence_manifest manifest.json \
    --string bundle_commit bundle.complete.json \
    --string evidence_state pending_bundle_commit || publish_rc=2
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
    printf '[lexer_no_mock_e2e] INTERNAL FAULT: incomplete bundle %s\n' \
      "$ART_DIR" >&2
    gate_release_note_once
    exit 2
  fi
  printf '[lexer_no_mock_e2e] %s reason=%s evidence=%s\n' \
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
  echo "[lexer_no_mock_e2e] evidence directory already claimed: $ART_DIR" >&2
  gate_release_note_once
  exit 2
fi
ART_DIR_CLAIMED=1
mkdir "$ART_DIR/inputs"
mkdir "$DRIVER_DIR"
mkdir "$DRIVER_DIR/src"
: > "$HUMAN"
printf 'def answer := 42\n' > "$ART_DIR/inputs/positive.lean"
printf 'def bad :=\t42\n' > "$ART_DIR/inputs/failure.lean"
printf 'def bad :=\t42\n#check\tbad\n' > "$ART_DIR/inputs/recovery.lean"

cat > "$DRIVER_DIR/Cargo.toml" <<EOF
[package]
name = "fln-lexer-e2e-driver"
version = "0.0.0"
edition = "2024"
publish = false

[workspace]

[dependencies]
fln-syntax = { path = "$ROOT/crates/fln-syntax" }
EOF

cat > "$DRIVER_DIR/src/main.rs" <<'RS'
#![forbid(unsafe_code)]

use fln_syntax::recover::{Lexed, lex, lex_recovering};
use fln_syntax::source::SourceText;
use std::env;
use std::fmt::Write as _;
use std::fs;
use std::process;

const MAX_INPUT_BYTES: usize = 4_096;
const MAX_DIAGNOSTICS: usize = 8;

fn refuse(message: &str) -> ! {
    eprintln!("lexer driver setup failure: {message}");
    process::exit(2);
}

fn json_string(value: &str) -> String {
    let mut encoded = String::from("\"");
    for character in value.chars() {
        match character {
            '"' => encoded.push_str("\\\""),
            '\\' => encoded.push_str("\\\\"),
            '\u{08}' => encoded.push_str("\\b"),
            '\u{0c}' => encoded.push_str("\\f"),
            '\n' => encoded.push_str("\\n"),
            '\r' => encoded.push_str("\\r"),
            '\t' => encoded.push_str("\\t"),
            character if character <= '\u{1f}' => {
                write!(encoded, "\\u{:04x}", character as u32)
                    .expect("writing to a String cannot fail");
            }
            character => encoded.push(character),
        }
    }
    encoded.push('"');
    encoded
}

fn diagnostics_json(lexed: &Lexed) -> String {
    lexed
        .errors
        .iter()
        .map(|recovered| {
            format!(
                "{{\"byte_offset\":{},\"message\":{}}}",
                recovered.error.at().0,
                json_string(recovered.error.message())
            )
        })
        .collect::<Vec<_>>()
        .join(",")
}

fn result_json(lexed: &Lexed) -> String {
    format!(
        "{{\"accepted\":{},\"diagnostics\":[{}]}}",
        lexed.accepted(),
        diagnostics_json(lexed)
    )
}

fn main() {
    let arguments = env::args().collect::<Vec<_>>();
    if arguments.len() != 8 {
        refuse(
            "expected CASE INPUT INPUT_ARTIFACT INPUT_SHA256 RUN_ID SEMANTIC TELEMETRY",
        );
    }
    let case = &arguments[1];
    if !matches!(case.as_str(), "positive" | "failure" | "recovery") {
        refuse("case is not positive, failure, or recovery");
    }
    let input_path = &arguments[2];
    let input_artifact = &arguments[3];
    let input_sha256 = &arguments[4];
    let run_id = &arguments[5];
    let semantic_path = &arguments[6];
    let telemetry_path = &arguments[7];
    if input_sha256.len() != 64
        || !input_sha256
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        refuse("input digest is not lowercase SHA-256");
    }
    let input = fs::read(input_path)
        .unwrap_or_else(|error| refuse(&format!("cannot read input: {error}")));
    if input.len() > MAX_INPUT_BYTES {
        refuse("input exceeds the telemetry bound");
    }
    let source = SourceText::from_utf8(&input)
        .unwrap_or_else(|error| refuse(&format!("input is not UTF-8: {error}")));
    let plain = lex(&source);
    let recovering = lex_recovering(&source);
    let acceptance_equal = plain.accepted() == recovering.accepted();
    let status = if acceptance_equal { "pass" } else { "fail" };
    let semantic = format!(
        concat!(
            "{{\"acceptance_relation\":{},\"case\":{},\"data_grade\":\"verified\",",
            "\"input_artifact\":{},\"input_sha256\":{},\"plain\":{},",
            "\"recovering\":{},\"run_id\":{},",
            "\"schema\":\"fln.e2e.lexer-semantic\",\"status\":{},\"version\":1}}\n"
        ),
        json_string(if acceptance_equal { "equal" } else { "different" }),
        json_string(case),
        json_string(input_artifact),
        json_string(input_sha256),
        result_json(&plain),
        result_json(&recovering),
        json_string(run_id),
        json_string(status),
    );
    let observed_diagnostics = plain.errors.len() + recovering.errors.len();
    let telemetry = format!(
        concat!(
            "{{\"case\":{},\"event\":\"phase_resources\",",
            "\"max_diagnostics\":{},\"max_input_bytes\":{},",
            "\"observed_diagnostics\":{},\"observed_input_bytes\":{},",
            "\"run_id\":{},\"schema\":\"fln.e2e.lexer-telemetry\",",
            "\"timing_used_as_gate\":false,\"version\":1}}\n"
        ),
        json_string(case),
        MAX_DIAGNOSTICS,
        MAX_INPUT_BYTES,
        observed_diagnostics,
        input.len(),
        json_string(run_id),
    );
    fs::write(semantic_path, semantic)
        .unwrap_or_else(|error| refuse(&format!("cannot write semantic evidence: {error}")));
    fs::write(telemetry_path, telemetry)
        .unwrap_or_else(|error| refuse(&format!("cannot write telemetry: {error}")));
    println!("lexer-semantic case={case} status={status}");
    if !acceptance_equal || observed_diagnostics > MAX_DIAGNOSTICS {
        process::exit(1);
    }
}
RS

ACTIVE_STEP=vendor_binding
"${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ROOT" \
  --vendor-path "$VENDOR_PATH" --output "$VENDOR_BINDING" \
  --artifact-root "$ART_DIR" || {
    set_final internal_fault early_vendor_binding_failure 2
    exit 2
  }
ACTIVE_STEP=run_start_emission
emit_event --new-log --string event run_start \
  --json-value argv '["scripts/e2e/lexer_no_mock_e2e.sh"]' \
  --string cwd "$ROOT" \
  --append-string claim_ids franken_lean-jbru-lexer-no-mock \
  --append-string invariant_ids FL-INV-01 \
  --append-string invariant_ids FL-INV-07 \
  --append-string gate_ids W4 \
  --string parity_ledger_row bounded_lexer_suite_and_acceptance_law \
  --string epoch lean-v4.32.0 --string mode sound --string profile e2e \
  --string platform "$(uname -srm)" --integer thread_count 32 \
  --json-value thread_matrix '[1,8,32]' \
  --json-value host_facts "$HOST_FACTS_JSON" \
  --string seed lexer-real-file-v1 \
  --string cache_state "${FLN_E2E_CACHE_STATE:-uncontrolled}" \
  --string input_root "$INPUT_ROOT" --string vendor_binding vendor-binding.json \
  --producer-binding-root "$ROOT" "${GOVERNED_ARGS[@]}" \
  --json-value budgets "{\"capture_bytes_per_stream\":$CAPTURE_BYTES,\"output_budget_bytes\":$OUTPUT_BUDGET_BYTES,\"step_timeout_ms\":$TIMEOUT_MS,\"kill_grace_ms\":$GRACE_MS,\"max_input_bytes\":4096,\"max_diagnostics\":8}" \
  || {
    set_final internal_fault early_run_start_emission_failure 2
    exit 2
  }
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
    --stage-id "$step" -- "$@" &
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
  LAST_CLASSIFICATION="$(read_meta_field "$LAST_META" classification)"
  LAST_REASON="$(read_meta_field "$LAST_META" reason_code)"
  LAST_META_WRAPPER="$(read_meta_field "$LAST_META" wrapper_exit)"
  LAST_CHILD_EXIT="$(read_meta_field "$LAST_META" child_exit)"
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
    --string expected_supervisor_classification "$LAST_CLASSIFICATION" \
    --integer expected_wrapper_exit "$LAST_RC" \
    --integer expected_child_exit "$LAST_CHILD_EXIT" \
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

validate_test_floor() {
  local step="$1" floor="$2" ignored_requirement="$3"
  local output="$ART_DIR/$step.counts.json"
  "${PYTHON[@]}" - "$LAST_OUT" "$LAST_ERR" "$step" "$floor" \
    "$ignored_requirement" "$output" <<'PY'
import json
import os
import pathlib
import re
import sys

stdout_path, stderr_path, step, raw_floor, ignored_requirement, output_path = sys.argv[1:]
text = (
    pathlib.Path(stdout_path).read_text(encoding="utf-8")
    + pathlib.Path(stderr_path).read_text(encoding="utf-8")
)
if "test result: FAILED" in text:
    raise SystemExit(f"{step}: libtest reported FAILED")
matches = [
    (int(passed), int(ignored))
    for passed, ignored in re.findall(
        r"test result: ok\. ([0-9]+) passed; [0-9]+ failed; "
        r"([0-9]+) ignored;",
        text,
    )
]
floor = int(raw_floor)
eligible = [
    (passed, ignored)
    for passed, ignored in matches
    if passed >= floor
    and (ignored_requirement != "exactly_one" or ignored == 1)
]
if not matches or not eligible:
    raise SystemExit(
        f"{step}: no successful libtest summary met floor={floor} "
        f"ignored={ignored_requirement}; observed={matches}"
    )
report = {
    "floor": floor,
    "ignored_requirement": ignored_requirement,
    "observed": [
        {"ignored": ignored, "passed": passed}
        for passed, ignored in matches
    ],
    "schema": "fln.e2e.libtest-floor/1",
    "status": "pass",
    "step": step,
}
data = (
    json.dumps(report, allow_nan=False, sort_keys=True, separators=(",", ":"))
    + "\n"
).encode()
descriptor = os.open(output_path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o644)
with os.fdopen(descriptor, "wb") as destination:
    destination.write(data)
PY
}

run_test_step() {
  local step="$1" floor="$2" ignored_requirement="$3"
  shift 3
  snapshot_before "$step"
  note "running $step with libtest floor $floor"
  supervise "$step" env CARGO_TARGET_DIR="$BUILD_TARGET" "$@"
  inspect_supervisor "$step"
  snapshot_after "$step"
  if [ "$LAST_CLASSIFICATION" != pass ] || [ "$LAST_RC" -ne 0 ] \
      || [ "$LAST_CHILD_EXIT" != 0 ]; then
    record_failure "$step" cargo_test_failed
  fi
  if ! validate_test_floor "$step" "$floor" "$ignored_requirement"; then
    record_failure "$step" libtest_floor_or_status_failed
  fi
  record_step "$step" \
    "cargo-test/pass/floor>=$floor/ignored=$ignored_requirement" \
    "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
    "$step.counts.json" "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
    "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
}

run_test_step lexer_state_model 7 any \
  cargo test --locked -q -p fln-syntax --test lexer_state_model
run_test_step lexer_fuzz 5 any \
  cargo test --locked -q -p fln-syntax --test lexer_fuzz
run_test_step lexer_thread_matrix 5 any \
  cargo test --locked -q -p fln-syntax --test lexer_thread_matrix
run_test_step lexer_resource_bounds 7 any \
  cargo test --locked -q -p fln-syntax --test lexer_resource_bounds
run_test_step token_table_totality 9 any \
  cargo test --locked -q -p fln-syntax --test token_table_totality
run_test_step incremental_lex_property 5 any \
  cargo test --locked -q -p fln-syntax --test incremental_lex_property
run_test_step golden_vellum 5 exactly_one \
  cargo test --locked -q -p fln-syntax --test golden_vellum
run_test_step syntax_lib 82 any \
  cargo test --locked -q -p fln-syntax --lib

ACTIVE_STEP=build_real_file_driver
snapshot_before "$ACTIVE_STEP"
note "building retained real-file lexer driver"
supervise "$ACTIVE_STEP" env CARGO_TARGET_DIR="$BUILD_TARGET" \
  cargo build --manifest-path "$DRIVER_DIR/Cargo.toml"
inspect_supervisor "$ACTIVE_STEP"
snapshot_after "$ACTIVE_STEP"
if [ "$LAST_CLASSIFICATION" != pass ] || [ "$LAST_RC" -ne 0 ] \
    || [ "$LAST_CHILD_EXIT" != 0 ] || [ ! -x "$DRIVER_BIN" ] \
    || [ ! -f "$DRIVER_DIR/Cargo.lock" ]; then
  record_failure "$ACTIVE_STEP" real_file_driver_build_failed
fi
record_step "$ACTIVE_STEP" \
  "artifact-only-driver/build/pass/wrapper=0/child=0" \
  "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
  not_applicable "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
  "$GLOBAL_BEFORE" "$GLOBAL_AFTER"

run_real_file_case() {
  local case="$1"
  local step="${case}_file"
  local input="$ART_DIR/inputs/$case.lean"
  local input_artifact="inputs/$case.lean"
  local digest semantic telemetry
  digest="$(sha256sum "$input" | cut -d' ' -f1)"
  semantic="$ART_DIR/$case.semantic.ndjson"
  telemetry="$ART_DIR/$case.telemetry.ndjson"
  snapshot_before "$step"
  note "running real-file lexer case=$case"
  supervise "$step" "$DRIVER_BIN" "$case" "$input" "$input_artifact" \
    "$digest" "$RUN_ID" "$semantic" "$telemetry"
  inspect_supervisor "$step"
  snapshot_after "$step"
  if [ "$LAST_CLASSIFICATION" != pass ] || [ "$LAST_RC" -ne 0 ] \
      || [ "$LAST_CHILD_EXIT" != 0 ] || [ ! -s "$semantic" ] \
      || [ ! -s "$telemetry" ]; then
    record_failure "$step" real_file_lexer_execution_failed
  fi
  record_step "$step" \
    "public-lexer/$case/canonical-semantic-and-telemetry" \
    "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
    "$case.semantic.ndjson" "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
    "$GLOBAL_BEFORE" "$GLOBAL_AFTER"
}

run_real_file_case positive
run_real_file_case failure
run_real_file_case recovery

ACTIVE_STEP=semantic_validation
snapshot_before "$ACTIVE_STEP"
note "independently validating lexer semantics, telemetry, and real inputs"
supervise "$ACTIVE_STEP" "${PYTHON[@]}" "$EVIDENCE" validate-lexer-no-mock \
  --expected-run-id "$RUN_ID" \
  --positive-semantic "$ART_DIR/positive.semantic.ndjson" \
  --positive-telemetry "$ART_DIR/positive.telemetry.ndjson" \
  --positive-input "$ART_DIR/inputs/positive.lean" \
  --positive-stdout "$ART_DIR/positive_file.out" \
  --positive-stderr "$ART_DIR/positive_file.err" \
  --failure-semantic "$ART_DIR/failure.semantic.ndjson" \
  --failure-telemetry "$ART_DIR/failure.telemetry.ndjson" \
  --failure-input "$ART_DIR/inputs/failure.lean" \
  --failure-stdout "$ART_DIR/failure_file.out" \
  --failure-stderr "$ART_DIR/failure_file.err" \
  --recovery-semantic "$ART_DIR/recovery.semantic.ndjson" \
  --recovery-telemetry "$ART_DIR/recovery.telemetry.ndjson" \
  --recovery-input "$ART_DIR/inputs/recovery.lean" \
  --recovery-stdout "$ART_DIR/recovery_file.out" \
  --recovery-stderr "$ART_DIR/recovery_file.err" \
  --artifact-root "$ART_DIR" --output "$ART_DIR/lexer.validation.json"
inspect_supervisor "$ACTIVE_STEP"
snapshot_after "$ACTIVE_STEP"
if [ "$LAST_CLASSIFICATION" != pass ] || [ "$LAST_RC" -ne 0 ] \
    || [ "$LAST_CHILD_EXIT" != 0 ] \
    || [ ! -s "$ART_DIR/lexer.validation.json" ]; then
  record_failure "$ACTIVE_STEP" independent_semantic_validation_failed
fi
record_step "$ACTIVE_STEP" \
  "lexer-validation/positive-failure-recovery/pass" \
  "$LAST_CLASSIFICATION/wrapper=$LAST_RC/child=$LAST_CHILD_EXIT" \
  lexer.validation.json "$SUBJECT_BEFORE" "$SUBJECT_AFTER" \
  "$GLOBAL_BEFORE" "$GLOBAL_AFTER"

run_test_step final_real_recheck 82 any \
  cargo test --locked -q -p fln-syntax

ACTIVE_STEP=final_real_recheck
set_final pass all_lexer_no_mock_obligations_satisfied 0
exit 0
