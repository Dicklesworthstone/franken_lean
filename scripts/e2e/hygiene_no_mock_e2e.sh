#!/usr/bin/env bash
# W4 production macro-hygiene no-mock evidence lane.
# The named Rust suites exercise the public quotation API, the pinned Reference
# supplies the overlapping scope oracle, and an independent validator keeps
# canonical semantic facts separate from operational telemetry.

set -Eeuo pipefail

PYTHON_BIN="$(command -v python3 || true)"
[ -n "$PYTHON_BIN" ] || {
  printf '[hygiene_no_mock_e2e] setup failure: python3 is required\n' >&2
  exit 2
}
PYTHON=("$PYTHON_BIN" -I -S)
for required_command in cargo setsid sha256sum; do
  command -v "$required_command" >/dev/null 2>&1 || {
    printf '[hygiene_no_mock_e2e] setup failure: %s is required\n' \
      "$required_command" >&2
    exit 2
  }
done

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
cd "$ROOT"
EVIDENCE="$ROOT/scripts/evidence.py"
SCHEMA="fln.e2e/2"
BEAD="franken_lean-7m54"
SCENARIO="hygiene_no_mock_e2e"
RUN_ID="hygiene-no-mock-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_ROOT="${FLN_E2E_ART_ROOT:-$ROOT/target/e2e}"
ART_DIR="$ART_ROOT/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
VENDOR_PATH="vendor/lean4-src"
VENDOR_BINDING="$ART_DIR/vendor-binding.json"
BUILD_TARGET="${CARGO_TARGET_DIR:-$ROOT/target/cargo}/e2e-hygiene"
CAPTURE_BYTES="${FLN_E2E_CAPTURE_BYTES:-262144}"
OUTPUT_BUDGET_BYTES="${FLN_E2E_OUTPUT_BUDGET_BYTES:-16777216}"
TIMEOUT_MS="${FLN_E2E_TIMEOUT_MS:-600000}"
GRACE_MS="${FLN_E2E_KILL_GRACE_MS:-2000}"
START_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
SEQ=0

PIN_TAG="$(
  awk '/^reference / {
    for (i = 1; i <= NF; i += 1) {
      if ($i ~ /^tag=/) {
        sub(/^tag=/, "", $i)
        print $i
      }
    }
  }' SUITE.lock
)"
[ "$PIN_TAG" = "v4.32.0" ] || {
  printf '[hygiene_no_mock_e2e] setup failure: unexpected Reference pin %s\n' \
    "$PIN_TAG" >&2
  exit 2
}
ELAN_ROOT="${ELAN_HOME:-$HOME/.elan}"
REFERENCE_LEAN="$ELAN_ROOT/toolchains/leanprover--lean4---$PIN_TAG/bin/lean"
[ -x "$REFERENCE_LEAN" ] || {
  printf '[hygiene_no_mock_e2e] inconclusive: pinned Reference binary is absent\n' >&2
  exit 3
}

INPUT_PATHS=(
  Cargo.toml
  Cargo.lock
  SUITE.lock
  rust-toolchain.toml
  ci/VERIFICATION_MANIFEST.jsonl
  crates/fln-core
  crates/fln-hash
  crates/fln-syntax
  crates/fln-parse
  scripts/e2e/hygiene_no_mock_e2e.sh
  scripts/evidence.py
  scripts/lib/gate_lock.sh
  vendor/NOTICE
)
SUBJECT_PATHS=(
  crates/fln-syntax/src/hygiene.rs
  crates/fln-parse/src/macro_expand.rs
  crates/fln-parse/tests/hygiene_scope_model.rs
  crates/fln-parse/tests/generated_name_property.rs
  crates/fln-parse/tests/quotation_roundtrip.rs
  crates/fln-parse/tests/macro_syntax_fuzz.rs
  crates/fln-parse/tests/hygiene_no_mock_e2e.rs
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

mkdir -p "$ART_ROOT"
if ! mkdir "$ART_DIR" 2>/dev/null; then
  printf '[hygiene_no_mock_e2e] setup failure: artifact path is not fresh: %s\n' \
    "$ART_DIR" >&2
  exit 2
fi

"${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ROOT" \
  --vendor-path "$VENDOR_PATH" --output "$VENDOR_BINDING" \
  --artifact-root "$ART_DIR" || {
    printf '[hygiene_no_mock_e2e] setup failure: cannot bind vendored Reference\n' >&2
    exit 2
  }
INPUT_ROOT="$(
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path "$VENDOR_PATH"
)" || {
  printf '[hygiene_no_mock_e2e] setup failure: cannot hash governed inputs\n' >&2
  exit 2
}
SUBJECT_ROOT="$(
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" \
    "${SUBJECT_HASH_ARGS[@]}"
)" || {
  printf '[hygiene_no_mock_e2e] setup failure: cannot hash subject inputs\n' >&2
  exit 2
}
HOST_FACTS_JSON="$(
  "${PYTHON[@]}" -c \
    'import json,platform; print(json.dumps({"machine":platform.machine(),"python":platform.python_version(),"release":platform.release(),"system":platform.system()},sort_keys=True,separators=(",",":")))'
)"

emit_event() {
  local sequence="$SEQ"
  SEQ=$((SEQ + 1))
  "${PYTHON[@]}" "$EVIDENCE" emit --file "$LOG" \
    --artifact-root "$ART_DIR" \
    --string schema "$SCHEMA" --string run_id "$RUN_ID" \
    --string bead "$BEAD" --string scenario "$SCENARIO" \
    --integer sequence "$sequence" \
    --integer monotonic_ns "$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')" \
    --string wall_time_utc "$(date -u -Is)" "$@"
}

emit_event --new-log --string event run_start \
  --json-value argv '["scripts/e2e/hygiene_no_mock_e2e.sh"]' \
  --string cwd "$ROOT" \
  --append-string claim_ids FLN-W4-MACRO-HYGIENE-PRODUCTION \
  --append-string invariant_ids FL-INV-01 \
  --append-string invariant_ids FL-INV-07 \
  --append-string gate_ids W4 \
  --string parity_ledger_row not_applicable_w4_production_slice \
  --string epoch "lean-$PIN_TAG" --string mode faithful \
  --string profile e2e --string platform "$(uname -srm)" \
  --integer thread_count 32 --string seed hygiene-path-v1 \
  --string cache_state "${FLN_E2E_CACHE_STATE:-uncontrolled}" \
  --string input_root "$INPUT_ROOT" --string subject_root "$SUBJECT_ROOT" \
  --string vendor_binding vendor-binding.json \
  --producer-binding-root "$ROOT" "${GOVERNED_ARGS[@]}" \
  --json-value host_facts "$HOST_FACTS_JSON" \
  --json-value budgets \
    "{\"capture_bytes_per_stream\":$CAPTURE_BYTES,\"output_budget_bytes\":$OUTPUT_BUDGET_BYTES,\"step_timeout_ms\":$TIMEOUT_MS,\"kill_grace_ms\":$GRACE_MS}"

run_step() {
  local step="$1"
  shift
  local metadata="$ART_DIR/$step.meta.json"
  local stdout="$ART_DIR/$step.out"
  local stderr="$ART_DIR/$step.err"
  local readiness="$ART_DIR/$step.ready.json"
  local validation="$ART_DIR/$step.validation.json"
  local wrapper_rc=0

  printf '[hygiene_no_mock_e2e] running %s\n' "$step" >&2
  setsid -- "${PYTHON[@]}" "$EVIDENCE" run --cwd "$ROOT" \
    --metadata "$metadata" --stdout "$stdout" --stderr "$stderr" \
    --readiness "$readiness" --artifact-root "$ART_DIR" \
    --capture-bytes "$CAPTURE_BYTES" \
    --output-budget-bytes "$OUTPUT_BUDGET_BYTES" \
    --timeout-ms "$TIMEOUT_MS" --grace-ms "$GRACE_MS" \
    --stage-id "$step" -- "$@" || wrapper_rc=$?
  "${PYTHON[@]}" "$EVIDENCE" validate-supervisor --file "$metadata" \
    --expected-stage-id "$step" --artifact-root "$ART_DIR" \
    --output "$validation" || {
      printf '[hygiene_no_mock_e2e] internal fault: invalid supervisor envelope for %s\n' \
        "$step" >&2
      exit 2
    }
  if [ "$wrapper_rc" -ne 0 ]; then
    printf '[hygiene_no_mock_e2e] refused: %s exited %s; logs=%s\n' \
      "$step" "$wrapper_rc" "$ART_DIR" >&2
    exit "$wrapper_rc"
  fi
  local current_root
  current_root="$(
    "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" \
      "${HASH_ARGS[@]}" --vendor-path "$VENDOR_PATH"
  )" || {
    printf '[hygiene_no_mock_e2e] internal fault: cannot hash %s final inputs\n' \
      "$step" >&2
    exit 2
  }
  if [ "$current_root" != "$INPUT_ROOT" ]; then
    printf '[hygiene_no_mock_e2e] inconclusive: governed inputs changed in %s\n' \
      "$step" >&2
    exit 3
  fi
  emit_event --string event step --string step_id "$step" \
    --string assertion pass --string expected exit_zero \
    --string actual pass --string input_root "$INPUT_ROOT" \
    --string final_state "$current_root" \
    --string validation_artifact "$step.validation.json" \
    --string expected_supervisor_classification pass \
    --integer expected_wrapper_exit 0 --integer expected_child_exit 0 \
    --string subject_root "$SUBJECT_ROOT" \
    --string subject_final_state "$SUBJECT_ROOT" \
    --json-file supervisor "$metadata"
}

cat > "$ART_DIR/reference_scope.lean" <<'LEAN'
import Lean

open Lean

def main : IO Unit := do
  let plain := `x
  let firstContext := `Main.command17._hygCtx
  let secondContext := `Imported.command4._hygCtx
  let first := addMacroScope firstContext plain 1
  let second := addMacroScope firstContext first 8
  let third := addMacroScope secondContext second 3
  IO.println third.toString
LEAN

cat > "$ART_DIR/validate_semantic.py" <<'PY'
import hashlib
import json
import pathlib
import re
import sys

artifact = pathlib.Path(sys.argv[1]).resolve()
run_id = sys.argv[2]
semantic_path = artifact / "semantic.ndjson"
telemetry_path = artifact / "telemetry.ndjson"
reference_path = artifact / "reference_scope_oracle.out"
version_path = artifact / "reference_version.out"

def load_rows(path):
    return [
        json.loads(line)
        for line in path.read_text(encoding="utf-8").splitlines()
        if line
    ]

def exact_keys(row, keys):
    if set(row) != set(keys):
        raise SystemExit(f"unexpected keys for {row.get('scenario', 'row')}")

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

rows = load_rows(semantic_path)
if len(rows) != 6:
    raise SystemExit("semantic row count is not six")
if [row.get("sequence") for row in rows] != list(range(6)):
    raise SystemExit("semantic sequence is not total and ordered")
if [row.get("scenario") for row in rows] != [
    "positive",
    "failure",
    "recovery",
    "cancellation",
    "resource",
    "thread_matrix",
]:
    raise SystemExit("semantic scenarios are incomplete or reordered")
if any(row.get("schema") != "fln.e2e.hygiene-semantic/1" for row in rows):
    raise SystemExit("semantic schema drift")

positive, failure, recovery, cancellation, resource, thread_matrix = rows
exact_keys(positive, {
    "schema", "sequence", "scenario", "status", "semantic_root",
    "scope_overlap", "generated_names", "output_nodes", "published",
})
exact_keys(failure, {
    "schema", "sequence", "scenario", "status", "diagnostic", "published",
})
exact_keys(recovery, {
    "schema", "sequence", "scenario", "status", "semantic_root", "published",
})
for row in (cancellation, resource):
    exact_keys(row, {
        "schema", "sequence", "scenario", "status", "published",
    })
exact_keys(thread_matrix, {
    "schema", "sequence", "scenario", "status", "thread_counts",
    "productive_expansions", "semantic_root", "published",
})

hex_digest = re.compile(r"[0-9a-f]{64}")
if positive["status"] != "accepted" or positive["published"] is not True:
    raise SystemExit("positive expansion was not published")
if positive["generated_names"] != 2 or positive["output_nodes"] != 7:
    raise SystemExit("positive anti-vacuity floor failed")
if not hex_digest.fullmatch(positive["semantic_root"]):
    raise SystemExit("positive semantic root is malformed")
if failure != {
    "schema": "fln.e2e.hygiene-semantic/1",
    "sequence": 1,
    "scenario": "failure",
    "status": "rejected",
    "diagnostic": "unexpected antiquotation splice",
    "published": False,
}:
    raise SystemExit("typed failure projection drift")
if recovery["status"] != "accepted" or recovery["published"] is not True:
    raise SystemExit("repair did not recover production expansion")
if not hex_digest.fullmatch(recovery["semantic_root"]):
    raise SystemExit("recovery semantic root is malformed")
for row in (cancellation, resource):
    if row["status"] != "inconclusive" or row["published"] is not False:
        raise SystemExit("Inconclusive outcome crossed publication boundary")
if thread_matrix["status"] != "accepted" or thread_matrix["published"] is not True:
    raise SystemExit("thread matrix did not publish")
if thread_matrix["thread_counts"] != [1, 8, 32]:
    raise SystemExit("thread matrix does not cover 1/8/32")
if thread_matrix["productive_expansions"] != 41:
    raise SystemExit("thread matrix was not productive")
if thread_matrix["semantic_root"] != positive["semantic_root"]:
    raise SystemExit("thread-count semantic roots diverged")

telemetry = load_rows(telemetry_path)
if len(telemetry) != 1:
    raise SystemExit("telemetry row count is not one")
exact_keys(telemetry[0], {
    "schema", "run_id", "thread_counts", "productive_expansions",
    "thread_root",
})
if telemetry[0] != {
    "schema": "fln.e2e.hygiene-telemetry/1",
    "run_id": run_id,
    "thread_counts": [1, 8, 32],
    "productive_expansions": 41,
    "thread_root": positive["semantic_root"],
}:
    raise SystemExit("telemetry binding drift")

expected_scope = (
    "x._@.Main.command17._hygCtx.1.8."
    "Imported.command4._hygCtx._hyg.3"
)
reference_scope = reference_path.read_text(encoding="utf-8").strip()
if reference_scope != expected_scope:
    raise SystemExit("pinned Reference scope oracle diverged")
if positive["scope_overlap"] != reference_scope:
    raise SystemExit("production scope overlap diverged from Reference")
if "version 4.32.0" not in version_path.read_text(encoding="utf-8"):
    raise SystemExit("Reference binary version is not the pinned epoch")

result = {
    "schema": "fln.e2e.hygiene-validation/1",
    "run_id": run_id,
    "scenarios": [row["scenario"] for row in rows],
    "semantic_root": positive["semantic_root"],
    "reference_scope": reference_scope,
    "semantic_sha256": digest(semantic_path),
    "telemetry_sha256": digest(telemetry_path),
    "reference_sha256": digest(reference_path),
}
print(json.dumps(result, sort_keys=True, separators=(",", ":")))
PY

run_step hygiene_targets \
  env FLN_HYGIENE_E2E_ART_DIR="$ART_DIR" \
    FLN_HYGIENE_E2E_RUN_ID="$RUN_ID" \
    CARGO_TARGET_DIR="$BUILD_TARGET" \
  cargo test --locked -q -p fln-parse \
    --test hygiene_scope_model \
    --test generated_name_property \
    --test quotation_roundtrip \
    --test macro_syntax_fuzz \
    --test hygiene_no_mock_e2e -- --nocapture

run_step internal_fault_nonpublication \
  env CARGO_TARGET_DIR="$BUILD_TARGET" \
  cargo test --locked -q -p fln-parse --lib \
    macro_expand::tests::a_source_map_drop_mutant_is_an_internal_fault_with_no_product \
    -- --exact --nocapture

run_step reference_version "$REFERENCE_LEAN" --version
run_step reference_scope_oracle "$REFERENCE_LEAN" --run \
  "$ART_DIR/reference_scope.lean"
run_step semantic_validation "${PYTHON[@]}" \
  "$ART_DIR/validate_semantic.py" "$ART_DIR" "$RUN_ID"

cp "$ART_DIR/semantic_validation.out" "$ART_DIR/semantic.validation.json"
SEMANTIC_ROOT="$(
  "${PYTHON[@]}" -c \
    'import json,sys; print(json.load(open(sys.argv[1],encoding="utf-8"))["semantic_root"])' \
    "$ART_DIR/semantic.validation.json"
)"
FINAL_ROOT="$(
  "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
    --vendor-path "$VENDOR_PATH"
)" || {
  printf '[hygiene_no_mock_e2e] internal fault: cannot hash final inputs\n' >&2
  exit 2
}
if [ "$FINAL_ROOT" != "$INPUT_ROOT" ]; then
  printf '[hygiene_no_mock_e2e] inconclusive: governed inputs changed during the run\n' >&2
  exit 3
fi

END_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
emit_event --string event run_end --string verdict pass \
  --string reason_code all_hygiene_obligations_satisfied \
  --integer process_exit 0 --string active_step semantic_validation \
  --integer duration_ns "$((END_NS - START_NS))" \
  --string cleanup_status retained_by_policy \
  --string final_state "$FINAL_ROOT" --string logical_root "$FINAL_ROOT" \
  --string receipt_root "$SEMANTIC_ROOT" --string first_divergence none \
  --string evidence_manifest manifest.json \
  --string bundle_commit bundle.complete.json \
  --string evidence_state pending_bundle_commit

"${PYTHON[@]}" "$EVIDENCE" validate-run --file "$LOG" \
  --schema "$SCHEMA" --expected-verdict pass --artifact-root "$ART_DIR" \
  --output "$ART_DIR/run.validation.json"
"${PYTHON[@]}" "$EVIDENCE" manifest --art-dir "$ART_DIR" \
  --output "$ART_DIR/manifest.json" \
  --digest-output "$ART_DIR/manifest.digest" \
  --run-id "$RUN_ID" --bead "$BEAD" --scenario "$SCENARIO" \
  --verdict pass --input-root "$INPUT_ROOT" --final-root "$FINAL_ROOT"
"${PYTHON[@]}" "$EVIDENCE" validate-manifest --art-dir "$ART_DIR" \
  --manifest "$ART_DIR/manifest.json" --digest "$ART_DIR/manifest.digest" \
  --offline
"${PYTHON[@]}" "$EVIDENCE" complete-bundle --art-dir "$ART_DIR" \
  --manifest "$ART_DIR/manifest.json" \
  --digest "$ART_DIR/manifest.digest" \
  --output "$ART_DIR/bundle.complete.json" \
  --governed-root "$ROOT" "${GOVERNED_ARGS[@]}" \
  --expected-root "$FINAL_ROOT" --vendor-path "$VENDOR_PATH"
"${PYTHON[@]}" "$EVIDENCE" adopt-bundle --art-dir "$ART_DIR" \
  --manifest "$ART_DIR/manifest.json" \
  --digest "$ART_DIR/manifest.digest" \
  --commit "$ART_DIR/bundle.complete.json" \
  --artifact-root "$ART_DIR" >/dev/null
"${PYTHON[@]}" "$EVIDENCE" validate-bundle --art-dir "$ART_DIR" \
  --manifest "$ART_DIR/manifest.json" \
  --digest "$ART_DIR/manifest.digest" \
  --commit "$ART_DIR/bundle.complete.json" \
  --artifact-root "$ART_DIR" >/dev/null

printf '[hygiene_no_mock_e2e] PASS evidence=%s semantic_root=%s\n' \
  "$ART_DIR" "$SEMANTIC_ROOT" >&2
