#!/usr/bin/env bash
# contract_drift.sh — shared E2E scenario for the extracted ABI/OLEAN contracts,
# CLI/Lake census, joined PublicSurface contract, and extern census (beads
# franken_lean-53v and fln-20ri, plan Appendix B/C).
#
# Real-path, no-mock: the checked-in extraction scripts re-run against the REAL
# pinned vendor tree (and, when the pinned Reference binary is installed, the
# real oracle environment walk), byte-compared against the checked-in artifacts;
# the consuming Rust suites run; then two REAL drift classes are seeded — a
# perturbed generated layout constant, and a rendered artifact desynchronized
# from its inventory root — and each must be KILLED by the named lane, followed
# by byte-verified restoration and a green recovery run. NDJSON under
# target/e2e/; artifacts retained.

# The legacy body below is deliberately retained as the one place that stages
# the three real mutants and the interrupted-publication recovery.  The outer
# invocation is the governed producer: it supervises that body, binds its raw
# per-stage attestations into the v2 record, and commits a complete bundle.
# Keeping the mutation code in this branch prevents a second implementation of
# the byte-identical restoration contract from drifting away from the one the
# scheduled lane actually executes.
if [[ "${FLN_CONTRACT_DRIFT_LEGACY:-0}" != 1 ]]; then
  set -Eeuo pipefail

  ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
  PYTHON_BIN="$(command -v python3 || true)"
  [ -n "$PYTHON_BIN" ] || {
    echo "[contract_drift] setup failure: python3 is required" >&2
    exit 2
  }
  PYTHON=("$PYTHON_BIN" -I -S)
  EVIDENCE="$ROOT/scripts/evidence.py"
  SCHEMA="fln.e2e/2"
  BEAD="franken_lean-smk0"
  SCENARIO="contract_drift"
  # The build gate, taken by this OUTER invocation rather than by whoever launched
  # it — bead franken_lean-gate-lock-producer-optional-o2vz. Same shape as
  # closure_audit.sh, indented to this branch: sits before the EXIT finalizer is
  # installed, so a contention `exit 3` writes no evidence. The LEGACY child body
  # (FLN_CONTRACT_DRIFT_LEGACY=1) deliberately takes nothing: it runs under this
  # supervisor while the gate is already held, and its supervised boundary closes
  # inherited descriptors. Not in INPUT_PATHS; SC1091 is disabled because the
  # library is checked directly by check.sh's shellcheck stage.
  # shellcheck source=scripts/lib/gate_lock.sh
  # shellcheck disable=SC1091
  . "$ROOT/scripts/lib/gate_lock.sh"
  fln_gate_acquire "$SCENARIO"
  RUN_ID="contract-drift-governed-$(date -u +%Y%m%dT%H%M%SZ)-$$"
  ART_ROOT="${FLN_E2E_ART_ROOT:-$ROOT/target/e2e}"
  ART_DIR="$ART_ROOT/$RUN_ID"
  LEGACY_RUN_ID="contract-drift-legacy-$RUN_ID"
  LEGACY_DIR="$ART_DIR/legacy"
  LEGACY_LOG="$LEGACY_DIR/$LEGACY_RUN_ID/run.ndjson"
  LOG="$ART_DIR/run.ndjson"
  VENDOR_PATH="vendor/lean4-src"
  VENDOR_BINDING="$ART_DIR/vendor-binding.json"
  CAPTURE_BYTES="${FLN_E2E_CAPTURE_BYTES:-524288}"
  OUTPUT_BUDGET_BYTES="${FLN_E2E_OUTPUT_BUDGET_BYTES:-67108864}"
  TIMEOUT_MS="${FLN_E2E_TIMEOUT_MS:-7200000}"
  GRACE_MS="${FLN_E2E_KILL_GRACE_MS:-5000}"
  START_NS="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"
  SEQ=0
  ACTIVE_STEP=setup
  FINAL_SET=0
  FINAL_VERDICT=internal_fault
  FINAL_REASON=uncommitted_exit
  FINAL_EXIT=2
  TERMINAL_EMITTED=0

  # These are every authoritative input the legacy child can inspect or
  # transiently mutate.  The final root is therefore an assertion that all
  # three source plants and the candidate-set recovery restored exactly the
  # input closure the run began with.
  INPUT_PATHS=(
    SUITE.lock ABI_CONTRACT.md OLEAN_CONTRACT.md
    contracts/PUBLIC_SURFACE_CONTRACT.txt contracts/PUBLIC_SURFACE_CONTRACT.md
    crates/fln-rt/src/abi.rs crates/fln-olean/src/format.rs
    crates/fln-conformance/src/public_surface_generated.rs
    scripts/e2e/contract_drift.sh scripts/evidence.py scripts/verify_vendor_tree.sh
    scripts/extract/gen_abi_contract.py scripts/extract/gen_olean_contract.py
    scripts/extract/gen_cli_lake_census.py scripts/extract/gen_extern_census.sh
    scripts/extract/gen_public_surface_contract.py
    crates/fln-conformance/tests/contract_roots.rs
    crates/fln-conformance/tests/public_surface.rs
    .github/workflows/contract-drift.yml
  )
  HASH_ARGS=()
  GOVERNED_ARGS=()
  for input_path in "${INPUT_PATHS[@]}"; do
    HASH_ARGS+=(--path "$input_path")
    GOVERNED_ARGS+=(--governed-path "$input_path")
  done
  INPUT_ROOT="$("${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" \
    "${HASH_ARGS[@]}" --vendor-path "$VENDOR_PATH")" || {
    echo "[contract_drift] setup failure: cannot hash governed inputs" >&2
    exit 2
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

  hash_governed() {
    "${PYTHON[@]}" "$EVIDENCE" hash-tree --root "$ROOT" "${HASH_ARGS[@]}" \
      --vendor-path "$VENDOR_PATH"
  }

  set_final() {
    FINAL_SET=1
    FINAL_VERDICT="$1"
    FINAL_REASON="$2"
    FINAL_EXIT="$3"
  }

  # shellcheck disable=SC2317 # invoked by the EXIT trap below
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
        --string logical_root "$final_root" --string receipt_root "$INPUT_ROOT" \
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
      printf '[contract_drift] INTERNAL FAULT: evidence bundle incomplete: %s\n' \
        "$ART_DIR" >&2
      exit 2
    fi
    if ! "${PYTHON[@]}" "$EVIDENCE" validate-bundle --art-dir "$ART_DIR" \
        --manifest "$ART_DIR/manifest.json" --digest "$ART_DIR/manifest.digest" \
        --commit "$ART_DIR/bundle.complete.json" --artifact-root "$ART_DIR" \
        >/dev/null; then
      printf '[contract_drift] INTERNAL FAULT: terminal bundle mutated: %s\n' \
        "$ART_DIR" >&2
      exit 2
    fi
    printf '[contract_drift] %s reason=%s evidence=%s\n' \
      "$FINAL_VERDICT" "$FINAL_REASON" "$ART_DIR" >&2
    exit "$FINAL_EXIT"
  }

  # shellcheck disable=SC2317 # invoked by signal traps below
  on_signal() {
    set_final cancelled "signal_$1" "$2"
    exit "$2"
  }

  trap 'on_signal HUP 129' HUP
  trap 'on_signal INT 130' INT
  trap 'on_signal TERM 143' TERM
  trap 'finalize "$?"' EXIT

  mkdir -p "$(dirname "$ART_DIR")"
  if ! mkdir "$ART_DIR" 2>/dev/null; then
    trap - EXIT
    echo "[contract_drift] evidence directory already claimed: $ART_DIR" >&2
    exit 2
  fi
  "${PYTHON[@]}" "$EVIDENCE" vendor-binding --root "$ROOT" \
    --vendor-path "$VENDOR_PATH" --output "$VENDOR_BINDING" --artifact-root "$ART_DIR"
  emit_event --new-log --string event run_start \
    --json-value argv '["scripts/e2e/contract_drift.sh"]' --string cwd "$ROOT" \
    --append-string claim_ids FLN-CONTRACT-DRIFT-REAL-PINNED-EXTRACTION \
    --append-string invariant_ids D5 --append-string invariant_ids D9 \
    --append-string invariant_ids FL-INV-01 --append-string invariant_ids FL-INV-07 \
    --append-string gate_ids W1 \
    --string parity_ledger_row not_applicable_contract_drift_extraction \
    --string epoch lean-v4.32.0 --string mode sound --string profile e2e \
    --string platform "$(uname -srm)" --integer thread_count 1 \
    --json-value host_facts "$("${PYTHON[@]}" -c 'import json,platform; print(json.dumps({"machine":platform.machine(),"python":platform.python_version(),"release":platform.release(),"system":platform.system()},sort_keys=True,separators=(",",":")))')" \
    --string seed "$LEGACY_RUN_ID" --string cache_state "${FLN_E2E_CACHE_STATE:-unspecified}" \
    --string input_root "$INPUT_ROOT" --string vendor_binding vendor-binding.json \
    --producer-binding-root "$ROOT" "${GOVERNED_ARGS[@]}" \
    --json-value budgets "{\"capture_bytes_per_stream\":$CAPTURE_BYTES,\"output_budget_bytes\":$OUTPUT_BUDGET_BYTES,\"step_timeout_ms\":$TIMEOUT_MS,\"kill_grace_ms\":$GRACE_MS}"

  ACTIVE_STEP=legacy_contract_drift
  META="$ART_DIR/legacy_contract_drift.meta.json"
  OUT="$ART_DIR/legacy_contract_drift.out"
  ERR="$ART_DIR/legacy_contract_drift.err"
  READY="$ART_DIR/legacy_contract_drift.ready.json"
  VALIDATION="$ART_DIR/legacy_contract_drift.validation.json"
  BEFORE="$(hash_governed)"
  set +e
  "${PYTHON[@]}" "$EVIDENCE" run --cwd "$ROOT" --metadata "$META" \
    --stdout "$OUT" --stderr "$ERR" --readiness "$READY" \
    --artifact-root "$ART_DIR" --capture-bytes "$CAPTURE_BYTES" \
    --output-budget-bytes "$OUTPUT_BUDGET_BYTES" --timeout-ms "$TIMEOUT_MS" \
    --grace-ms "$GRACE_MS" --stage-id legacy_contract_drift -- \
    env FLN_CONTRACT_DRIFT_LEGACY=1 FLN_E2E_LEGACY_ART_ROOT="$LEGACY_DIR" \
    FLN_E2E_RUN_ID="$LEGACY_RUN_ID" "$ROOT/scripts/e2e/contract_drift.sh"
  WRAPPER_RC=$?
  set -e
  "${PYTHON[@]}" "$EVIDENCE" validate-supervisor --file "$META" \
    --expected-stage-id legacy_contract_drift --artifact-root "$ART_DIR" \
    --output "$VALIDATION"
  AFTER="$(hash_governed)"

  legacy_status() {
    "${PYTHON[@]}" - "$LEGACY_LOG" "$1" <<'PY'
import json
import pathlib
import sys

for line in pathlib.Path(sys.argv[1]).read_text(encoding="utf-8").splitlines():
    record = json.loads(line)
    if record.get("step") == sys.argv[2]:
        print(record.get("status", "missing"))
        break
else:
    print("missing")
PY
  }

  read_meta() {
    "${PYTHON[@]}" - "$1" "$2" <<'PY'
import json
import pathlib
import sys

print(json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))[sys.argv[2]])
PY
  }

  ACTUAL_CLASS="$(read_meta "$META" classification)"
  ACTUAL_CHILD="$(read_meta "$META" child_exit)"
  STEP_IDS=(
    vendor_tree abi_drift olean_drift cli_lake_drift public_surface_drift
    census_drift suite mutant_a mutant_b mutant_c public_surface_recovery recovery
  )
  for STEP in "${STEP_IDS[@]}"; do
    ACTIVE_STEP="$STEP"
    STATUS=missing
    [ -f "$LEGACY_LOG" ] && STATUS="$(legacy_status "$STEP")"
    ASSERTION=pass
    EXPECTED="passed"
    ACCEPTED_STATUSES=passed
    if [ "$STEP" = census_drift ]; then
      EXPECTED="passed_or_typed_skip"
      ACCEPTED_STATUSES=passed,skipped
      [[ "$STATUS" = passed || "$STATUS" = skipped ]] || ASSERTION=fail
    elif [ "$STATUS" != passed ]; then
      ASSERTION=fail
    fi
    STEP_META="$ART_DIR/$STEP.meta.json"
    STEP_OUT="$ART_DIR/$STEP.out"
    STEP_ERR="$ART_DIR/$STEP.err"
    STEP_READY="$ART_DIR/$STEP.ready.json"
    STEP_VALIDATION="$ART_DIR/$STEP.validation.json"
    set +e
    "${PYTHON[@]}" "$EVIDENCE" run --cwd "$ROOT" --metadata "$STEP_META" \
      --stdout "$STEP_OUT" --stderr "$STEP_ERR" --readiness "$STEP_READY" \
      --artifact-root "$ART_DIR" --capture-bytes "$CAPTURE_BYTES" \
      --output-budget-bytes "$OUTPUT_BUDGET_BYTES" --timeout-ms "$TIMEOUT_MS" \
      --grace-ms "$GRACE_MS" --stage-id "$STEP" -- \
      "${PYTHON[@]}" -c 'import json,pathlib,sys
rows = [json.loads(line) for line in pathlib.Path(sys.argv[1]).read_text(encoding="utf-8").splitlines() if line]
matches = [row for row in rows if row.get("step") == sys.argv[2]]
accepted = set(sys.argv[3].split(","))
if len(matches) != 1 or matches[0].get("status") not in accepted:
    raise SystemExit(1)' "$LEGACY_LOG" "$STEP" "$ACCEPTED_STATUSES"
    STEP_WRAPPER_RC=$?
    set -e
    "${PYTHON[@]}" "$EVIDENCE" validate-supervisor --file "$STEP_META" \
      --expected-stage-id "$STEP" --artifact-root "$ART_DIR" \
      --output "$STEP_VALIDATION"
    STEP_CLASS="$(read_meta "$STEP_META" classification)"
    STEP_CHILD="$(read_meta "$STEP_META" child_exit)"
    if [ "$WRAPPER_RC" -ne 0 ] || [ "$ACTUAL_CLASS" != pass ] \
        || [ "$ACTUAL_CHILD" -ne 0 ] || [ "$BEFORE" != "$INPUT_ROOT" ] \
        || [ "$AFTER" != "$INPUT_ROOT" ] || [ "$STEP_WRAPPER_RC" -ne 0 ] \
        || [ "$STEP_CLASS" != pass ] || [ "$STEP_CHILD" -ne 0 ]; then
      ASSERTION=fail
    fi
    emit_event --string event step --string step_id "$STEP" \
      --string assertion "$ASSERTION" --string expected "$EXPECTED" \
      --string actual "legacy:$STATUS" --string input_root "$BEFORE" \
      --string final_state "$AFTER" \
      --string validation_artifact "$(basename "$STEP_VALIDATION")" \
      --string expected_supervisor_classification pass \
      --integer expected_wrapper_exit 0 --integer expected_child_exit 0 \
      --string subject_root "$BEFORE" --string subject_final_state "$AFTER" \
      --json-file supervisor "$STEP_META"
    if [ "$ASSERTION" != pass ]; then
      set_final fail "$STEP:legacy_attestation_failed" 1
      exit 1
    fi
  done
  set_final pass all_contract_drift_obligations_passed 0
  exit 0
fi

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
PYTHON_BIN="$(command -v python3 || true)"
[ -n "$PYTHON_BIN" ] || {
  echo "[contract_drift] setup failure: python3 is required" >&2
  exit 2
}
PYTHON=("$PYTHON_BIN" -I -S)
HOSTILE_PYTHON_CONFIGURATION=()
while IFS= read -r environment_name; do
  [[ "$environment_name" == PYTHON* ]] \
    && HOSTILE_PYTHON_CONFIGURATION+=("$environment_name")
done < <(compgen -e | LC_ALL=C sort)
if ((${#HOSTILE_PYTHON_CONFIGURATION[@]} > 0)); then
  printf '[contract_drift] setup failure: sealed_interpreter_hostile_environment names=%s\n' \
    "$(IFS=,; printf '%s' "${HOSTILE_PYTHON_CONFIGURATION[*]}")" >&2
  exit 2
fi
RUN_ID="${FLN_E2E_RUN_ID:-contract-drift-$(date -u +%Y%m%dT%H%M%SZ)-$$}"
ART_DIR="${FLN_E2E_LEGACY_ART_ROOT:-$ROOT/target/e2e}/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
mkdir -p "$(dirname "$ART_DIR")"
if ! mkdir "$ART_DIR" 2>/dev/null; then
  echo "[contract_drift] setup failure: evidence directory already claimed: $ART_DIR" >&2
  exit 2
fi

BEAD="franken_lean-53v"
SCHEMA="fln-e2e/1"
HOST="$(uname -sr)"
start_ns=$(date +%s%N)

emit() { # emit <step_id> <status> <detail-json-fragment>
  local now_ns
  now_ns=$(date +%s%N)
  printf '{"schema":"%s","run_id":"%s","bead":"%s","scenario":"contract_drift","step":"%s","status":"%s","elapsed_ms":%d,"host":"%s",%s}\n' \
    "$SCHEMA" "$RUN_ID" "$BEAD" "$1" "$2" $(( (now_ns - start_ns) / 1000000 )) "$HOST" "$3" >> "$LOG"
}

note() { echo "[contract_drift] $*" >&2; }

emit run_start started "\"cwd\":\"$ROOT\",\"argv\":\"$0\""

# ---- lane 0: the staged Reference tree is exactly the pinned Git tree ------------------
note "vendor tree binding check (SUITE.lock -> staged Reference Git tree)"
set +e
"$ROOT/scripts/verify_vendor_tree.sh" > "$ART_DIR/vendor_tree_check.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit vendor_tree failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"vendor_tree_check.log\""
  note "FAIL: staged Reference tree does not match the pin"
  exit 1
fi
emit vendor_tree passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"vendor_tree_check.log\""

# ---- lane 1: ABI extraction is drift-free against the pin ------------------------------
note "ABI contract drift check (lean.h -> inventory/MD/Rust)"
set +e
"${PYTHON[@]}" "$ROOT/scripts/extract/gen_abi_contract.py" --check > "$ART_DIR/abi_check.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit abi_drift failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"abi_check.log\""
  note "FAIL: ABI contract drifted from the pin"
  exit 1
fi
emit abi_drift passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"abi_check.log\""

# ---- lane 2: olean extraction is drift-free against the pin ----------------------------
note "OLEAN contract drift check (module.cpp/compact/Lean structures)"
set +e
"${PYTHON[@]}" "$ROOT/scripts/extract/gen_olean_contract.py" --check > "$ART_DIR/olean_check.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit olean_drift failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"olean_check.log\""
  note "FAIL: OLEAN contract drifted from the pin"
  exit 1
fi
emit olean_drift passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"olean_check.log\""

# ---- lane 3: CLI/Lake source census is drift-free against the pin ----------------------
note "CLI/Lake census source drift check (pinned sources -> inventory)"
set +e
"${PYTHON[@]}" "$ROOT/scripts/extract/gen_cli_lake_census.py" --check \
  > "$ART_DIR/cli_lake_check.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit cli_lake_drift failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"cli_lake_check.log\""
  note "FAIL: CLI/Lake census drifted from the pinned sources or policy"
  exit 1
fi
emit cli_lake_drift passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"cli_lake_check.log\""

# ---- lane 4: joined public-surface contract is drift-free ------------------------------
note "PublicSurface join drift check (option + CLI/Lake + LSP)"
set +e
"${PYTHON[@]}" "$ROOT/scripts/extract/gen_public_surface_contract.py" --check \
  > "$ART_DIR/public_surface_check.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit public_surface_drift failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"public_surface_check.log\""
  note "FAIL: joined PublicSurface contract drifted from its canonical domain inputs"
  exit 1
fi
emit public_surface_drift passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"public_surface_check.log\""

# ---- lane 5: extern census drift (requires the pinned Reference binary) ----------------
PIN_TAG="$(sed -E 's/.*tag=([^ ]+).*/\1/' <<<"$(grep -E '^reference ' "$ROOT/SUITE.lock")")"
if [ -x "$HOME/.elan/toolchains/leanprover--lean4---$PIN_TAG/bin/lean" ]; then
  note "extern census drift check (pin-verified environment walk)"
  set +e
  "$ROOT/scripts/extract/gen_extern_census.sh" --check > "$ART_DIR/census_check.log" 2>&1
  rc=$?
  set -e
  if [ "$rc" -ne 0 ]; then
    emit census_drift failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"census_check.log\""
    note "FAIL: extern census drifted from the pin"
    exit 1
  fi
  emit census_drift passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"census_check.log\""
else
  # Typed, honest skip: without the oracle binary this lane cannot run; the
  # checked-in census stays validated by lane 5's coherence tests only.
  emit census_drift skipped "\"reason\":\"reference_binary_absent\",\"limitation\":\"L0: census-vs-pin unverified on this host\""
  note "SKIP: pinned Reference binary not installed; census drift lane skipped (typed limitation)"
fi

# ---- lane 6: the consuming Rust suites -------------------------------------------------
note "running the contract consumer suites (fln-rt, fln-olean, conformance linkage)"
set +e
( cd "$ROOT" \
    && CARGO_TARGET_DIR=target_local cargo test -q -p fln-rt -p fln-olean \
    && CARGO_TARGET_DIR=target_local cargo test -q -p fln-conformance \
      --test contract_roots --test public_surface ) \
  > "$ART_DIR/suite.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit suite failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"suite.log\""
  note "FAIL: contract consumer suites failed (see $ART_DIR/suite.log)"
  exit 1
fi
emit suite passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"suite.log\""

# ---- lane 7: seeded mutation A — perturbed generated layout constant -------------------
ABI_RS="$ROOT/crates/fln-rt/src/abi.rs"
BACKUP="$ART_DIR/abi.rs.orig"
cp "$ABI_RS" "$BACKUP"
sha_before="$(sha256sum "$ABI_RS" | cut -d' ' -f1)"
note "seeding mutant A: TAG_CLOSURE perturbed in the generated Rust module"
if ! grep -q '^pub const TAG_CLOSURE: u8 = 245;$' "$ABI_RS"; then
  emit mutant_a failed "\"reason\":\"seed_anchor_missing\""
  note "FAIL: mutation seed anchor not found in abi.rs"
  exit 1
fi
"${PYTHON[@]}" - "$ABI_RS" <<'EOF'
import sys
path = sys.argv[1]
text = open(path).read()
open(path, "w").write(text.replace(
    "pub const TAG_CLOSURE: u8 = 245;",
    "pub const TAG_CLOSURE: u8 = 244;", 1))
EOF
set +e
"${PYTHON[@]}" "$ROOT/scripts/extract/gen_abi_contract.py" --check > "$ART_DIR/mutant_a_check.log" 2>&1
check_rc=$?
( cd "$ROOT" && CARGO_TARGET_DIR=target_local cargo test -q -p fln-rt --test abi_contract ) \
  > "$ART_DIR/mutant_a_suite.log" 2>&1
suite_rc=$?
set -e
cp "$BACKUP" "$ABI_RS"
sha_after="$(sha256sum "$ABI_RS" | cut -d' ' -f1)"
if [ "$sha_before" != "$sha_after" ]; then
  emit mutant_a failed "\"reason\":\"restore_failed\""
  note "FAIL: abi.rs not restored byte-identically"
  exit 1
fi
if [ "$check_rc" -eq 0 ] || [ "$suite_rc" -eq 0 ]; then
  emit mutant_a failed "\"check_exit\":$check_rc,\"suite_exit\":$suite_rc,\"expected\":\"both nonzero\",\"artifacts\":\"mutant_a_check.log,mutant_a_suite.log\""
  note "FAIL: mutant A survived (check=$check_rc suite=$suite_rc — a perturbed layout constant must be killed twice)"
  exit 1
fi
emit mutant_a passed "\"check_exit\":$check_rc,\"suite_exit\":$suite_rc,\"restored_sha\":\"$sha_after\",\"artifacts\":\"mutant_a_check.log,mutant_a_suite.log\""
note "mutant A killed by both the drift lane and the named tripwire test"

# ---- lane 8: seeded mutation B — rendered artifact desynced from inventory root --------
MD="$ROOT/ABI_CONTRACT.md"
BACKUP_MD="$ART_DIR/ABI_CONTRACT.md.orig"
cp "$MD" "$BACKUP_MD"
sha_before="$(sha256sum "$MD" | cut -d' ' -f1)"
note "seeding mutant B: ABI_CONTRACT.md inventory digest desynchronized"
"${PYTHON[@]}" - "$MD" <<'EOF'
import re, sys
path = sys.argv[1]
text = open(path).read()
new, n = re.subn(
    r"(> inventory: `contracts/abi_inventory\.json` sha256 `)([0-9a-f])",
    lambda m: m.group(1) + ("0" if m.group(2) != "0" else "1"),
    text, count=1)
if n != 1:
    raise SystemExit("seed anchor missing: inventory digest line")
open(path, "w").write(new)
EOF
set +e
( cd "$ROOT" && CARGO_TARGET_DIR=target_local cargo test -q -p fln-conformance --test contract_roots ) \
  > "$ART_DIR/mutant_b_suite.log" 2>&1
suite_rc=$?
set -e
cp "$BACKUP_MD" "$MD"
sha_after="$(sha256sum "$MD" | cut -d' ' -f1)"
if [ "$sha_before" != "$sha_after" ]; then
  emit mutant_b failed "\"reason\":\"restore_failed\""
  note "FAIL: ABI_CONTRACT.md not restored byte-identically"
  exit 1
fi
if [ "$suite_rc" -eq 0 ]; then
  emit mutant_b failed "\"suite_exit\":0,\"expected\":\"nonzero\",\"artifact\":\"mutant_b_suite.log\""
  note "FAIL: mutant B survived (a desynced rendered artifact must break the linkage test)"
  exit 1
fi
emit mutant_b passed "\"suite_exit\":$suite_rc,\"restored_sha\":\"$sha_after\",\"artifact\":\"mutant_b_suite.log\""
note "mutant B killed by the cross-artifact linkage test"

# ---- lane 9: seeded mutation C — perturbed generated OLEAN header size -----------------
OLEAN_RS="$ROOT/crates/fln-olean/src/format.rs"
BACKUP_OLEAN="$ART_DIR/format.rs.orig"
cp "$OLEAN_RS" "$BACKUP_OLEAN"
sha_before="$(sha256sum "$OLEAN_RS" | cut -d' ' -f1)"
note "seeding mutant C: OLEAN_HEADER_SIZE perturbed in the generated Rust module"
if ! grep -q '^pub const OLEAN_HEADER_SIZE: usize = 88;$' "$OLEAN_RS"; then
  emit mutant_c failed "\"reason\":\"seed_anchor_missing\""
  note "FAIL: mutation seed anchor not found in format.rs"
  exit 1
fi
"${PYTHON[@]}" - "$OLEAN_RS" <<'EOF'
import sys
path = sys.argv[1]
text = open(path).read()
open(path, "w").write(text.replace(
    "pub const OLEAN_HEADER_SIZE: usize = 88;",
    "pub const OLEAN_HEADER_SIZE: usize = 89;", 1))
EOF
set +e
"${PYTHON[@]}" "$ROOT/scripts/extract/gen_olean_contract.py" --check \
  > "$ART_DIR/mutant_c_check.log" 2>&1
check_rc=$?
set -e
cp "$BACKUP_OLEAN" "$OLEAN_RS"
sha_after="$(sha256sum "$OLEAN_RS" | cut -d' ' -f1)"
if [ "$sha_before" != "$sha_after" ]; then
  emit mutant_c failed "\"reason\":\"restore_failed\""
  note "FAIL: format.rs not restored byte-identically"
  exit 1
fi
if [ "$check_rc" -eq 0 ] \
    || ! grep -Fq 'gen_olean_contract: DRIFT: crates/fln-olean/src/format.rs:20' \
      "$ART_DIR/mutant_c_check.log" \
    || ! grep -Fq "checked-in: 'pub const OLEAN_HEADER_SIZE: usize = 89;'" \
      "$ART_DIR/mutant_c_check.log" \
    || ! grep -Fq "regenerated: 'pub const OLEAN_HEADER_SIZE: usize = 88;'" \
      "$ART_DIR/mutant_c_check.log"; then
  emit mutant_c failed "\"check_exit\":$check_rc,\"expected\":\"nonzero discriminator naming format.rs:20 and values 88/89\",\"artifact\":\"mutant_c_check.log\""
  note "FAIL: mutant C was not killed by the exact OLEAN drift discriminator"
  exit 1
fi
emit mutant_c passed "\"check_exit\":$check_rc,\"restored_sha\":\"$sha_after\",\"artifact\":\"mutant_c_check.log\""
note "mutant C killed by the exact OLEAN drift discriminator"

# ---- lane 10: interrupted PublicSurface publication recovers atomically ----------------
PUBLIC_CONTRACT="$ROOT/contracts/PUBLIC_SURFACE_CONTRACT.txt"
PUBLIC_DOCUMENT="$ROOT/contracts/PUBLIC_SURFACE_CONTRACT.md"
PUBLIC_RUST="$ROOT/crates/fln-conformance/src/public_surface_generated.rs"
PUBLIC_CONTRACT_CANDIDATE="$PUBLIC_CONTRACT.candidate"
PUBLIC_DOCUMENT_CANDIDATE="$PUBLIC_DOCUMENT.candidate"
PUBLIC_RUST_CANDIDATE="$PUBLIC_RUST.candidate"
for candidate in \
  "$PUBLIC_CONTRACT_CANDIDATE" \
  "$PUBLIC_DOCUMENT_CANDIDATE" \
  "$PUBLIC_RUST_CANDIDATE"; do
  if [ -e "$candidate" ]; then
    emit public_surface_recovery failed "\"reason\":\"preexisting_candidate\",\"path\":\"$candidate\""
    note "FAIL: PublicSurface recovery drill found a pre-existing candidate"
    exit 1
  fi
done
public_sha_before="$(
  sha256sum "$PUBLIC_CONTRACT" "$PUBLIC_DOCUMENT" "$PUBLIC_RUST" \
    | sha256sum | cut -d' ' -f1
)"
cp "$PUBLIC_CONTRACT" "$PUBLIC_CONTRACT_CANDIDATE"
cp "$PUBLIC_DOCUMENT" "$PUBLIC_DOCUMENT_CANDIDATE"
cp "$PUBLIC_RUST" "$PUBLIC_RUST_CANDIDATE"
set +e
"${PYTHON[@]}" "$ROOT/scripts/extract/gen_public_surface_contract.py" --check \
  > "$ART_DIR/public_surface_interrupted_check.log" 2>&1
check_rc=$?
"${PYTHON[@]}" "$ROOT/scripts/extract/gen_public_surface_contract.py" --recover \
  > "$ART_DIR/public_surface_recover.log" 2>&1
recover_rc=$?
"${PYTHON[@]}" "$ROOT/scripts/extract/gen_public_surface_contract.py" --check \
  > "$ART_DIR/public_surface_recovered_check.log" 2>&1
recovered_check_rc=$?
set -e
public_sha_after="$(
  sha256sum "$PUBLIC_CONTRACT" "$PUBLIC_DOCUMENT" "$PUBLIC_RUST" \
    | sha256sum | cut -d' ' -f1
)"
if [ "$check_rc" -eq 0 ] \
    || [ "$recover_rc" -ne 0 ] \
    || [ "$recovered_check_rc" -ne 0 ] \
    || [ "$public_sha_before" != "$public_sha_after" ] \
    || [ -e "$PUBLIC_CONTRACT_CANDIDATE" ] \
    || [ -e "$PUBLIC_DOCUMENT_CANDIDATE" ] \
    || [ -e "$PUBLIC_RUST_CANDIDATE" ]; then
  for candidate in \
    "$PUBLIC_CONTRACT_CANDIDATE" \
    "$PUBLIC_DOCUMENT_CANDIDATE" \
    "$PUBLIC_RUST_CANDIDATE"; do
    if [ -e "$candidate" ]; then
      mv "$candidate" "$ART_DIR/$(basename "$candidate").retained"
    fi
  done
  emit public_surface_recovery failed "\"interrupted_check_exit\":$check_rc,\"recover_exit\":$recover_rc,\"recovered_check_exit\":$recovered_check_rc,\"before\":\"$public_sha_before\",\"after\":\"$public_sha_after\",\"artifacts\":\"public_surface_interrupted_check.log,public_surface_recover.log,public_surface_recovered_check.log\""
  note "FAIL: PublicSurface interrupted publication did not recover byte-identically"
  exit 1
fi
emit public_surface_recovery passed "\"interrupted_check_exit\":$check_rc,\"recover_exit\":0,\"recovered_check_exit\":0,\"restored_sha\":\"$public_sha_after\",\"artifacts\":\"public_surface_interrupted_check.log,public_surface_recover.log,public_surface_recovered_check.log\""
note "PublicSurface interrupted candidate set recovered before canonical authority"

# ---- lane 11: recovery — everything green again after restoration ----------------------
note "recovery: drift checks and linkage green after restoration"
set +e
"${PYTHON[@]}" "$ROOT/scripts/extract/gen_abi_contract.py" --check > "$ART_DIR/recovery_abi.log" 2>&1
rc1=$?
"${PYTHON[@]}" "$ROOT/scripts/extract/gen_olean_contract.py" --check > "$ART_DIR/recovery_olean.log" 2>&1
rc2=$?
"${PYTHON[@]}" "$ROOT/scripts/extract/gen_cli_lake_census.py" --check \
  > "$ART_DIR/recovery_cli_lake.log" 2>&1
rc3=$?
"${PYTHON[@]}" "$ROOT/scripts/extract/gen_public_surface_contract.py" --check \
  > "$ART_DIR/recovery_public_surface.log" 2>&1
rc4=$?
( cd "$ROOT" \
    && CARGO_TARGET_DIR=target_local cargo test -q -p fln-rt --test abi_contract \
    && CARGO_TARGET_DIR=target_local cargo test -q -p fln-conformance \
      --test contract_roots --test public_surface ) \
  > "$ART_DIR/recovery_suite.log" 2>&1
rc5=$?
set -e
if [ "$rc1" -ne 0 ] \
    || [ "$rc2" -ne 0 ] \
    || [ "$rc3" -ne 0 ] \
    || [ "$rc4" -ne 0 ] \
    || [ "$rc5" -ne 0 ]; then
  emit recovery failed "\"abi_check_exit\":$rc1,\"olean_check_exit\":$rc2,\"cli_lake_check_exit\":$rc3,\"public_surface_check_exit\":$rc4,\"suite_exit\":$rc5,\"artifacts\":\"recovery_abi.log,recovery_olean.log,recovery_cli_lake.log,recovery_public_surface.log,recovery_suite.log\""
  note "FAIL: recovery lane not green (abi_check=$rc1 olean_check=$rc2 cli_lake_check=$rc3 public_surface_check=$rc4 suite=$rc5)"
  exit 1
fi
emit recovery passed "\"abi_check_exit\":0,\"olean_check_exit\":0,\"cli_lake_check_exit\":0,\"public_surface_check_exit\":0,\"suite_exit\":0,\"artifacts\":\"recovery_abi.log,recovery_olean.log,recovery_cli_lake.log,recovery_public_surface.log,recovery_suite.log\""

emit run_end passed "\"cleanup_status\":\"retained_by_policy\",\"artifact_dir\":\"target/e2e/$RUN_ID\""
note "PASS: all lanes green (artifacts in target/e2e/$RUN_ID)"
