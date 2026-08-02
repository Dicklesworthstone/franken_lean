#!/usr/bin/env bash
# bignum_vectors.sh — shared E2E scenario for the fln-bignum arithmetic core
# (beads franken_lean-npl / fln-msou).
#
# Real-path, no-mock: the golden corpus is drift-checked against its generator
# (CPython ground truth, Lean Nat semantics), the real suite runs (5 725 vectors +
# models), the C4 stage0 gauntlet runs the same arithmetic-heavy C probe against
# Marrow and the pinned Reference runtime, then nine named arithmetic/ABI-view
# defects are seeded one at a time in an isolated overlay. Each cell must fail
# through its registered discriminating test (a compile failure is not a kill)
# before one pristine recovery. The fln-msou profile/source/threshold joins and
# schoolbook/Karatsuba/Toom boundary equivalence run inside the real suite.
# The default entry point wraps the real lane in a producer-bound fln.e2e/2
# bundle. `FLN_BIGNUM_INNER=1` is private recursion used only by that wrapper:
# its legacy stream is retained as bounded telemetry, while canonical arithmetic
# facts are projected into a separately validated semantic stream.

set -Eeuo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
PYTHON_BIN="$(command -v python3 || true)"
[ -n "$PYTHON_BIN" ] || {
  echo "[bignum_vectors] setup failure: python3 is required" >&2
  exit 2
}
PYTHON=("$PYTHON_BIN" -I -S)
HOSTILE_PYTHON_CONFIGURATION=()
while IFS= read -r environment_name; do
  [[ "$environment_name" == PYTHON* ]] \
    && HOSTILE_PYTHON_CONFIGURATION+=("$environment_name")
done < <(compgen -e | LC_ALL=C sort)
if ((${#HOSTILE_PYTHON_CONFIGURATION[@]} > 0)); then
  printf '[bignum_vectors] setup failure: sealed_interpreter_hostile_environment names=%s\n' \
    "$(IFS=,; printf '%s' "${HOSTILE_PYTHON_CONFIGURATION[*]}")" >&2
  exit 2
fi

run_outer() {
  for required_command in bash cargo git setsid sha256sum; do
    command -v "$required_command" >/dev/null 2>&1 || {
      printf '[bignum_vectors] setup failure: %s is required\n' \
        "$required_command" >&2
      exit 2
    }
  done

  local evidence="$ROOT/scripts/evidence.py"
  local schema="fln.e2e/2"
  local semantic_schema="fln.e2e.bignum-semantic/1"
  local telemetry_schema="fln.e2e.bignum-telemetry/1"
  local bead="${FLN_BIGNUM_BEAD:-franken_lean-npl}"
  local scenario="bignum_vectors"
  local run_id
  run_id="bignum-no-mock-$(date -u +%Y%m%dT%H%M%SZ)-$$"
  local art_root="${FLN_E2E_ART_ROOT:-$ROOT/target/e2e}"
  local art_dir="$art_root/$run_id"
  local log="$art_dir/run.ndjson"
  local semantic="$art_dir/semantic.ndjson"
  local telemetry="$art_dir/telemetry.ndjson"
  local inner_root="$art_dir/inner"
  local vendor_path="vendor/lean4-src"
  local vendor_binding="$art_dir/vendor-binding.json"
  local build_target="${FLN_E2E_CARGO_TARGET_DIR:-${CARGO_TARGET_DIR:-$ROOT/target_local}}"
  local capture_bytes="${FLN_E2E_CAPTURE_BYTES:-1048576}"
  local output_budget_bytes="${FLN_E2E_OUTPUT_BUDGET_BYTES:-16777216}"
  local timeout_ms="${FLN_E2E_TIMEOUT_MS:-900000}"
  local grace_ms="${FLN_E2E_KILL_GRACE_MS:-2000}"
  local start_ns
  local seq=0
  local input_root
  local subject_root
  local inner_dir
  local final_root
  local semantic_root
  local end_ns
  local -a hash_args=()
  local -a governed_args=()
  local -a subject_hash_args=()
  local -a inner_candidates=()
  local -a input_paths=(
    Cargo.toml
    Cargo.lock
    SUITE.lock
    rust-toolchain.toml
    ci/VERIFICATION_MANIFEST.jsonl
    ci/ABI_EXPORT_STATUS.txt
    crates/fln-core
    crates/fln-bignum
    crates/fln-rt
    crates/fln-unsafe-abi
    crates/fln-kernel/tests/k1_judgments.rs
    tribunal/fixtures/c4
    scripts/e2e/bignum_vectors.sh
    scripts/e2e/marrow_stage0_gauntlet.sh
    scripts/evidence.py
    scripts/extract/gen_bignum_vectors.py
    scripts/lib/gate_lock.sh
    vendor/NOTICE
  )
  local -a subject_paths=(
    crates/fln-bignum/fixtures/kernel_reduction_profile.tsv
    crates/fln-bignum/fixtures/nat_vectors.txt
    crates/fln-bignum/src
    crates/fln-bignum/tests
    crates/fln-unsafe-abi/src
  )

  for input_path in "${input_paths[@]}"; do
    hash_args+=(--path "$input_path")
    governed_args+=(--governed-path "$input_path")
  done
  for subject_path in "${subject_paths[@]}"; do
    subject_hash_args+=(--path "$subject_path")
  done

  # shellcheck source=scripts/lib/gate_lock.sh
  # shellcheck disable=SC1091
  . "$ROOT/scripts/lib/gate_lock.sh"
  trap 'fln_gate_release_note "bignum_vectors"' EXIT
  fln_gate_acquire "$scenario"

  mkdir -p "$art_root"
  if ! mkdir "$art_dir" 2>/dev/null; then
    printf '[bignum_vectors] setup failure: artifact path is not fresh: %s\n' \
      "$art_dir" >&2
    exit 2
  fi
  mkdir "$inner_root"

  "${PYTHON[@]}" "$evidence" vendor-binding --root "$ROOT" \
    --vendor-path "$vendor_path" --output "$vendor_binding" \
    --artifact-root "$art_dir" || {
      printf '[bignum_vectors] setup failure: cannot bind vendored Reference\n' >&2
      exit 2
    }
  input_root="$(
    "${PYTHON[@]}" "$evidence" hash-tree --root "$ROOT" \
      "${hash_args[@]}" --vendor-path "$vendor_path"
  )" || {
    printf '[bignum_vectors] setup failure: cannot hash governed inputs\n' >&2
    exit 2
  }
  subject_root="$(
    "${PYTHON[@]}" "$evidence" hash-tree --root "$ROOT" \
      "${subject_hash_args[@]}"
  )" || {
    printf '[bignum_vectors] setup failure: cannot hash subject inputs\n' >&2
    exit 2
  }
  start_ns="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"

  emit_event() {
    local sequence="$seq"
    seq=$((seq + 1))
    "${PYTHON[@]}" "$evidence" emit --file "$log" \
      --artifact-root "$art_dir" \
      --string schema "$schema" --string run_id "$run_id" \
      --string bead "$bead" --string scenario "$scenario" \
      --integer sequence "$sequence" \
      --integer monotonic_ns "$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')" \
      --string wall_time_utc "$(date -u -Is)" "$@"
  }

  emit_event --new-log --string event run_start \
    --json-value argv '["scripts/e2e/bignum_vectors.sh"]' \
    --string cwd "$ROOT" \
    --append-string claim_ids FLN-NPL-OWNED-BIGNUM-KERNEL-GRADE \
    --append-string claim_ids FLN-MSOU-SUBQUADRATIC-BIGNUM-ALGORITHMS \
    --append-string invariant_ids FL-INV-07 \
    --append-string gate_ids W3 --append-string gate_ids PG-K \
    --string parity_ledger_row not_applicable_bignum_component_bounded_model \
    --string epoch v4.32.0 --string mode sound \
    --string profile e2e --string platform "$(uname -srm)" \
    --integer thread_count 1 --string seed bignum-vectors-v1 \
    --string cache_state "${FLN_E2E_CACHE_STATE:-uncontrolled}" \
    --string input_root "$input_root" --string subject_root "$subject_root" \
    --string vendor_binding vendor-binding.json \
    --producer-binding-root "$ROOT" "${governed_args[@]}" \
    --json-value host_facts "$(
      "${PYTHON[@]}" -c \
        'import json,platform; print(json.dumps({"machine":platform.machine(),"python":platform.python_version(),"release":platform.release(),"system":platform.system()},sort_keys=True,separators=(",",":")))'
    )" \
    --json-value budgets \
      "{\"capture_bytes_per_stream\":$capture_bytes,\"output_budget_bytes\":$output_budget_bytes,\"step_timeout_ms\":$timeout_ms,\"kill_grace_ms\":$grace_ms}"

  check_input_root() {
    local step="$1"
    local current_root
    current_root="$(
      "${PYTHON[@]}" "$evidence" hash-tree --root "$ROOT" \
        "${hash_args[@]}" --vendor-path "$vendor_path"
    )" || {
      printf '[bignum_vectors] internal fault: cannot hash %s final inputs\n' \
        "$step" >&2
      exit 2
    }
    if [ "$current_root" != "$input_root" ]; then
      printf '[bignum_vectors] inconclusive: governed inputs changed in %s\n' \
        "$step" >&2
      exit 3
    fi
  }

  run_step() {
    local step="$1"
    shift
    local metadata="$art_dir/$step.meta.json"
    local stdout="$art_dir/$step.out"
    local stderr="$art_dir/$step.err"
    local readiness="$art_dir/$step.ready.json"
    local validation="$art_dir/$step.validation.json"
    local wrapper_rc=0

    printf '[bignum_vectors] running %s\n' "$step" >&2
    setsid -- "${PYTHON[@]}" "$evidence" run --cwd "$ROOT" \
      --metadata "$metadata" --stdout "$stdout" --stderr "$stderr" \
      --readiness "$readiness" --artifact-root "$art_dir" \
      --capture-bytes "$capture_bytes" \
      --output-budget-bytes "$output_budget_bytes" \
      --timeout-ms "$timeout_ms" --grace-ms "$grace_ms" \
      --stage-id "$step" -- "$@" || wrapper_rc=$?
    "${PYTHON[@]}" "$evidence" validate-supervisor --file "$metadata" \
      --expected-stage-id "$step" --artifact-root "$art_dir" \
      --output "$validation" || {
        printf '[bignum_vectors] internal fault: invalid supervisor envelope for %s\n' \
          "$step" >&2
        exit 2
      }
    if [ "$wrapper_rc" -ne 0 ]; then
      printf '[bignum_vectors] refused: %s exited %s; logs=%s\n' \
        "$step" "$wrapper_rc" "$art_dir" >&2
      exit "$wrapper_rc"
    fi
    check_input_root "$step"
    emit_event --string event step --string step_id "$step" \
      --string assertion pass --string expected exit_zero \
      --string actual pass --string input_root "$input_root" \
      --string final_state "$input_root" \
      --string validation_artifact "$step.validation.json" \
      --string expected_supervisor_classification pass \
      --integer expected_wrapper_exit 0 --integer expected_child_exit 0 \
      --string subject_root "$subject_root" \
      --string subject_final_state "$subject_root" \
      --json-file supervisor "$metadata"
  }

  run_step bignum_lane env \
    FLN_BIGNUM_INNER=1 \
    FLN_BIGNUM_INNER_ART_ROOT="$inner_root" \
    FLN_E2E_CARGO_TARGET_DIR="$build_target" \
    bash scripts/e2e/bignum_vectors.sh

  mapfile -d '' -t inner_candidates < <(
    find "$inner_root" -mindepth 1 -maxdepth 1 -type d -print0
  )
  if ((${#inner_candidates[@]} != 1)); then
    printf '[bignum_vectors] internal fault: inner lane published %d roots\n' \
      "${#inner_candidates[@]}" >&2
    exit 2
  fi
  inner_dir="${inner_candidates[0]}"

  "${PYTHON[@]}" - \
    "$inner_dir" "$semantic" "$telemetry" "$run_id" \
    "$semantic_schema" "$telemetry_schema" <<'PY'
import hashlib
import json
import pathlib
import sys

inner = pathlib.Path(sys.argv[1])
semantic_path = pathlib.Path(sys.argv[2])
telemetry_path = pathlib.Path(sys.argv[3])
run_id, semantic_schema, telemetry_schema = sys.argv[4:]

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def records(path):
    return [
        json.loads(line)
        for line in path.read_text(encoding="utf-8").splitlines()
        if line
    ]

inner_records = records(inner / "run.ndjson")
by_step = {row["step"]: row for row in inner_records}
mutations = [
    ("carry_drop", "nat::tests::u128_model_agreement"),
    ("borrow_drop", "truncated_subtraction_saturates_at_zero_and_never_wraps"),
    ("normalization_single_pop", "nat::tests::edge_laws"),
    (
        "division_zero_guard_drop",
        "nat::tests::knuth_d_matches_the_bitwise_model_and_reconstructs_the_dividend",
    ),
    (
        "threshold_off_by_one",
        "nat::tests::multiplication_crossovers_are_pinned_and_both_sides_are_equivalent",
    ),
    (
        "signed_product_flip",
        "nat::tests::toom3_signed_evaluations_and_carry_chains_match_schoolbook",
    ),
    (
        "abi_view_origin_shift",
        "borrowed_limb_views_alias_storage_and_match_owned_arithmetic",
    ),
    ("decimal_validation_drop", "nat::tests::edge_laws"),
    ("shift_limb_boundary", "nat::tests::edge_laws"),
]
fixture = inner / "vector-fixture.txt"
vector_count = sum(
    1
    for line in fixture.read_text(encoding="utf-8").splitlines()
    if "|" in line and not line.startswith("#")
)
profile_rows = [
    line.split("\t")
    for line in (inner / "profile.snapshot.tsv")
    .read_text(encoding="utf-8")
    .splitlines()
    if line.startswith("source\t")
]
projections = [
    {"kind": row[4], "sha256": row[3]}
    for row in profile_rows
]
c4_facts = inner / "c4-facts-marrow.ndjson"
facts_digest = digest(c4_facts)
semantic = [
    {
        "fixture_sha256": digest(fixture),
        "scenario": "vector_corpus",
        "schema": semantic_schema,
        "sequence": 0,
        "status": "matched",
        "vectors": vector_count,
    },
    {
        "projections": projections,
        "scenario": "profile_binding",
        "schema": semantic_schema,
        "sequence": 1,
        "sources": len(profile_rows),
        "status": "matched",
    },
    {
        "packages": ["fln-bignum", "fln-rt", "fln-unsafe-abi"],
        "scenario": "consumer_suites",
        "schema": semantic_schema,
        "sequence": 2,
        "status": "passed",
    },
    {
        "fact_sha256": facts_digest,
        "nat_facts": sum(
            1
            for line in c4_facts.read_text(encoding="utf-8").splitlines()
            if '"probe":"nat.' in line
        ),
        "scenario": "c4_differential",
        "schema": semantic_schema,
        "sequence": 3,
        "status": "matched",
    },
]
for mutation, test in mutations:
    semantic.append(
        {
            "mutation": mutation,
            "published": False,
            "scenario": "mutation",
            "schema": semantic_schema,
            "sequence": len(semantic),
            "status": "killed",
            "test": test,
        }
    )
semantic.append(
    {
        "matches_positive": True,
        "scenario": "recovery",
        "schema": semantic_schema,
        "sequence": len(semantic),
        "status": "passed",
    }
)
semantic_bytes = b"".join(
    (
        json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n"
    ).encode()
    for row in semantic
)
semantic_path.write_bytes(semantic_bytes)
telemetry = {
    "elapsed_ms_by_step": {
        row["step"]: row["elapsed_ms"]
        for row in inner_records
        if "elapsed_ms" in row
    },
    "full_source_drifts": by_step["profile_binding"]["full_source_drifts"],
    "host": by_step["run_start"]["host"],
    "inner_run_id": by_step["run_start"]["run_id"],
    "inner_run_sha256": digest(inner / "run.ndjson"),
    "mutation_process_exits": {
        mutation: by_step[f"mutant_{mutation}"]["actual_exit"]
        for mutation, _test in mutations
    },
    "run_id": run_id,
    "schema": telemetry_schema,
    "semantic_sha256": hashlib.sha256(semantic_bytes).hexdigest(),
}
telemetry_path.write_text(
    json.dumps(telemetry, sort_keys=True, separators=(",", ":")) + "\n",
    encoding="utf-8",
)
PY

  run_step semantic_validation \
    "${PYTHON[@]}" "$evidence" validate-bignum-no-mock \
      --expected-run-id "$run_id" \
      --semantic "$semantic" --telemetry "$telemetry" \
      --inner-log "$inner_dir/run.ndjson" \
      --inner-root "$inner_dir" \
      --lane-metadata "$art_dir/bignum_lane.meta.json" \
      --artifact-root "$art_dir" \
      --output "$art_dir/semantic.validation.json"

  run_step final_real_recheck env CARGO_TARGET_DIR="$build_target" \
    cargo test --locked -q -p fln-bignum -p fln-unsafe-abi -p fln-rt

  final_root="$(
    "${PYTHON[@]}" "$evidence" hash-tree --root "$ROOT" \
      "${hash_args[@]}" --vendor-path "$vendor_path"
  )" || {
    printf '[bignum_vectors] internal fault: cannot hash final inputs\n' >&2
    exit 2
  }
  if [ "$final_root" != "$input_root" ]; then
    printf '[bignum_vectors] inconclusive: governed inputs changed\n' >&2
    exit 3
  fi
  semantic_root="$(
    "${PYTHON[@]}" -c \
      'import json,sys; print(json.load(open(sys.argv[1],encoding="utf-8"))["semantic_sha256"])' \
      "$art_dir/semantic.validation.json"
  )"
  end_ns="$("${PYTHON[@]}" -c 'import time; print(time.monotonic_ns())')"

  emit_event --string event run_end --string verdict pass \
    --string reason_code bignum_vectors_mutants_refused_and_recovered \
    --integer process_exit 0 --string active_step final_real_recheck \
    --integer duration_ns "$((end_ns - start_ns))" \
    --string cleanup_status retained_by_policy \
    --string final_state "$final_root" --string logical_root "$final_root" \
    --string receipt_root "$semantic_root" --string first_divergence none \
    --string evidence_manifest manifest.json \
    --string bundle_commit bundle.complete.json \
    --string evidence_state pending_bundle_commit

  "${PYTHON[@]}" "$evidence" validate-run --file "$log" \
    --schema "$schema" --expected-verdict pass --artifact-root "$art_dir" \
    --output "$art_dir/run.validation.json"
  "${PYTHON[@]}" "$evidence" manifest --art-dir "$art_dir" \
    --output "$art_dir/manifest.json" \
    --digest-output "$art_dir/manifest.digest" \
    --run-id "$run_id" --bead "$bead" --scenario "$scenario" \
    --verdict pass --input-root "$input_root" --final-root "$final_root"
  "${PYTHON[@]}" "$evidence" validate-manifest --art-dir "$art_dir" \
    --manifest "$art_dir/manifest.json" --digest "$art_dir/manifest.digest" \
    --offline
  "${PYTHON[@]}" "$evidence" complete-bundle --art-dir "$art_dir" \
    --manifest "$art_dir/manifest.json" \
    --digest "$art_dir/manifest.digest" \
    --output "$art_dir/bundle.complete.json" \
    --governed-root "$ROOT" "${governed_args[@]}" \
    --expected-root "$final_root" --vendor-path "$vendor_path"
  "${PYTHON[@]}" "$evidence" adopt-bundle --art-dir "$art_dir" \
    --manifest "$art_dir/manifest.json" \
    --digest "$art_dir/manifest.digest" \
    --commit "$art_dir/bundle.complete.json" \
    --artifact-root "$art_dir" >/dev/null
  "${PYTHON[@]}" "$evidence" validate-bundle --art-dir "$art_dir" \
    --manifest "$art_dir/manifest.json" \
    --digest "$art_dir/manifest.digest" \
    --commit "$art_dir/bundle.complete.json" \
    --artifact-root "$art_dir" >/dev/null

  printf '[bignum_vectors] PASS evidence=%s semantic_root=%s\n' \
    "$art_dir" "$semantic_root" >&2
}

if [ "${FLN_BIGNUM_INNER:-0}" != "1" ]; then
  run_outer "$@"
  exit 0
fi

RUN_ID="bignum-vectors-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_ROOT="${FLN_BIGNUM_INNER_ART_ROOT:-$ROOT/target/e2e}"
ART_DIR="$ART_ROOT/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
BUILD_TARGET="${FLN_E2E_CARGO_TARGET_DIR:-$ROOT/target_local}"
mkdir -p "$(dirname "$ART_DIR")"
if ! mkdir "$ART_DIR" 2>/dev/null; then
  echo "[bignum_vectors] setup failure: evidence directory already claimed: $ART_DIR" >&2
  exit 2
fi

BEAD="${FLN_BIGNUM_BEAD:-franken_lean-npl}"
SCHEMA="fln-e2e/1"
HOST="$(uname -sr)"
start_ns=$(date +%s%N)

emit() { # emit <step_id> <status> <detail-json-fragment>
  local now_ns
  now_ns=$(date +%s%N)
  printf '{"schema":"%s","run_id":"%s","bead":"%s","scenario":"bignum_vectors","step":"%s","status":"%s","elapsed_ms":%d,"host":"%s",%s}\n' \
    "$SCHEMA" "$RUN_ID" "$BEAD" "$1" "$2" $(( (now_ns - start_ns) / 1000000 )) "$HOST" "$3" >> "$LOG"
}

note() { echo "[bignum_vectors] $*" >&2; }

emit run_start started "\"cwd\":\"$ROOT\",\"argv\":\"$0\""

# ---- step 1: the golden corpus matches its generator -----------------------------------
note "vector drift check (CPython ground truth)"
set +e
"${PYTHON[@]}" "$ROOT/scripts/extract/gen_bignum_vectors.py" --check > "$ART_DIR/drift.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit drift failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"drift.log\""
  note "FAIL: golden corpus drifted from its generator"
  exit "$rc"
fi
emit drift passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"drift.log\""
cp "$ROOT/crates/fln-bignum/fixtures/nat_vectors.txt" \
  "$ART_DIR/vector-fixture.txt"
cp "$ROOT/crates/fln-bignum/src/nat.rs" \
  "$ART_DIR/nat-source-pristine.rs"

# ---- step 2: the threshold profile is bound to its real fixture sources ----------------
note "binding the threshold profile to the KR-313 and C4 fixture bytes"
profile="$ROOT/crates/fln-bignum/fixtures/kernel_reduction_profile.tsv"
cp "$profile" "$ART_DIR/profile.snapshot.tsv"
source_count=0
full_source_drifts=0
while IFS=$'\t' read -r kind source measured_sha expected_projection projection_kind; do
  [ "$kind" = "source" ] || continue
  source_count=$((source_count + 1))
  if [ ! -f "$ROOT/$source" ]; then
    emit profile_binding failed "\"detail\":\"profile source missing\",\"source\":\"$source\""
    note "FAIL: profile source is missing: $source"
    exit 1
  fi
  cp "$ROOT/$source" "$ART_DIR/profile-source-$source_count.bin"
  actual_sha="$(sha256sum "$ROOT/$source" | awk '{print $1}')"
  if [ "$actual_sha" != "$measured_sha" ]; then
    full_source_drifts=$((full_source_drifts + 1))
  fi
  set +e
  actual_projection="$(
    "${PYTHON[@]}" - "$ROOT/$source" "$projection_kind" <<'EOF'
import hashlib
import sys

source_path, projection_kind = sys.argv[1:]
data = open(source_path, "rb").read()
markers = {
    "kr313-operation-test-body-v1": (
        b"fn kr313_the_pin_operation_table_computes_literal_results() {",
        b"#[test]\nfn kr313_comparisons_produce_bool_constants()",
    ),
    "c4-nat-slice-v1": (
        b"/* ---- slice 3: bignum-backed Nat families */",
        b"/* ---- slice 3: Name equality",
    ),
}
try:
    start_marker, end_marker = markers[projection_kind]
except KeyError:
    sys.exit(4)
if data.count(start_marker) != 1 or data.count(end_marker) != 1:
    sys.exit(3)
start = data.index(start_marker)
end = data.index(end_marker, start + len(start_marker))
print(hashlib.sha256(data[start:end]).hexdigest())
EOF
  )"
  projection_rc=$?
  set -e
  if [ "$projection_rc" -ne 0 ] || [ "$actual_projection" != "$expected_projection" ]; then
    emit profile_binding failed \
      "\"detail\":\"profile semantic projection drifted\",\"source\":\"$source\",\"projection\":\"$projection_kind\""
    note "FAIL: profile semantic projection drifted: $source ($projection_kind)"
    exit 1
  fi
done < "$profile"
if [ "$source_count" -ne 2 ]; then
  emit profile_binding failed "\"detail\":\"profile source-row floor drifted\",\"sources\":$source_count"
  note "FAIL: threshold profile must bind exactly two fixture sources"
  exit 1
fi
emit profile_binding passed \
  "\"sources\":2,\"semantic_projections\":2,\"full_source_drifts\":$full_source_drifts,\"profile\":\"crates/fln-bignum/fixtures/kernel_reduction_profile.tsv\""

# ---- step 3: the real suite ------------------------------------------------------------
note "running the bignum + ABI consumer suites"
set +e
( cd "$ROOT" && CARGO_TARGET_DIR="$BUILD_TARGET" \
    cargo test -q -p fln-bignum -p fln-unsafe-abi -p fln-rt ) \
  > "$ART_DIR/suite.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit suite failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"suite.log\""
  note "FAIL: bignum/ABI suite failed (see $ART_DIR/suite.log)"
  exit 1
fi
emit suite passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"suite.log\""

# ---- step 4: the real C4 stage0 path agrees with the pinned runtime ---------------------
note "running the C4 stage0 Reference-vs-Marrow gauntlet"
set +e
( cd "$ROOT" && FLN_E2E_CARGO_TARGET_DIR="$BUILD_TARGET" \
    bash scripts/e2e/marrow_stage0_gauntlet.sh ) \
  > "$ART_DIR/c4.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit c4_gauntlet failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"c4.log\""
  note "FAIL: C4 stage0 gauntlet failed (see $ART_DIR/c4.log)"
  exit 1
fi
c4_dir="$(sed -n 's/^.*PASS — artifacts in //p' "$ART_DIR/c4.log" | tail -1)"
if [ -z "$c4_dir" ] || [ ! -s "$c4_dir/facts_marrow.ndjson" ] \
    || [ ! -s "$c4_dir/facts_reference.ndjson" ]; then
  emit c4_gauntlet failed "\"detail\":\"gauntlet passed without retained fact streams\",\"artifact\":\"c4.log\""
  note "FAIL: C4 gauntlet did not retain both fact streams"
  exit 1
fi
marrow_nat_facts="$(grep -c '"probe":"nat\.' "$c4_dir/facts_marrow.ndjson")"
reference_nat_facts="$(grep -c '"probe":"nat\.' "$c4_dir/facts_reference.ndjson")"
if [ "$marrow_nat_facts" -ne 28 ] || [ "$reference_nat_facts" -ne 28 ] \
    || ! cmp -s "$c4_dir/facts_marrow.ndjson" "$c4_dir/facts_reference.ndjson"; then
  emit c4_gauntlet failed "\"detail\":\"Nat fact population or full differential drifted\",\"artifact\":\"c4.log\""
    note "FAIL: C4 Nat facts drifted"
    exit 1
fi
cp "$c4_dir/run.ndjson" "$ART_DIR/c4-run.ndjson"
cp "$c4_dir/facts_marrow.ndjson" "$ART_DIR/c4-facts-marrow.ndjson"
cp "$c4_dir/facts_reference.ndjson" "$ART_DIR/c4-facts-reference.ndjson"
emit c4_gauntlet passed "\"facts\":28,\"artifact\":\"c4.log\""

# ---- step 5: every named production mutant must be killed -------------------------------
OVERLAY="$ART_DIR/overlay"
mkdir -p "$OVERLAY/crates/fln-kernel/tests" "$OVERLAY/tribunal/fixtures/c4"
for crate in fln-core fln-bignum; do
  cp -r "$ROOT/crates/$crate" "$OVERLAY/crates/$crate"
done
cp "$ROOT/crates/fln-kernel/tests/k1_judgments.rs" \
  "$OVERLAY/crates/fln-kernel/tests/k1_judgments.rs"
cp "$ROOT/tribunal/fixtures/c4/probe_export.c" \
  "$OVERLAY/tribunal/fixtures/c4/probe_export.c"
cat > "$OVERLAY/Cargo.toml" <<'EOF'
[workspace]
resolver = "3"
members = ["crates/fln-core", "crates/fln-bignum"]
EOF
cp "$ROOT/rust-toolchain.toml" "$OVERLAY/rust-toolchain.toml"

seed_mutation() {
  local mutation_id="$1"
  cp "$ROOT/crates/fln-bignum/src/nat.rs" \
    "$OVERLAY/crates/fln-bignum/src/nat.rs"
  "${PYTHON[@]}" - "$OVERLAY/crates/fln-bignum/src/nat.rs" "$mutation_id" <<'EOF'
import sys

source_path, mutation_id = sys.argv[1:]
source = open(source_path).read()
cells = {
    "carry_drop": (
        "fn add_limbs(",
        "fn sub_limbs(",
        "    if carry != 0 {\n        out.push(carry as u64);\n    }\n",
        "    if false && carry != 0 {\n        out.push(carry as u64);\n    }\n",
    ),
    "borrow_drop": (
        "fn sub_in_place(",
        "#[cfg(test)]\nfn shl1_in_place(",
        "        borrow = u64::from(o1 || o2);\n",
        "        borrow = u64::from(o1 && o2);\n",
    ),
    "normalization_single_pop": (
        "fn normalize(",
        "fn normalized_len(",
        "    while limbs.last() == Some(&0) {\n",
        "    if limbs.last() == Some(&0) {\n",
    ),
    "division_zero_guard_drop": (
        "fn div_rem_limbs(",
        "fn trailing_zero_bits_limbs(",
        "    if divisor.is_empty() || cmp_limbs(dividend, divisor) == Ordering::Less {\n",
        "    if cmp_limbs(dividend, divisor) == Ordering::Less {\n",
    ),
    "threshold_off_by_one": (
        "fn mul_algorithm(",
        "fn add_shifted_limbs(",
        "    if shorter < KARATSUBA_THRESHOLD || longer > shorter.saturating_mul(2) {\n",
        "    if shorter <= KARATSUBA_THRESHOLD || longer > shorter.saturating_mul(2) {\n",
    ),
    "signed_product_flip": (
        "    fn mul(&self, other: &SignedLimbs)",
        "    fn mul_small(&self, factor: u64)",
        "            negative: self.negative ^ other.negative,\n",
        "            negative: self.negative == other.negative,\n",
    ),
    "abi_view_origin_shift": (
        "    pub fn limbs_le(self) -> &'a [u64]",
        "    /// Materialize an owned value",
        "        self.limbs\n",
        (
            "        if self.limbs.is_empty() {\n"
            "            self.limbs\n"
            "        } else {\n"
            "            &self.limbs[1..]\n"
            "        }\n"
        ),
    ),
    "decimal_validation_drop": (
        "    pub fn from_decimal(s: &str)",
        "    /// The normalized little-endian limbs",
        "            if !byte.is_ascii_digit() {\n",
        "            if byte == b'_' {\n",
    ),
    "shift_limb_boundary": (
        "    pub fn checked_shl(&self, bits: u64)",
        "    /// `self >> bits`",
        "        let limb_shift = u128::from(bits / 64);\n",
        "        let limb_shift = u128::from(bits.saturating_sub(1) / 64);\n",
    ),
}
try:
    start_marker, end_marker, old, new = cells[mutation_id]
except KeyError:
    sys.exit(4)
start = source.find(start_marker)
end = source.find(end_marker, start + len(start_marker))
if start < 0 or end < 0:
    sys.exit(3)
region = source[start:end]
if region.count(old) != 1:
    sys.exit(3)
mutated = source[:start] + region.replace(old, new, 1) + source[end:]
with open(source_path, "w") as stream:
    stream.write(mutated)
EOF
}

run_mutation_cell() {
  local mutation_id="$1"
  local target_kind="$2"
  local test_name="$3"
  local artifact="mutant-$mutation_id.log"
  local -a cargo_args=()
  case "$target_kind" in
    lib) cargo_args=(--lib "$test_name") ;;
    properties) cargo_args=(--test properties "$test_name") ;;
    *)
      emit "mutant_$mutation_id" failed \
        "\"detail\":\"unknown test target\",\"target\":\"$target_kind\""
      exit 2
      ;;
  esac

  note "seeding $mutation_id; expecting $test_name to discriminate it"
  set +e
  seed_mutation "$mutation_id"
  mutation_rc=$?
  set -e
  if [ "$mutation_rc" -ne 0 ]; then
    emit "mutant_$mutation_id" failed \
      "\"detail\":\"mutation seed was a no-op\",\"seed_exit\":$mutation_rc"
    note "FAIL: $mutation_id seed did not apply"
    exit 1
  fi

  set +e
  ( cd "$OVERLAY" && CARGO_TARGET_DIR="$OVERLAY/target" \
      cargo test -p fln-bignum "${cargo_args[@]}" -- --exact ) \
    > "$ART_DIR/$artifact" 2>&1
  rc=$?
  set -e
  if [ "$rc" -eq 0 ]; then
    emit "mutant_$mutation_id" failed \
      "\"expected_exit\":\"nonzero\",\"actual_exit\":0,\"artifact\":\"$artifact\""
    note "FAIL: $mutation_id survived $test_name"
    exit 1
  fi
  if ! grep -F "test $test_name" "$ART_DIR/$artifact" | grep -Fq "FAILED"; then
    emit "mutant_$mutation_id" failed \
      "\"detail\":\"registered test did not fail\",\"actual_exit\":$rc,\"artifact\":\"$artifact\""
    note "FAIL: $mutation_id stopped for a reason other than $test_name"
    exit 1
  fi
  emit "mutant_$mutation_id" passed \
    "\"expected_exit\":\"nonzero\",\"actual_exit\":$rc,\"test\":\"$test_name\",\"artifact\":\"$artifact\""
}

run_mutation_cell carry_drop lib nat::tests::u128_model_agreement
run_mutation_cell borrow_drop properties \
  truncated_subtraction_saturates_at_zero_and_never_wraps
run_mutation_cell normalization_single_pop lib nat::tests::edge_laws
run_mutation_cell division_zero_guard_drop lib \
  nat::tests::knuth_d_matches_the_bitwise_model_and_reconstructs_the_dividend
run_mutation_cell threshold_off_by_one lib \
  nat::tests::multiplication_crossovers_are_pinned_and_both_sides_are_equivalent
run_mutation_cell signed_product_flip lib \
  nat::tests::toom3_signed_evaluations_and_carry_chains_match_schoolbook
run_mutation_cell abi_view_origin_shift properties \
  borrowed_limb_views_alias_storage_and_match_owned_arithmetic
run_mutation_cell decimal_validation_drop lib nat::tests::edge_laws
run_mutation_cell shift_limb_boundary lib nat::tests::edge_laws

# ---- step 6: recovery — pristine overlay passes ----------------------------------------
cp "$ROOT/crates/fln-bignum/src/nat.rs" "$OVERLAY/crates/fln-bignum/src/nat.rs"
set +e
( cd "$OVERLAY" && CARGO_TARGET_DIR="$OVERLAY/target" cargo test -q -p fln-bignum ) \
  > "$ART_DIR/recovered.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit recovery failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"recovered.log\""
  note "FAIL: pristine overlay no longer passes"
  exit 1
fi
emit recovery passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"recovered.log\""

emit run_end passed "\"verdict\":\"pass\",\"artifacts_dir\":\"target/e2e/$RUN_ID\",\"cleanup_status\":\"retained_by_policy\""
note "PASS — artifacts in $ART_DIR"
