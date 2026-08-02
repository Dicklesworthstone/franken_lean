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
# NDJSON under target/e2e/; fixtures retained.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
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
RUN_ID="bignum-vectors-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_DIR="$ROOT/target/e2e/$RUN_ID"
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

# ---- step 2: the threshold profile is bound to its real fixture sources ----------------
note "binding the threshold profile to the KR-313 and C4 fixture bytes"
profile="$ROOT/crates/fln-bignum/fixtures/kernel_reduction_profile.tsv"
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
