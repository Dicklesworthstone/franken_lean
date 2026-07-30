#!/usr/bin/env bash
# bignum_vectors.sh — shared E2E scenario for the fln-bignum arithmetic core
# (beads franken_lean-npl / fln-msou).
#
# Real-path, no-mock: the golden corpus is drift-checked against its generator
# (CPython ground truth, Lean Nat semantics), the real suite runs (5 725 vectors +
# models), the C4 stage0 gauntlet runs the same arithmetic-heavy C probe against
# Marrow and the pinned Reference runtime, then a division-by-zero law defect is
# seeded in an isolated overlay and the vectors must discriminate it before a
# pristine recovery. The fln-msou profile/source/threshold joins and
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
while IFS=$'\t' read -r kind source expected_sha _; do
  [ "$kind" = "source" ] || continue
  source_count=$((source_count + 1))
  if [ ! -f "$ROOT/$source" ]; then
    emit profile_binding failed "\"detail\":\"profile source missing\",\"source\":\"$source\""
    note "FAIL: profile source is missing: $source"
    exit 1
  fi
  actual_sha="$(sha256sum "$ROOT/$source" | awk '{print $1}')"
  if [ "$actual_sha" != "$expected_sha" ]; then
    emit profile_binding failed "\"detail\":\"profile source hash drifted\",\"source\":\"$source\""
    note "FAIL: profile source hash drifted: $source"
    exit 1
  fi
done < "$profile"
if [ "$source_count" -ne 2 ]; then
  emit profile_binding failed "\"detail\":\"profile source-row floor drifted\",\"sources\":$source_count"
  note "FAIL: threshold profile must bind exactly two fixture sources"
  exit 1
fi
emit profile_binding passed "\"sources\":2,\"profile\":\"crates/fln-bignum/fixtures/kernel_reduction_profile.tsv\""

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

# ---- step 5: seeded mutant must be killed ----------------------------------------------
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
# The mutant: break Lean's div-by-zero law (a real Nat-semantics bug class) by
# making x/0 = x instead of 0. Applied to the shared owned/borrowed division
# helper so both surfaces are exercised by the same discriminating suite.
if ! grep -Fq "fn div_rem_limbs" "$OVERLAY/crates/fln-bignum/src/nat.rs"; then
  emit seeded_mutant failed "\"detail\":\"div implementation not found for seeding\""
  note "FAIL: could not locate the div implementation to seed"
  exit 1
fi
"${PYTHON[@]}" - "$OVERLAY/crates/fln-bignum/src/nat.rs" <<'EOF'
import sys
p = sys.argv[1]
s = open(p).read()
# Strip the div-by-zero guard from div_rem: x/0 stops being 0 (KR-313 violation).
marker = "fn div_rem_limbs(dividend: &[u64], divisor: &[u64])"
start = s.find(marker)
if start < 0:
    sys.exit(3)
prefix, production = s[:start], s[start:]
mutated_production = production.replace(
    "if divisor.is_empty() || cmp_limbs(dividend, divisor) == Ordering::Less {",
    "if cmp_limbs(dividend, divisor) == Ordering::Less {",
    1,
)
if mutated_production == production:
    sys.exit(3)
mutated = prefix + mutated_production
open(p, "w").write(mutated)
EOF
mutation_rc=$?
if [ "$mutation_rc" -ne 0 ]; then
  emit seeded_mutant failed "\"detail\":\"mutation seed was a no-op (rc=$mutation_rc)\""
  note "FAIL: mutation seed did not apply"
  exit 1
fi
set +e
( cd "$OVERLAY" && CARGO_TARGET_DIR="$OVERLAY/target" cargo test -q -p fln-bignum ) \
  > "$ART_DIR/mutant.log" 2>&1
rc=$?
set -e
if [ "$rc" -eq 0 ]; then
  emit seeded_mutant failed "\"expected_exit\":\"nonzero\",\"actual_exit\":0,\"artifact\":\"mutant.log\""
  note "FAIL: the div-by-zero-law mutant SURVIVED the suite"
  exit 1
fi
emit seeded_mutant passed "\"expected_exit\":\"nonzero\",\"actual_exit\":$rc,\"detected\":\"div-by-zero-law mutant killed\",\"artifact\":\"mutant.log\""

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
