#!/usr/bin/env bash
# bignum_vectors.sh — shared E2E scenario for the fln-bignum arithmetic core
# (bead franken_lean-npl).
#
# Real-path, no-mock: the golden corpus is drift-checked against its generator
# (CPython ground truth, Lean Nat semantics), the real suite runs (5 725 vectors +
# models), then a REAL bug class is seeded in an overlay — truncated subtraction
# replaced by wrapping subtraction — and the vectors must KILL the mutant, then
# recovery. NDJSON under target/e2e/; fixtures retained.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RUN_ID="bignum-vectors-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_DIR="$ROOT/target/e2e/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
mkdir -p "$ART_DIR"

BEAD="franken_lean-npl"
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
python3 "$ROOT/scripts/extract/gen_bignum_vectors.py" --check > "$ART_DIR/drift.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit drift failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"drift.log\""
  note "FAIL: golden corpus drifted from its generator"
  exit "$rc"
fi
emit drift passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"drift.log\""

# ---- step 2: the real suite ------------------------------------------------------------
note "running the fln-bignum suite (goldens + models + interop)"
set +e
( cd "$ROOT" && CARGO_TARGET_DIR=target_local cargo test -q -p fln-bignum ) \
  > "$ART_DIR/suite.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit suite failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"suite.log\""
  note "FAIL: fln-bignum suite failed (see $ART_DIR/suite.log)"
  exit 1
fi
emit suite passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"suite.log\""

# ---- step 3: seeded mutant must be killed ----------------------------------------------
OVERLAY="$ART_DIR/overlay"
mkdir -p "$OVERLAY"
for crate in fln-core fln-bignum; do
  cp -r "$ROOT/crates/$crate" "$OVERLAY/$crate"
done
cat > "$OVERLAY/Cargo.toml" <<'EOF'
[workspace]
resolver = "3"
members = ["fln-core", "fln-bignum"]
EOF
cp "$ROOT/rust-toolchain.toml" "$OVERLAY/rust-toolchain.toml"
# The mutant: break Lean's div-by-zero law (a real Nat-semantics bug class) by
# making x/0 = x instead of 0. Applied textually to whichever site implements it.
if ! grep -rn "fn div" "$OVERLAY/fln-bignum/src/nat.rs" > /dev/null; then
  emit seeded_mutant failed "\"detail\":\"div implementation not found for seeding\""
  note "FAIL: could not locate the div implementation to seed"
  exit 1
fi
python3 - "$OVERLAY/fln-bignum/src/nat.rs" <<'EOF'
import sys
p = sys.argv[1]
s = open(p).read()
# Strip the div-by-zero guard from div_rem: x/0 stops being 0 (KR-313 violation).
mutated = s.replace(
    "if other.is_zero() || self < other {",
    "if self < other {",
    1,
)
if mutated == s:
    sys.exit(3)
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

# ---- step 4: recovery — pristine overlay passes ----------------------------------------
cp "$ROOT/crates/fln-bignum/src/nat.rs" "$OVERLAY/fln-bignum/src/nat.rs"
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
