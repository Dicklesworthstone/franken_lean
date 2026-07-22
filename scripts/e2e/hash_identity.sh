#!/usr/bin/env bash
# hash_identity.sh — shared E2E scenario for the fln-hash identity layer
# (bead franken_lean-rps).
#
# Real-path, no-mock: runs the real fln-hash suite (the BLAKE3 core is checked
# against the OFFICIAL upstream test vectors — 35 lengths x 3 modes x full XOF —
# which are the cross-platform ground truth), then seeds a corrupted vector into a
# scratch fixture and proves the vector gate rejects it, then recovery. Human logs
# on stderr; schema-versioned NDJSON under target/e2e/. Fixtures retained.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RUN_ID="hash-identity-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_DIR="$ROOT/target/e2e/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
mkdir -p "$ART_DIR"

BEAD="franken_lean-rps"
SCHEMA="fln-e2e/1"
HOST="$(uname -sr)"
start_ns=$(date +%s%N)

emit() { # emit <step_id> <status> <detail-json-fragment>
  local now_ns
  now_ns=$(date +%s%N)
  printf '{"schema":"%s","run_id":"%s","bead":"%s","scenario":"hash_identity","step":"%s","status":"%s","elapsed_ms":%d,"host":"%s",%s}\n' \
    "$SCHEMA" "$RUN_ID" "$BEAD" "$1" "$2" $(( (now_ns - start_ns) / 1000000 )) "$HOST" "$3" >> "$LOG"
}

note() { echo "[hash_identity] $*" >&2; }

emit run_start started "\"cwd\":\"$ROOT\",\"argv\":\"$0\""

# ---- step 1: the real suite against the official vectors -------------------------------
note "running the fln-hash suite (official BLAKE3 vectors + registry + roots)"
set +e
( cd "$ROOT" && cargo test -q -p fln-hash ) > "$ART_DIR/suite.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit suite failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"suite.log\""
  note "FAIL: fln-hash suite failed (see $ART_DIR/suite.log)"
  exit 1
fi
emit suite passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"suite.log\""

# ---- step 2: a corrupted official vector must be detected ------------------------------
SCRATCH="$ART_DIR/fixtures"
mkdir -p "$SCRATCH"
FIXTURE="$ROOT/crates/fln-hash/fixtures/blake3_vectors.txt"
cp "$FIXTURE" "$SCRATCH/original.txt"
# Flip the first hex digit of the first vector row's hash field.
awk -F'|' 'BEGIN{OFS="|"} !done && NF==4 && $2 ~ /^[0-9a-f]/ { $2 = ($2 ~ /^0/ ? "f" substr($2,2) : "0" substr($2,2)); done=1 } { print }' \
  "$SCRATCH/original.txt" > "$SCRATCH/corrupted.txt"
if cmp -s "$SCRATCH/original.txt" "$SCRATCH/corrupted.txt"; then
  emit seeded_corruption failed "\"detail\":\"seed produced no change\""
  note "FAIL: corruption seed was a no-op"
  exit 1
fi
# Rebuild against the corrupted fixture in an overlay crate copy: the fixture is
# include_str!'d, so swap it in a scratch copy of the crate and run that test only.
OVERLAY="$SCRATCH/overlay"
mkdir -p "$OVERLAY"
cp -r "$ROOT/crates/fln-hash" "$OVERLAY/fln-hash"
cp -r "$ROOT/crates/fln-core" "$OVERLAY/fln-core"
cp "$SCRATCH/corrupted.txt" "$OVERLAY/fln-hash/fixtures/blake3_vectors.txt"
cat > "$OVERLAY/Cargo.toml" <<'EOF'
[workspace]
resolver = "3"
members = ["fln-hash", "fln-core"]
EOF
cp "$ROOT/rust-toolchain.toml" "$OVERLAY/rust-toolchain.toml"
set +e
( cd "$OVERLAY" && cargo test -q -p fln-hash blake3 ) > "$ART_DIR/corrupted.log" 2>&1
rc=$?
set -e
if [ "$rc" -eq 0 ]; then
  emit seeded_corruption failed "\"expected_exit\":\"nonzero\",\"actual_exit\":0,\"artifact\":\"corrupted.log\""
  note "FAIL: corrupted vector was not detected"
  exit 1
fi
emit seeded_corruption passed "\"expected_exit\":\"nonzero\",\"actual_exit\":$rc,\"detected\":\"vector corruption\",\"artifact\":\"corrupted.log\""

# ---- step 3: recovery — pristine fixture goes green ------------------------------------
cp "$SCRATCH/original.txt" "$OVERLAY/fln-hash/fixtures/blake3_vectors.txt"
set +e
( cd "$OVERLAY" && cargo test -q -p fln-hash blake3 ) > "$ART_DIR/recovered.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit recovery failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"recovered.log\""
  note "FAIL: pristine overlay still fails"
  exit 1
fi
emit recovery passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"recovered.log\""

emit run_end passed "\"verdict\":\"pass\",\"artifacts_dir\":\"target/e2e/$RUN_ID\",\"fixture_root\":\"$SCRATCH\",\"cleanup_status\":\"retained_by_policy\""
note "PASS — artifacts in $ART_DIR"
