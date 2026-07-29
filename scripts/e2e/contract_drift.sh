#!/usr/bin/env bash
# contract_drift.sh — shared E2E scenario for the extracted ABI/OLEAN contracts,
# CLI/Lake census, and extern census (bead franken_lean-53v, plan Appendix B/C).
#
# Real-path, no-mock: the checked-in extraction scripts re-run against the REAL
# pinned vendor tree (and, when the pinned Reference binary is installed, the
# real oracle environment walk), byte-compared against the checked-in artifacts;
# the consuming Rust suites run; then two REAL drift classes are seeded — a
# perturbed generated layout constant, and a rendered artifact desynchronized
# from its inventory root — and each must be KILLED by the named lane, followed
# by byte-verified restoration and a green recovery run. NDJSON under
# target/e2e/; artifacts retained.

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
RUN_ID="contract-drift-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_DIR="$ROOT/target/e2e/$RUN_ID"
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

# ---- lane 4: extern census drift (requires the pinned Reference binary) ----------------
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

# ---- lane 5: the consuming Rust suites -------------------------------------------------
note "running the contract consumer suites (fln-rt, fln-olean, conformance linkage)"
set +e
( cd "$ROOT" \
    && CARGO_TARGET_DIR=target_local cargo test -q -p fln-rt -p fln-olean \
    && CARGO_TARGET_DIR=target_local cargo test -q -p fln-conformance --test contract_roots ) \
  > "$ART_DIR/suite.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit suite failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"suite.log\""
  note "FAIL: contract consumer suites failed (see $ART_DIR/suite.log)"
  exit 1
fi
emit suite passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"suite.log\""

# ---- lane 6: seeded mutation A — perturbed generated layout constant -------------------
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

# ---- lane 7: seeded mutation B — rendered artifact desynced from inventory root --------
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

# ---- lane 8: seeded mutation C — perturbed generated OLEAN header size -----------------
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

# ---- lane 9: recovery — everything green again after restoration -----------------------
note "recovery: drift checks and linkage green after restoration"
set +e
"${PYTHON[@]}" "$ROOT/scripts/extract/gen_abi_contract.py" --check > "$ART_DIR/recovery_abi.log" 2>&1
rc1=$?
"${PYTHON[@]}" "$ROOT/scripts/extract/gen_olean_contract.py" --check > "$ART_DIR/recovery_olean.log" 2>&1
rc2=$?
"${PYTHON[@]}" "$ROOT/scripts/extract/gen_cli_lake_census.py" --check \
  > "$ART_DIR/recovery_cli_lake.log" 2>&1
rc3=$?
( cd "$ROOT" \
    && CARGO_TARGET_DIR=target_local cargo test -q -p fln-rt --test abi_contract \
    && CARGO_TARGET_DIR=target_local cargo test -q -p fln-conformance --test contract_roots ) \
  > "$ART_DIR/recovery_suite.log" 2>&1
rc4=$?
set -e
if [ "$rc1" -ne 0 ] || [ "$rc2" -ne 0 ] || [ "$rc3" -ne 0 ] || [ "$rc4" -ne 0 ]; then
  emit recovery failed "\"abi_check_exit\":$rc1,\"olean_check_exit\":$rc2,\"cli_lake_check_exit\":$rc3,\"suite_exit\":$rc4,\"artifacts\":\"recovery_abi.log,recovery_olean.log,recovery_cli_lake.log,recovery_suite.log\""
  note "FAIL: recovery lane not green (abi_check=$rc1 olean_check=$rc2 cli_lake_check=$rc3 suite=$rc4)"
  exit 1
fi
emit recovery passed "\"abi_check_exit\":0,\"olean_check_exit\":0,\"cli_lake_check_exit\":0,\"suite_exit\":0,\"artifacts\":\"recovery_abi.log,recovery_olean.log,recovery_cli_lake.log,recovery_suite.log\""

emit run_end passed "\"cleanup_status\":\"retained_by_policy\",\"artifact_dir\":\"target/e2e/$RUN_ID\""
note "PASS: all lanes green (artifacts in target/e2e/$RUN_ID)"
