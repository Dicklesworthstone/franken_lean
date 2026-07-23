#!/usr/bin/env bash
# marrow_stage0_gauntlet.sh — the stage0 ABI gauntlet, slice 1 (bead
# franken_lean-83r; plan §6.6/§18.2, corpus family C4).
#
# The exported lean_* C symbol surface under upstream's own generated code:
#   * symbol-surface audit — the staticlib's defined lean_*/mi_* symbols must
#     equal the implemented rows of ci/ABI_EXPORT_STATUS.txt exactly;
#   * stage0 symbol-demand audit — real stage0 translation units compiled by
#     the D2 cc against stage0's OWN lean.h; every demanded lean_*/mi_*
#     symbol must be classified by the status ledger (exported or a typed
#     Unsupported row — an unknown symbol fails);
#   * the link gauntlet — one probe source compiled twice, linked once to
#     Marrow's staticlib and once to the Reference's libleanshared; NDJSON
#     facts must be byte-identical and panic modes must terminate with the
#     same exit code and message line;
#   * the named mutant 83r-M1 — an ownership-convention perturbation
#     (lean_dec_ref_cold dropped to a no-op) planted in a COPY of the crate;
#     the gauntlet must catch it, and the real tree stays byte-identical.
#
# D8 boundary: stage0 C and the Reference runtime are TEST APPARATUS only;
# nothing built here enters a release artifact. Probes are compiled with
# -DNDEBUG exactly as the pin compiles generated C in release (the bare
# lean_notify_assert hook is a debug-build symbol outside the exported
# census). Missing gcc/toolchain is a TYPED SKIP, never a pass.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RUN_ID="marrow-stage0-gauntlet-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_DIR="$ROOT/target/e2e/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
mkdir -p "$ART_DIR"

BUILD_TARGET="${FLN_E2E_CARGO_TARGET_DIR:-$ROOT/target_local}"
BEAD="franken_lean-83r"
SCHEMA="fln-e2e/1"
HOST="$(uname -sr)"
start_ns=$(date +%s%N)

PIN_TAG="$(awk '/^reference /{for(i=1;i<=NF;i++) if ($i ~ /^tag=/) {sub(/^tag=/,"",$i); print $i}}' "$ROOT/SUITE.lock")"
ELAN_TC="$HOME/.elan/toolchains/leanprover--lean4---$PIN_TAG"
GCC_BIN="${FLN_E2E_CC:-gcc}"
STATUS_FILE="$ROOT/ci/ABI_EXPORT_STATUS.txt"

emit() { # step status detail-json-fragment
    local now_ns elapsed_ms
    now_ns=$(date +%s%N)
    elapsed_ms=$(((now_ns - start_ns) / 1000000))
    printf '{"schema":"%s","run_id":"%s","bead":"%s","scenario":"marrow_stage0_gauntlet","step":"%s","status":"%s","elapsed_ms":%d,"host":"%s",%s}\n' \
        "$SCHEMA" "$RUN_ID" "$BEAD" "$1" "$2" "$elapsed_ms" "$HOST" "$3" >>"$LOG"
}

fail() { # step artifact-fragment
    emit "$1" failed "$2"
    note "FAILED at $1 — artifacts in $ART_DIR"
    emit run_end failed "\"artifact_dir\":\"target/e2e/$RUN_ID\""
    exit 1
}

note() { printf 'marrow_stage0_gauntlet: %s\n' "$*" >&2; }

emit run_start started "\"cwd\":\"$ROOT\",\"argv\":\"$0 $*\",\"pin\":\"$PIN_TAG\",\"cargo_target\":\"$BUILD_TARGET\""

# ---- lane 1: unit suite (export parity + small-heap prefix + guard covenant) --
note "lane 1: fln-unsafe-abi unit suite + structure-guard covenant"
if CARGO_TARGET_DIR="$BUILD_TARGET" cargo test --offline -q -p fln-unsafe-abi >"$ART_DIR/unit.log" 2>&1; then
    emit unit_suite passed "\"artifact\":\"unit.log\""
else
    fail unit_suite "\"artifact\":\"unit.log\""
fi
if CARGO_TARGET_DIR="$BUILD_TARGET" cargo run --offline -q -p structure-guard >"$ART_DIR/guard.log" 2>&1; then
    emit structure_guard passed "\"artifact\":\"guard.log\""
else
    fail structure_guard "\"artifact\":\"guard.log\""
fi

# ---- lane 2: staticlib build + symbol-surface audit ---------------------------
note "lane 2: staticlib build + exported-symbol equality vs the status ledger"
if ! CARGO_TARGET_DIR="$BUILD_TARGET" cargo rustc --offline -q -p fln-unsafe-abi --crate-type staticlib --release >"$ART_DIR/staticlib.log" 2>&1; then
    fail staticlib_build "\"artifact\":\"staticlib.log\""
fi
STATICLIB="$BUILD_TARGET/release/libfln_unsafe_abi.a"
[ -f "$STATICLIB" ] || fail staticlib_build "\"detail\":\"staticlib artifact missing\""
nm -g "$STATICLIB" 2>/dev/null | awk '$2=="T" && ($3 ~ /^lean_/ || $3 ~ /^mi_/) {print $3}' | sort -u >"$ART_DIR/symbols_defined.txt"
grep -E '^(row|support|extern) ' "$STATUS_FILE" \
    | awk -F'|' '{status=$2; gsub(/ /,"",status); if (status != "Unsupported") {sym=$1; sub(/^(row|support|extern) /,"",sym); gsub(/ /,"",sym); print sym}}' \
    | sort -u >"$ART_DIR/symbols_rowed.txt"
if diff -u "$ART_DIR/symbols_rowed.txt" "$ART_DIR/symbols_defined.txt" >"$ART_DIR/symbols.diff"; then
    emit symbol_surface passed "\"symbols\":$(wc -l <"$ART_DIR/symbols_defined.txt"),\"artifact\":\"symbols_defined.txt\""
else
    fail symbol_surface "\"artifact\":\"symbols.diff\""
fi

# ---- lane 3: pinned-header + config tripwire ----------------------------------
note "lane 3: header/config tripwires"
skip_reference=""
if [ ! -d "$ELAN_TC" ]; then
    skip_reference="pinned toolchain $PIN_TAG not installed under ~/.elan"
elif ! command -v "$GCC_BIN" >/dev/null 2>&1; then
    skip_reference="no system C compiler ($GCC_BIN)"
fi
if [ -z "$skip_reference" ]; then
    vendor_sha=$(sha256sum "$ROOT/vendor/lean4-src/src/include/lean/lean.h" | cut -d' ' -f1)
    elan_sha=$(sha256sum "$ELAN_TC/include/lean/lean.h" | cut -d' ' -f1)
    config_sha=$(sha256sum "$ELAN_TC/include/lean/config.h" | cut -d' ' -f1)
    stage0_hdr_sha=$(sha256sum "$ROOT/vendor/lean4-src/stage0/src/include/lean/lean.h" | cut -d' ' -f1)
    if [ "$vendor_sha" = "$elan_sha" ]; then
        emit header_tripwire passed "\"lean_h_sha256\":\"$vendor_sha\",\"config_sha256\":\"$config_sha\",\"stage0_lean_h_sha256\":\"$stage0_hdr_sha\""
    else
        fail header_tripwire "\"vendor_sha256\":\"$vendor_sha\",\"elan_sha256\":\"$elan_sha\""
    fi
    if ! grep -q '^#define LEAN_MIMALLOC' "$ELAN_TC/include/lean/config.h"; then
        fail config_tripwire "\"detail\":\"pin config no longer defines LEAN_MIMALLOC; the membrane demand set must be re-derived\""
    fi
    emit config_tripwire passed "\"allocator\":\"LEAN_MIMALLOC\""
fi

# ---- lane 4: stage0 symbol-demand audit ---------------------------------------
# Real stage0 translation units, stage0's OWN lean.h (the exact code the
# ecosystem ships), the pin's shipped config.h. Every demanded lean_*/mi_*
# symbol must be classified by the status ledger; unknown symbols fail.
STAGE0_TUS=("Init/Prelude.c" "Init/SizeOf.c" "Init/Data/Nat/Basic.c")
if [ "${FLN_E2E_DEEP:-0}" = "1" ]; then
    STAGE0_TUS+=("Init/Core.c")
fi
if [ -n "$skip_reference" ]; then
    note "lanes 4-8 SKIPPED (typed limitation): $skip_reference"
    emit stage0_demand_audit skipped "\"limitation\":\"$skip_reference\",\"level\":\"L1-local-only\""
    emit link_gauntlet skipped "\"limitation\":\"$skip_reference\""
    emit fact_differential skipped "\"limitation\":\"$skip_reference\""
    emit panic_parity skipped "\"limitation\":\"$skip_reference\""
    emit mutant_drill skipped "\"limitation\":\"$skip_reference\""
    emit run_end passed "\"cleanup_status\":\"retained_by_policy\",\"artifact_dir\":\"target/e2e/$RUN_ID\",\"level\":\"L1-local-only\""
    note "PASS (typed local-only level) — artifacts in $ART_DIR"
    exit 0
fi
note "lane 4: stage0 symbol-demand audit over ${#STAGE0_TUS[@]} translation units"
: >"$ART_DIR/demand_all.txt"
for tu in "${STAGE0_TUS[@]}"; do
    tu_src="$ROOT/vendor/lean4-src/stage0/stdlib/$tu"
    tu_obj="$ART_DIR/$(echo "$tu" | tr '/' '_').o"
    tu_sha=$(sha256sum "$tu_src" | cut -d' ' -f1)
    if ! "$GCC_BIN" -c -O1 -DNDEBUG \
        -I "$ROOT/vendor/lean4-src/stage0/src/include" \
        -I "$ELAN_TC/include" \
        "$tu_src" -o "$tu_obj" >"$ART_DIR/stage0_cc.log" 2>&1; then
        fail stage0_compile "\"tu\":\"$tu\",\"artifact\":\"stage0_cc.log\""
    fi
    nm -u "$tu_obj" | grep -oE '(lean|mi)_[a-z0-9_]+' | sort -u >>"$ART_DIR/demand_all.txt"
    emit stage0_compile passed "\"tu\":\"$tu\",\"sha256\":\"$tu_sha\""
done
sort -u "$ART_DIR/demand_all.txt" >"$ART_DIR/demand.txt"
exported=0; unsupported=0; unknown=0
: >"$ART_DIR/demand_classified.ndjson"
while IFS= read -r sym; do
    row=$(grep -E "^(row|support|extern) $sym \|" "$STATUS_FILE" | head -1 || true)
    if [ -z "$row" ]; then
        class="UNKNOWN"; unknown=$((unknown + 1))
    else
        status=$(printf '%s' "$row" | awk -F'|' '{gsub(/ /,"",$2); print $2}')
        if [ "$status" = "Unsupported" ]; then
            class="unsupported"; unsupported=$((unsupported + 1))
        else
            class="exported"; exported=$((exported + 1))
        fi
    fi
    printf '{"schema":"fln-83r-demand/1","symbol":"%s","class":"%s"}\n' "$sym" "$class" >>"$ART_DIR/demand_classified.ndjson"
done <"$ART_DIR/demand.txt"
if [ "$unknown" -gt 0 ]; then
    fail stage0_demand_audit "\"exported\":$exported,\"unsupported\":$unsupported,\"unknown\":$unknown,\"artifact\":\"demand_classified.ndjson\""
fi
emit stage0_demand_audit passed "\"demanded\":$(wc -l <"$ART_DIR/demand.txt"),\"exported\":$exported,\"unsupported\":$unsupported,\"unknown\":0,\"artifact\":\"demand_classified.ndjson\""

# ---- lane 5: the link gauntlet (Marrow direction) -----------------------------
note "lane 5: probe_export.c linked against the Marrow staticlib"
PROBE_SRC="$ROOT/tribunal/fixtures/c4/probe_export.c"
probe_sha=$(sha256sum "$PROBE_SRC" | cut -d' ' -f1)
if ! "$GCC_BIN" -O1 -DNDEBUG -Wall -Werror -I "$ELAN_TC/include" \
    "$PROBE_SRC" "$STATICLIB" -lpthread -ldl -lm \
    -o "$ART_DIR/probe_marrow" >"$ART_DIR/gcc_marrow.log" 2>&1; then
    fail marrow_link "\"artifact\":\"gcc_marrow.log\""
fi
if "$ART_DIR/probe_marrow" >"$ART_DIR/facts_marrow.ndjson" 2>"$ART_DIR/probe_marrow.err"; then
    emit link_gauntlet passed "\"facts\":$(wc -l <"$ART_DIR/facts_marrow.ndjson"),\"probe_sha256\":\"$probe_sha\""
else
    fail link_gauntlet "\"artifact\":\"probe_marrow.err\""
fi

# ---- lane 6: the differential (Reference direction + diff + negative control) --
note "lane 6: same probe against libleanshared; facts must be byte-identical"
if ! "$GCC_BIN" -O1 -DNDEBUG -Wall -Werror -I "$ELAN_TC/include" \
    "$PROBE_SRC" -L "$ELAN_TC/lib/lean" -lleanshared -Wl,-rpath,"$ELAN_TC/lib/lean" \
    -o "$ART_DIR/probe_reference" >"$ART_DIR/gcc_reference.log" 2>&1; then
    fail reference_link "\"artifact\":\"gcc_reference.log\""
fi
if ! "$ART_DIR/probe_reference" >"$ART_DIR/facts_reference.ndjson" 2>"$ART_DIR/probe_reference.err"; then
    fail reference_probe "\"artifact\":\"probe_reference.err\""
fi
if diff -u "$ART_DIR/facts_reference.ndjson" "$ART_DIR/facts_marrow.ndjson" >"$ART_DIR/facts.diff"; then
    emit fact_differential passed "\"facts\":$(wc -l <"$ART_DIR/facts_marrow.ndjson"),\"artifact\":\"facts.diff\""
else
    fail fact_differential "\"artifact\":\"facts.diff\""
fi
sed '1s/"value":[0-9-]*/"value":999999/' "$ART_DIR/facts_reference.ndjson" >"$ART_DIR/facts_corrupt.ndjson"
if diff -q "$ART_DIR/facts_corrupt.ndjson" "$ART_DIR/facts_marrow.ndjson" >/dev/null 2>&1; then
    fail corruption_control "\"detail\":\"corrupted facts compared equal — the differential does not discriminate\""
fi
emit corruption_control passed "\"detail\":\"seeded corruption detected\""

# ---- lane 6b: stage0 EXECUTION — the membrane's proof --------------------------
# The pinned tree's own generated Init/Prelude.c (compiled untouched in lane
# 4) linked against Marrow's exported surface and EXECUTED: the module
# initializer plus generated functions plus closure application through
# generated instance objects. The same driver + the SAME object file against
# libleanshared must emit byte-identical facts.
note "lane 6b: stage0 Init/Prelude.o EXECUTES against Marrow (and the Reference)"
DRIVER_SRC="$ROOT/tribunal/fixtures/c4/stage0_driver.c"
driver_sha=$(sha256sum "$DRIVER_SRC" | cut -d' ' -f1)
PRELUDE_OBJ="$ART_DIR/Init_Prelude.c.o"
[ -f "$PRELUDE_OBJ" ] || fail stage0_exec_setup "\"detail\":\"lane-4 Prelude object missing\""
if ! "$GCC_BIN" -O1 -DNDEBUG -Wall -Werror -I "$ELAN_TC/include" \
    "$DRIVER_SRC" "$PRELUDE_OBJ" "$STATICLIB" -lpthread -ldl -lm \
    -o "$ART_DIR/stage0_marrow" >"$ART_DIR/gcc_stage0_marrow.log" 2>&1; then
    fail stage0_exec_link "\"artifact\":\"gcc_stage0_marrow.log\""
fi
if ! "$ART_DIR/stage0_marrow" >"$ART_DIR/facts_stage0_marrow.ndjson" 2>"$ART_DIR/stage0_marrow.err"; then
    fail stage0_exec_run "\"artifact\":\"stage0_marrow.err\""
fi
emit stage0_exec_marrow passed "\"facts\":$(wc -l <"$ART_DIR/facts_stage0_marrow.ndjson"),\"driver_sha256\":\"$driver_sha\""
if ! "$GCC_BIN" -O1 -DNDEBUG -Wall -Werror -I "$ELAN_TC/include" \
    "$DRIVER_SRC" "$PRELUDE_OBJ" -L "$ELAN_TC/lib/lean" -lleanshared -Wl,-rpath,"$ELAN_TC/lib/lean" \
    -o "$ART_DIR/stage0_reference" >"$ART_DIR/gcc_stage0_reference.log" 2>&1; then
    fail stage0_exec_ref_link "\"artifact\":\"gcc_stage0_reference.log\""
fi
if ! "$ART_DIR/stage0_reference" >"$ART_DIR/facts_stage0_reference.ndjson" 2>"$ART_DIR/stage0_reference.err"; then
    fail stage0_exec_ref_run "\"artifact\":\"stage0_reference.err\""
fi
if diff -u "$ART_DIR/facts_stage0_reference.ndjson" "$ART_DIR/facts_stage0_marrow.ndjson" >"$ART_DIR/stage0_facts.diff"; then
    emit stage0_exec_differential passed "\"facts\":$(wc -l <"$ART_DIR/facts_stage0_marrow.ndjson"),\"artifact\":\"stage0_facts.diff\""
else
    fail stage0_exec_differential "\"artifact\":\"stage0_facts.diff\""
fi

# ---- lane 7: panic parity ------------------------------------------------------
# Exit codes and the message line must match. The Reference appends an
# address-nondeterministic backtrace block on the panic_fn path (varies
# between its own runs), so the comparison is rc + first stderr line — the
# deterministic contract; the restriction is typed in ABI_EXPORT_STATUS.txt.
note "lane 7: panic parity (exit codes + message lines)"
for mode in panic-internal panic-fn; do
    set +e
    "$ART_DIR/probe_marrow" "$mode" >/dev/null 2>"$ART_DIR/${mode}_marrow.err"; rc_m=$?
    "$ART_DIR/probe_reference" "$mode" >/dev/null 2>"$ART_DIR/${mode}_reference.err"; rc_r=$?
    set -e
    line_m=$(head -1 "$ART_DIR/${mode}_marrow.err")
    line_r=$(head -1 "$ART_DIR/${mode}_reference.err")
    if [ "$rc_m" != "$rc_r" ] || [ "$line_m" != "$line_r" ] || [ "$rc_m" != 1 ]; then
        fail panic_parity "\"mode\":\"$mode\",\"rc_marrow\":$rc_m,\"rc_reference\":$rc_r"
    fi
    emit panic_parity passed "\"mode\":\"$mode\",\"rc\":$rc_m,\"line\":\"$line_m\""
done

# ---- lane 8: named mutant 83r-M1 ----------------------------------------------
# Ownership-convention perturbation per §18.2: the exported lean_dec_ref_cold
# drops the release. Planted in a COPY of the crate; the differential must
# catch it (rc.child.after_parent_death flips 1 -> 2) and the REAL tree must
# stay byte-identical.
note "lane 8: mutant drill 83r-M1 (lean_dec_ref_cold dropped in a copy)"
MUT_WS="$ART_DIR/mutant-ws"
mkdir -p "$MUT_WS"
# The crate's path-dependency closure rides along (fln-bignum -> fln-core).
cp -r "$ROOT/crates/fln-unsafe-abi" "$MUT_WS/fln-unsafe-abi"
cp -r "$ROOT/crates/fln-bignum" "$MUT_WS/fln-bignum"
cp -r "$ROOT/crates/fln-core" "$MUT_WS/fln-core"
cp "$ROOT/rust-toolchain.toml" "$MUT_WS/"
printf '\n[workspace]\n' >>"$MUT_WS/fln-unsafe-abi/Cargo.toml"
real_sha_before=$(sha256sum "$ROOT/crates/fln-unsafe-abi/src/export.rs" | cut -d' ' -f1)
if ! sed -i 's|unsafe { rc::dec_ref_cold(o) };|let _ = o; // 83r-M1: release dropped|' "$MUT_WS/fln-unsafe-abi/src/export.rs" \
    || ! grep -q "83r-M1" "$MUT_WS/fln-unsafe-abi/src/export.rs"; then
    fail mutant_plant "\"detail\":\"mutation did not apply to the copy\""
fi
if ! (cd "$MUT_WS/fln-unsafe-abi" && CARGO_TARGET_DIR="$MUT_WS/target" cargo rustc --offline -q --crate-type staticlib --release) >"$ART_DIR/mutant_build.log" 2>&1; then
    fail mutant_build "\"artifact\":\"mutant_build.log\""
fi
if ! "$GCC_BIN" -O1 -DNDEBUG -Wall -Werror -I "$ELAN_TC/include" \
    "$PROBE_SRC" "$MUT_WS/target/release/libfln_unsafe_abi.a" -lpthread -ldl -lm \
    -o "$ART_DIR/probe_mutant" >"$ART_DIR/gcc_mutant.log" 2>&1; then
    fail mutant_link "\"artifact\":\"gcc_mutant.log\""
fi
set +e
"$ART_DIR/probe_mutant" >"$ART_DIR/facts_mutant.ndjson" 2>"$ART_DIR/probe_mutant.err"
set -e
if diff -q "$ART_DIR/facts_reference.ndjson" "$ART_DIR/facts_mutant.ndjson" >/dev/null 2>&1; then
    fail mutant_drill "\"detail\":\"83r-M1 SURVIVED — the gauntlet does not discriminate ownership-convention drift\""
fi
if ! grep -q '"probe":"rc.child.after_parent_death","value":2' "$ART_DIR/facts_mutant.ndjson"; then
    fail mutant_drill "\"detail\":\"mutant diverged but not on the designed discriminator\",\"artifact\":\"facts_mutant.ndjson\""
fi
real_sha_after=$(sha256sum "$ROOT/crates/fln-unsafe-abi/src/export.rs" | cut -d' ' -f1)
if [ "$real_sha_before" != "$real_sha_after" ]; then
    fail mutant_isolation "\"detail\":\"the REAL tree changed during the drill\""
fi
emit mutant_drill passed "\"mutant\":\"83r-M1\",\"discriminator\":\"rc.child.after_parent_death\",\"real_tree_sha_stable\":true"

emit run_end passed "\"cleanup_status\":\"retained_by_policy\",\"artifact_dir\":\"target/e2e/$RUN_ID\""
note "PASS — artifacts in $ART_DIR"
