#!/usr/bin/env bash
# marrow_region_load.sh — compacted regions end to end (bead fln-wgp, §6.4):
# real pinned-toolchain oleans load via mmap + relocation and materialize as
# live objects; page sharing across two consumers is measured with real
# kernel accounting; corrupted regions fault typed (never panic); the atomic
# staging drill proves a crash never half-publishes a region; and the
# hardened trap-on-write drill proves a sealed region kills a raw writer
# with SIGSEGV while the safe surface refuses typed (region hygiene).
#
# No-mock lane: real olean fixtures, real mmap/smaps, real process kills,
# real hardware traps.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RUN_ID="marrow-region-load-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_DIR="$ROOT/target/e2e/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
mkdir -p "$ART_DIR"

BUILD_TARGET="${FLN_E2E_CARGO_TARGET_DIR:-$ROOT/target_local}"
BEAD="fln-wgp"
SCHEMA="fln-e2e/1"
HOST="$(uname -sr)"
start_ns=$(date +%s%N)

emit() { # step status detail-json-fragment
    local now_ns elapsed_ms
    now_ns=$(date +%s%N)
    elapsed_ms=$(((now_ns - start_ns) / 1000000))
    printf '{"schema":"%s","run_id":"%s","bead":"%s","scenario":"marrow_region_load","step":"%s","status":"%s","elapsed_ms":%d,"host":"%s",%s}\n' \
        "$SCHEMA" "$RUN_ID" "$BEAD" "$1" "$2" "$elapsed_ms" "$HOST" "$3" >>"$LOG"
}

note() { printf 'marrow_region_load: %s\n' "$*" >&2; }

fail_run() {
    emit run_end failed "\"artifact_dir\":\"target/e2e/$RUN_ID\""
    exit 1
}

emit run_start started "\"cwd\":\"$ROOT\",\"argv\":\"$0\""

# ---- lane 1: unit/property suites (both crates) -----------------------------
note "lane 1: fln-unsafe-region + fln-rt suites"
if CARGO_TARGET_DIR="$BUILD_TARGET" cargo test --offline -q -p fln-unsafe-region -p fln-rt >"$ART_DIR/unit.log" 2>&1; then
    emit unit_suite passed "\"artifact\":\"unit.log\""
else
    emit unit_suite failed "\"artifact\":\"unit.log\""
    note "unit suite FAILED — see $ART_DIR/unit.log"
    fail_run
fi

# ---- lane 2: build the drivers ----------------------------------------------
if CARGO_TARGET_DIR="$BUILD_TARGET" cargo build --offline -q -p fln-rt -p fln-unsafe-region --examples >"$ART_DIR/build.log" 2>&1; then
    emit build_drivers passed "\"artifact\":\"build.log\""
else
    emit build_drivers failed "\"artifact\":\"build.log\""
    fail_run
fi
LOAD="$BUILD_TARGET/debug/examples/region_load"
SHARE="$BUILD_TARGET/debug/examples/region_share_probe"

# ---- lane 3: real olean loads -----------------------------------------------
FIXTURES=(Init.SizeOfLemmas.olean Init.BinderNameHint.olean Init.olean)
loaded=0
for fx in "${FIXTURES[@]}"; do
    src="$ROOT/tribunal/fixtures/c3/$fx"
    if [ ! -f "$src" ]; then
        emit "load_$fx" skipped "\"limitation\":\"fixture absent\""
        continue
    fi
    if "$LOAD" "$src" >"$ART_DIR/load_$fx.ndjson" 2>"$ART_DIR/load_$fx.err"; then
        objects=$(grep -o '"objects":[0-9]*' "$ART_DIR/load_$fx.ndjson" | cut -d: -f2)
        emit "load_$fx" passed "\"objects\":${objects:-0},\"artifact\":\"load_$fx.ndjson\""
        loaded=$((loaded + 1))
    else
        emit "load_$fx" failed "\"artifact\":\"load_$fx.err\""
        fail_run
    fi
done
if [ "$loaded" -eq 0 ]; then
    note "no fixtures loadable — the real-path lane cannot pass vacuously"
    emit real_lane failed "\"detail\":\"zero fixtures present\""
    fail_run
fi

# ---- lane 4: page sharing across two consumers ------------------------------
note "lane 4: page-sharing probe (PG-4/PG-6 mechanism)"
if "$SHARE" "$ROOT/tribunal/fixtures/c3/Init.SizeOfLemmas.olean" >"$ART_DIR/share.ndjson" 2>"$ART_DIR/share.err"; then
    emit page_sharing passed "\"artifact\":\"share.ndjson\""
else
    emit page_sharing failed "\"artifact\":\"share.ndjson\""
    fail_run
fi

# ---- lane 5: corrupted region faults typed (R18 negative lane) --------------
note "lane 5: corruption negative controls"
CORRUPT="$ART_DIR/corrupt.olean"
cp "$ROOT/tribunal/fixtures/c3/Init.SizeOfLemmas.olean" "$CORRUPT"
# Flip a byte inside the region payload (offset 96: first object's header).
printf '\xff' | dd of="$CORRUPT" bs=1 seek=96 count=1 conv=notrunc status=none
if "$LOAD" "$CORRUPT" >"$ART_DIR/corrupt.ndjson" 2>"$ART_DIR/corrupt.err"; then
    emit corruption_control failed "\"detail\":\"corrupted region loaded successfully\""
    fail_run
fi
if grep -q "panicked" "$ART_DIR/corrupt.err"; then
    emit corruption_control failed "\"detail\":\"fault path panicked instead of typing the error\""
    fail_run
fi
if grep -q '"fault"' "$ART_DIR/corrupt.ndjson"; then
    emit corruption_control passed "\"artifact\":\"corrupt.ndjson\""
else
    emit corruption_control failed "\"detail\":\"no typed fault emitted\""
    fail_run
fi
# Truncation variant.
head -c 2000 "$ROOT/tribunal/fixtures/c3/Init.SizeOfLemmas.olean" >"$CORRUPT"
if "$LOAD" "$CORRUPT" >"$ART_DIR/truncated.ndjson" 2>"$ART_DIR/truncated.err"; then
    emit truncation_control failed "\"detail\":\"truncated region loaded successfully\""
    fail_run
else
    if grep -q "panicked" "$ART_DIR/truncated.err"; then
        emit truncation_control failed "\"detail\":\"panic on truncated input\""
        fail_run
    fi
    emit truncation_control passed "\"artifact\":\"truncated.ndjson\""
fi

# ---- lane 6: atomic staging drill (crash never half-publishes) --------------
note "lane 6: crash-during-construction drill"
OUT="$ART_DIR/rebuilt.olean"
set +e
"$LOAD" "$ROOT/tribunal/fixtures/c3/Init.SizeOfLemmas.olean" \
    --rebuild-out "$OUT" --crash-after-temp >"$ART_DIR/crash.ndjson" 2>&1
crash_rc=$?
set -e
if [ "$crash_rc" -eq 0 ]; then
    emit staging_crash failed "\"detail\":\"crash mode exited 0\""
    fail_run
fi
if [ -e "$OUT" ]; then
    emit staging_crash failed "\"detail\":\"half-published region exists after crash\""
    fail_run
fi
tmp_count=$(find "$ART_DIR" -name ".rebuilt.olean.tmp.*" | wc -l)
emit staging_crash passed "\"leftover_tmps\":$tmp_count,\"artifact\":\"crash.ndjson\""

# Recovery: the clean rerun publishes atomically, and the published region
# loads back through the same production path.
if "$LOAD" "$ROOT/tribunal/fixtures/c3/Init.SizeOfLemmas.olean" \
    --rebuild-out "$OUT" >"$ART_DIR/rebuild.ndjson" 2>"$ART_DIR/rebuild.err" \
    && [ -s "$OUT" ] \
    && "$LOAD" "$OUT" >"$ART_DIR/reload.ndjson" 2>"$ART_DIR/reload.err"; then
    orig_objects=$(grep -o '"objects":[0-9]*' "$ART_DIR/load_Init.SizeOfLemmas.olean.ndjson" | cut -d: -f2)
    reload_objects=$(grep -o '"objects":[0-9]*' "$ART_DIR/reload.ndjson" | cut -d: -f2)
    if [ "$orig_objects" = "$reload_objects" ]; then
        emit staging_recovery passed "\"objects\":$reload_objects,\"artifact\":\"reload.ndjson\""
    else
        emit staging_recovery failed "\"detail\":\"object count drifted: $orig_objects vs $reload_objects\""
        fail_run
    fi
else
    emit staging_recovery failed "\"artifact\":\"rebuild.err\""
    fail_run
fi

# ---- lane 7: hardened trap-on-write drill (region hygiene) ------------------
note "lane 7: hardened trap-on-write drill"
TRAP="$BUILD_TARGET/debug/examples/region_trap_probe"
FIX="$ROOT/tribunal/fixtures/c3/Init.SizeOfLemmas.olean"
pre_sum=$(cksum <"$FIX")

# Positive control: a sealed mapping stays fully readable.
if "$TRAP" "$FIX" no-write >"$ART_DIR/trap_read.ndjson" 2>"$ART_DIR/trap_read.err"; then
    emit trap_read_control passed "\"artifact\":\"trap_read.ndjson\""
else
    emit trap_read_control failed "\"artifact\":\"trap_read.err\""
    fail_run
fi

# Typed refusal: the safe surface refuses sealed mutation (FL-INV-07 plane).
if "$TRAP" "$FIX" safe-write >"$ART_DIR/trap_safe.ndjson" 2>"$ART_DIR/trap_safe.err" \
    && grep -q '"ok":true' "$ART_DIR/trap_safe.ndjson"; then
    emit trap_typed_refusal passed "\"artifact\":\"trap_safe.ndjson\""
else
    emit trap_typed_refusal failed "\"artifact\":\"trap_safe.ndjson\""
    fail_run
fi

# The trap itself: a raw write into the sealed mapping — the move a buggy
# plugin or JIT stub would make through the membrane — must die by SIGSEGV
# (rc 128+11), after the probe logged that it reached the write.
set +e
"$TRAP" "$FIX" raw-write >"$ART_DIR/trap_raw.ndjson" 2>"$ART_DIR/trap_raw.err"
trap_rc=$?
set -e
if [ "$trap_rc" -ne 139 ]; then
    emit trap_on_write failed "\"detail\":\"expected SIGSEGV (rc 139), got rc $trap_rc\""
    fail_run
fi
if grep -q "panicked" "$ART_DIR/trap_raw.err"; then
    emit trap_on_write failed "\"detail\":\"trap path panicked instead of faulting\""
    fail_run
fi
if ! grep -q '"attempting_raw_write"' "$ART_DIR/trap_raw.ndjson"; then
    emit trap_on_write failed "\"detail\":\"probe died before reaching the write\""
    fail_run
fi
emit trap_on_write passed "\"signal\":11,\"rc\":$trap_rc,\"artifact\":\"trap_raw.ndjson\""

# Isolation: the crashed writer changed nothing — the artifact is
# byte-identical (CoW + the trap) and reloads with the lane-3 object count.
post_sum=$(cksum <"$FIX")
if [ "$pre_sum" != "$post_sum" ]; then
    emit trap_isolation failed "\"detail\":\"artifact bytes changed under the trap drill\""
    fail_run
fi
if "$LOAD" "$FIX" >"$ART_DIR/trap_reload.ndjson" 2>"$ART_DIR/trap_reload.err"; then
    lane3_objects=$(grep -o '"objects":[0-9]*' "$ART_DIR/load_Init.SizeOfLemmas.olean.ndjson" | cut -d: -f2)
    trap_objects=$(grep -o '"objects":[0-9]*' "$ART_DIR/trap_reload.ndjson" | cut -d: -f2)
    if [ "$trap_objects" = "$lane3_objects" ]; then
        emit trap_isolation passed "\"objects\":$trap_objects,\"artifact\":\"trap_reload.ndjson\""
    else
        emit trap_isolation failed "\"detail\":\"object count drifted after the drill: $lane3_objects vs $trap_objects\""
        fail_run
    fi
else
    emit trap_isolation failed "\"artifact\":\"trap_reload.err\""
    fail_run
fi

# ---- lane 8: hostile-region fuzz under resource budgets (R18) ---------------
# Deterministic seed-replayable mutation fuzz over the whole engine: typed
# totality, per-case time budget, relocation invariance on surviving
# mutants, 1 MiB stack. The deep count here dwarfs the unit-run default.
note "lane 8: hostile-region fuzz (deep campaign)"
FUZZ_CASES="${FLN_E2E_FUZZ_CASES:-25000}"
if CARGO_TARGET_DIR="$BUILD_TARGET" FLN_REGION_FUZZ_CASES="$FUZZ_CASES" \
    cargo test --offline -q -p fln-rt --test region_fuzz -- --nocapture \
    >"$ART_DIR/fuzz.log" 2>&1; then
    survivors=$(grep -c "surviving operations" "$ART_DIR/fuzz.log" || true)
    emit hostile_fuzz passed "\"cases_per_arm\":$FUZZ_CASES,\"arms_reporting\":$survivors,\"artifact\":\"fuzz.log\""
else
    emit hostile_fuzz failed "\"artifact\":\"fuzz.log\""
    note "fuzz lane FAILED — see $ART_DIR/fuzz.log"
    fail_run
fi

emit run_end passed "\"cleanup_status\":\"retained_by_policy\",\"artifact_dir\":\"target/e2e/$RUN_ID\""
note "PASS — artifacts in $ART_DIR"
