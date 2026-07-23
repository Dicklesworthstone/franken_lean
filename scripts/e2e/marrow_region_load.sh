#!/usr/bin/env bash
# marrow_region_load.sh — compacted regions end to end (bead fln-wgp, §6.4):
# real pinned-toolchain oleans load via mmap + relocation and materialize as
# live objects; page sharing across two consumers is measured with real
# kernel accounting; corrupted regions fault typed (never panic); and the
# atomic staging drill proves a crash never half-publishes a region.
#
# No-mock lane: real olean fixtures, real mmap/smaps, real process kills.

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
if CARGO_TARGET_DIR="$BUILD_TARGET" cargo build --offline -q -p fln-rt --examples >"$ART_DIR/build.log" 2>&1; then
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

emit run_end passed "\"cleanup_status\":\"retained_by_policy\",\"artifact_dir\":\"target/e2e/$RUN_ID\""
note "PASS — artifacts in $ART_DIR"
