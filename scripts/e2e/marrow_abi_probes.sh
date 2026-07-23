#!/usr/bin/env bash
# marrow_abi_probes.sh — C4 native-ABI probes, both directions on the
# implemented subset (bead fln-lld; corpus family C4, plan §18).
#
# Direction A (Reference): tribunal/fixtures/c4/probe_reference.c compiled by
# the D2 system C compiler against the PINNED toolchain's lean.h, linked to
# the real libleanshared, emits layout/RC facts.
# Direction B (Marrow): fln-unsafe-abi's c4_probe_emit_facts emits the same
# facts from the Rust object model.
# The facts must be identical. A seeded-corruption lane proves the diff
# discriminates; the shadow mutation lane proves ownership faults are caught.
#
# No-mock lane: real cargo test binaries, real gcc, real Reference runtime.
# Missing gcc/toolchain is a TYPED SKIP (limitation recorded), never a pass.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RUN_ID="marrow-abi-probes-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_DIR="$ROOT/target/e2e/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
mkdir -p "$ART_DIR"

BUILD_TARGET="${FLN_E2E_CARGO_TARGET_DIR:-$ROOT/target_local}"
BEAD="fln-lld"
SCHEMA="fln-e2e/1"
HOST="$(uname -sr)"
start_ns=$(date +%s%N)

PIN_TAG="$(awk '/^reference /{for(i=1;i<=NF;i++) if ($i ~ /^tag=/) {sub(/^tag=/,"",$i); print $i}}' "$ROOT/SUITE.lock")"
ELAN_TC="$HOME/.elan/toolchains/leanprover--lean4---$PIN_TAG"

emit() { # step status detail-json-fragment
    local now_ns elapsed_ms
    now_ns=$(date +%s%N)
    elapsed_ms=$(((now_ns - start_ns) / 1000000))
    printf '{"schema":"%s","run_id":"%s","bead":"%s","scenario":"marrow_abi_probes","step":"%s","status":"%s","elapsed_ms":%d,"host":"%s",%s}\n' \
        "$SCHEMA" "$RUN_ID" "$BEAD" "$1" "$2" "$elapsed_ms" "$HOST" "$3" >>"$LOG"
}

note() { printf 'marrow_abi_probes: %s\n' "$*" >&2; }

emit run_start started "\"cwd\":\"$ROOT\",\"argv\":\"$0\",\"pin\":\"$PIN_TAG\",\"cargo_target\":\"$BUILD_TARGET\""

# ---- lane 1: full unit/property/mutation suite (boundary + safe surface) ----
note "lane 1: fln-unsafe-abi + fln-rt unit/property/mutation suites"
if CARGO_TARGET_DIR="$BUILD_TARGET" cargo test --offline -q -p fln-unsafe-abi -p fln-rt >"$ART_DIR/unit.log" 2>&1; then
    emit unit_suite passed "\"artifact\":\"unit.log\""
else
    emit unit_suite failed "\"artifact\":\"unit.log\""
    note "unit suite FAILED — see $ART_DIR/unit.log"
    emit run_end failed "\"artifact_dir\":\"target/e2e/$RUN_ID\""
    exit 1
fi

# ---- lane 2: Marrow probe facts ---------------------------------------------
note "lane 2: Marrow emits C4 facts"
if FLN_C4_EMIT="$ART_DIR/facts_marrow.ndjson" CARGO_TARGET_DIR="$BUILD_TARGET" \
    cargo test --offline -q -p fln-unsafe-abi tests::c4_probe_emit_facts >"$ART_DIR/marrow_probe.log" 2>&1 \
    && [ -s "$ART_DIR/facts_marrow.ndjson" ]; then
    marrow_facts=$(wc -l <"$ART_DIR/facts_marrow.ndjson")
    emit marrow_probe passed "\"facts\":$marrow_facts,\"artifact\":\"facts_marrow.ndjson\""
else
    emit marrow_probe failed "\"artifact\":\"marrow_probe.log\""
    emit run_end failed "\"artifact_dir\":\"target/e2e/$RUN_ID\""
    exit 1
fi

# ---- lane 3: pinned-header tripwire -----------------------------------------
note "lane 3: elan header vs vendor pin tripwire"
GCC_BIN="${FLN_E2E_CC:-gcc}"
skip_reference=""
if [ ! -d "$ELAN_TC" ]; then
    skip_reference="pinned toolchain $PIN_TAG not installed under ~/.elan"
elif ! command -v "$GCC_BIN" >/dev/null 2>&1; then
    skip_reference="no system C compiler ($GCC_BIN)"
fi
if [ -z "$skip_reference" ]; then
    vendor_sha=$(sha256sum "$ROOT/vendor/lean4-src/src/include/lean/lean.h" | cut -d' ' -f1)
    elan_sha=$(sha256sum "$ELAN_TC/include/lean/lean.h" | cut -d' ' -f1)
    if [ "$vendor_sha" = "$elan_sha" ]; then
        emit header_tripwire passed "\"sha256\":\"$vendor_sha\""
    else
        # Facts still compare against the DEPLOYED header's behavior; a hash
        # divergence between vendor pin and deployed toolchain is itself a
        # finding that must be triaged, so the lane fails.
        emit header_tripwire failed "\"vendor_sha256\":\"$vendor_sha\",\"elan_sha256\":\"$elan_sha\""
        emit run_end failed "\"artifact_dir\":\"target/e2e/$RUN_ID\""
        exit 1
    fi
fi

# ---- lane 4: Reference probe (compile + run) --------------------------------
if [ -n "$skip_reference" ]; then
    note "lane 4 SKIPPED (typed limitation): $skip_reference"
    emit reference_probe skipped "\"limitation\":\"$skip_reference\",\"level\":\"L1-local-only\""
    emit fact_diff skipped "\"limitation\":\"reference facts unavailable\""
else
    note "lane 4: compile probe_reference.c against $PIN_TAG and run"
    if "$GCC_BIN" -O1 -Wall -Werror -I "$ELAN_TC/include" \
        "$ROOT/tribunal/fixtures/c4/probe_reference.c" \
        -L "$ELAN_TC/lib/lean" -lleanshared \
        -Wl,-rpath,"$ELAN_TC/lib/lean" \
        -o "$ART_DIR/probe_reference" >"$ART_DIR/gcc.log" 2>&1; then
        emit reference_compile passed "\"artifact\":\"gcc.log\""
    else
        emit reference_compile failed "\"artifact\":\"gcc.log\""
        emit run_end failed "\"artifact_dir\":\"target/e2e/$RUN_ID\""
        exit 1
    fi
    if "$ART_DIR/probe_reference" >"$ART_DIR/facts_reference.ndjson" 2>"$ART_DIR/probe_reference.err"; then
        ref_facts=$(wc -l <"$ART_DIR/facts_reference.ndjson")
        emit reference_probe passed "\"facts\":$ref_facts,\"artifact\":\"facts_reference.ndjson\""
    else
        emit reference_probe failed "\"artifact\":\"probe_reference.err\""
        emit run_end failed "\"artifact_dir\":\"target/e2e/$RUN_ID\""
        exit 1
    fi

    # ---- lane 5: the differential -------------------------------------------
    note "lane 5: diff Reference facts against Marrow facts"
    sort "$ART_DIR/facts_reference.ndjson" >"$ART_DIR/facts_reference.sorted"
    sort "$ART_DIR/facts_marrow.ndjson" >"$ART_DIR/facts_marrow.sorted"
    if diff -u "$ART_DIR/facts_reference.sorted" "$ART_DIR/facts_marrow.sorted" >"$ART_DIR/facts.diff"; then
        emit fact_diff passed "\"facts\":$(wc -l <"$ART_DIR/facts_marrow.sorted"),\"artifact\":\"facts.diff\""
    else
        emit fact_diff failed "\"artifact\":\"facts.diff\""
        note "FACT DIVERGENCE — see $ART_DIR/facts.diff"
        emit run_end failed "\"artifact_dir\":\"target/e2e/$RUN_ID\""
        exit 1
    fi

    # ---- lane 6: seeded corruption (the diff must discriminate) -------------
    note "lane 6: seeded corruption negative control"
    sed '1s/"value":[0-9-]*/"value":999999/' "$ART_DIR/facts_reference.sorted" >"$ART_DIR/facts_corrupt.sorted"
    if diff -q "$ART_DIR/facts_corrupt.sorted" "$ART_DIR/facts_marrow.sorted" >/dev/null 2>&1; then
        emit corruption_control failed "\"detail\":\"corrupted facts compared equal — the differential does not discriminate\""
        emit run_end failed "\"artifact_dir\":\"target/e2e/$RUN_ID\""
        exit 1
    else
        emit corruption_control passed "\"detail\":\"seeded corruption detected\""
    fi
fi

# ---- lane 7: ownership-shadow mutation kills (negative/recovery) ------------
note "lane 7: shadow mutation kills"
if CARGO_TARGET_DIR="$BUILD_TARGET" cargo test --offline -q -p fln-unsafe-abi shadow_ >"$ART_DIR/shadow.log" 2>&1; then
    emit shadow_mutations passed "\"artifact\":\"shadow.log\""
else
    emit shadow_mutations failed "\"artifact\":\"shadow.log\""
    emit run_end failed "\"artifact_dir\":\"target/e2e/$RUN_ID\""
    exit 1
fi

emit run_end passed "\"cleanup_status\":\"retained_by_policy\",\"artifact_dir\":\"target/e2e/$RUN_ID\""
note "PASS — artifacts in $ART_DIR"
