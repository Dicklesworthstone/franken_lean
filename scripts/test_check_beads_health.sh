#!/usr/bin/env bash
# Self-test for scripts/check_beads_health.sh (bead fln-kyo0).
# Exercises:
#   1. Positive control: live repo .beads/ passes in < 1 s.
#   2. Negative control (planted recovery wedge): a scratch copy of the retained
#      .doctor/manual-20260927T2230Z/ family with a torn beads.db-shm header fails
#      loudly, names `recovery in progress`, and prints the recovery procedure.
#   3. Recovery proof: running `br doctor migrate-schema recover` on that torn
#      scratch copy makes scripts/check_beads_health.sh pass again.
#   4. Negative control (non-writable DB): chmod 0400 beads.db fails loudly and
#      prints the recovery procedure.
# Scratch copies under $LAB are intentionally retained (AGENTS.md Rule 1).
set -euo pipefail

REPO="$(cd "$(dirname "$0")/.." && pwd)"
CHECK="$REPO/scripts/check_beads_health.sh"

# 1. Positive control: live workspace passes in < 1000 ms.
start_ns=$(date +%s%N)
pos_out=$(bash "$CHECK" --root "$REPO" 2>&1)
end_ns=$(date +%s%N)
elapsed_ms=$(( (end_ns - start_ns) / 1000000 ))
if [ "$elapsed_ms" -ge 1000 ]; then
    printf 'FAIL: healthy check took %d ms (expected < 1000 ms)\n' "$elapsed_ms" >&2
    exit 1
fi
printf 'PASS positive: %s (%d ms)\n' "$pos_out" "$elapsed_ms"

LAB=$(mktemp -d "${TMPDIR:-/tmp}/fln-beads-health-test.XXXXXXXX")

# 2. Negative control #1: planted torn beads.db-shm recovery marker.
TORN="$LAB/torn"
mkdir -p "$TORN/.beads"
if [ -d "$REPO/.doctor/manual-20260927T2230Z" ]; then
    cp -a "$REPO/.doctor/manual-20260927T2230Z/." "$TORN/.beads/"
else
    cp -a "$REPO/.beads/beads.db" "$TORN/.beads/"
    for sidecar in beads.db-wal beads.db-shm beads.db-wal-cert beads.db-wal-cert-head beads.db-fsqlite-ns-gate beads.db-fsqlite-ns-use; do
        [ -f "$REPO/.beads/$sidecar" ] && cp -a "$REPO/.beads/$sidecar" "$TORN/.beads/"
    done
fi
cp -a "$REPO/.beads/issues.jsonl" "$REPO/.beads/config.yaml" "$REPO/.beads/metadata.json" "$TORN/.beads/"
python3 - "$TORN/.beads/beads.db-shm" <<'PY'
import sys
with open(sys.argv[1], "r+b") as fh:
    fh.write(b"CORRUPT_SHM_HEADER_TORN_RECOVERY_MARKER")
PY

if torn_out=$(bash "$CHECK" --root "$TORN" 2>&1); then
    printf 'FAIL: planted torn-shm wedge unexpectedly passed: %s\n' "$torn_out" >&2
    exit 1
fi
if ! printf '%s' "$torn_out" | grep -q 'recovery in progress'; then
    printf 'FAIL: torn-shm failure omitted recovery-in-progress diagnostic:\n%s\n' "$torn_out" >&2
    exit 1
fi
if ! printf '%s' "$torn_out" | grep -q 'br doctor migrate-schema recover' \
    || ! printf '%s' "$torn_out" | grep -q 'br doctor --repair --allow-repeated-repair'; then
    printf 'FAIL: torn-shm failure omitted recovery procedure:\n%s\n' "$torn_out" >&2
    exit 1
fi
printf 'PASS negative (planted torn-shm recovery wedge refused with recovery procedure)\n'

# 3. Recovery proof on the planted torn-shm copy.
(cd "$TORN" && br doctor migrate-schema recover >/dev/null 2>&1)
rec_out=$(bash "$CHECK" --root "$TORN" 2>&1)
printf 'PASS recovery: %s\n' "$rec_out"

# 4. Negative control #2: non-writable database.
RO="$LAB/readonly"
mkdir -p "$RO/.beads"
cp -a "$REPO/.beads/beads.db" "$REPO/.beads/issues.jsonl" "$REPO/.beads/config.yaml" "$REPO/.beads/metadata.json" "$RO/.beads/"
chmod 0400 "$RO/.beads/beads.db"
if ro_out=$(bash "$CHECK" --root "$RO" 2>&1); then
    chmod 0600 "$RO/.beads/beads.db"
    printf 'FAIL: read-only beads.db unexpectedly passed: %s\n' "$ro_out" >&2
    exit 1
fi
chmod 0600 "$RO/.beads/beads.db"
if ! printf '%s' "$ro_out" | grep -q 'not writable' \
    || ! printf '%s' "$ro_out" | grep -q 'RECOVERY PROCEDURE'; then
    printf 'FAIL: read-only failure omitted writable diagnostic or recovery procedure:\n%s\n' "$ro_out" >&2
    exit 1
fi
printf 'PASS negative (non-writable beads.db refused with recovery procedure)\n'
printf 'ALL 4 BEADS HEALTH CHECKS PASSED (scratch retained at %s)\n' "$LAB"
