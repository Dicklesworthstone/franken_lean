#!/usr/bin/env bash
# Cheap (<1 s) tracker health check for the .beads/ FrankenSQLite database
# (bead fln-kyo0).
#
# Why this does more than `br doctor health`:
# Measured on br 0.7.6 against a torn .beads/beads.db-shm header,
# `br doctor health --json` exits 0 ("healthy") because it reads only the SQLite
# file-header user_version bytes without opening FrankenSQLite's WAL/SHM layer,
# while real `br` commands immediately fail with
# `Database error: database is busy (recovery in progress)`.
# This check therefore verifies:
#   1. .beads/, .beads/beads.db, and .beads/issues.jsonl exist and are writable;
#   2. `br doctor health --json` confirms DB/JSONL presence and schema compatibility;
#   3. `br count --no-auto-import --no-auto-flush` and `br sync --status` open
#      the real FrankenSQLite storage layer cleanly without hitting a recovery wedge.
set -euo pipefail

ROOT="${PWD}"
while [ "$#" -gt 0 ]; do
    case "$1" in
        --root)
            shift
            if [ "$#" -eq 0 ]; then
                printf 'check_beads_health: --root requires a directory\n' >&2
                exit 2
            fi
            ROOT=$1
            ;;
        -h|--help)
            printf 'Usage: %s [--root DIR]\n' "$0"
            exit 0
            ;;
        *)
            printf 'check_beads_health: unknown argument: %s\n' "$1" >&2
            exit 2
            ;;
    esac
    shift
done

print_recovery() {
    cat >&2 <<'EOF'
RECOVERY PROCEDURE (fln-kyo0 — NEVER delete .beads/beads.db* files):
  1. First try non-destructive WAL-index rebuild (preserves issue data and saves
     pre-recovery sidecars under .beads/.br_recovery/schema-migrations/):
       br doctor migrate-schema recover
  2. If `migrate-schema recover` fails or the DB remains wedged, preserve the
     entire .beads/beads.db* family into .doctor/manual-<UTC-timestamp>/ and
     rebuild from canonical .beads/issues.jsonl:
       ts=$(date -u +%Y%m%dT%H%M%SZ)
       mkdir -p ".doctor/manual-${ts}"
       mv .beads/beads.db* ".doctor/manual-${ts}/"
       br doctor --repair --allow-repeated-repair
EOF
}

fail_health() {
    printf 'check_beads_health: UNHEALTHY (%s): %s\n' "$ROOT" "$1" >&2
    if [ "${2:-}" != "" ]; then
        printf '%s\n' "$2" >&2
    fi
    print_recovery
    exit 1
}

if ! command -v br >/dev/null 2>&1; then
    fail_health 'br executable not found on PATH'
fi

BEADS_DIR="$ROOT/.beads"
DB_FILE="$BEADS_DIR/beads.db"
JSONL_FILE="$BEADS_DIR/issues.jsonl"

if [ ! -d "$BEADS_DIR" ]; then
    fail_health "missing $BEADS_DIR directory"
fi
if [ ! -f "$DB_FILE" ]; then
    fail_health "missing $DB_FILE"
fi
if [ ! -f "$JSONL_FILE" ]; then
    fail_health "missing $JSONL_FILE"
fi
if [ ! -w "$BEADS_DIR" ] || [ ! -w "$DB_FILE" ]; then
    fail_health "tracker directory or database is not writable ($DB_FILE)"
fi

health_out=$(cd "$ROOT" && br doctor health --json 2>&1) || true
if ! printf '%s' "$health_out" | grep -q '"db_present"[[:space:]]*:[[:space:]]*true' \
    || ! printf '%s' "$health_out" | grep -q '"jsonl_present"[[:space:]]*:[[:space:]]*true' \
    || ! printf '%s' "$health_out" | grep -q '"schema_compatible"[[:space:]]*:[[:space:]]*true'; then
    fail_health 'br doctor health reported missing DB/JSONL or incompatible schema' "$health_out"
fi

if ! count_out=$(cd "$ROOT" && br count --no-auto-import --no-auto-flush 2>&1); then
    fail_health 'br count could not open FrankenSQLite storage cleanly' "$count_out"
fi

if ! sync_out=$(cd "$ROOT" && br sync --status 2>&1); then
    fail_health 'br sync --status failed against FrankenSQLite storage' "$sync_out"
fi

printf 'check_beads_health: OK root=%s count=%s\n' "$ROOT" "$(printf '%s' "$count_out" | tr -d '[:space:]')"
