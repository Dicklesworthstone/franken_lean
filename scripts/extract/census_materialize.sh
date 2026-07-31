#!/usr/bin/env bash
# census_materialize.sh — put the extern/builtin census shards on disk, verified
# against the pins that are checked in (bead fln-census-out-of-git-2ya9).
#
# The four census shards are 231.7 MB of the ~232 MB governed contract surface.
# They remain tracked until removal receives explicit authorization. They are
# derived, not authored: gen_extern_census.sh walks a Reference binary pin-verified
# against SUITE.lock and every projection is deterministic ("derived, never
# remembered"). The compact material needed to check a future materialization is:
#
#   contracts/EXTERN_BUILTIN_ENVIRONMENT.txt   774 B, sha256 per census group
#   contracts/CONTRACT_HANDOFF.txt             exact bytes= per shard
#   SUITE.lock                                 the Reference pin itself
#
# So this script never has to be trusted about content. It verifies existing bytes
# or regenerates them from the pin, then proves them against those committed pins;
# a reproduction that differs is refused rather than accepted.
#
# Sources, in order of preference:
#   1. already on disk and already correct — nothing to do
#   2. regeneration via gen_extern_census.sh, when the pinned Reference exists
#
# This script deliberately has no network-fetch path. Rule D2 prohibits curl, and
# publishing an archive directly into contracts/ would make a torn four-file group
# observable. The checked-in extractor already provides the required critical
# section, candidate validation, atomic renames, and stale-candidate refusal.
#
# Usage: scripts/extract/census_materialize.sh [--verify-only|--help]
#
# Exit taxonomy, matching scripts/check.sh:
#   0 census present and matching the pins
#   1 census present but DISAGREES with the pins (a real, decided failure)
#   2 setup or internal fault (missing pin file, unreadable envelope, bad usage)
#   3 inconclusive — no source could supply the census on this machine

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
ENVELOPE="$ROOT/contracts/EXTERN_BUILTIN_ENVIRONMENT.txt"
HANDOFF="$ROOT/contracts/CONTRACT_HANDOFF.txt"
SUITE_LOCK="$ROOT/SUITE.lock"
GENERATOR="$ROOT/scripts/extract/gen_extern_census.sh"
# The publication lock lives in the machine's shared scratch space when there is one
# (this box's /data/tmp), else in TMPDIR, else /tmp — a hardcoded /data/tmp dies on
# hosts without it (measured: the ci.yml census step on a GitHub-hosted runner).
if [ -d /data/tmp ]; then
  LOCK_DIR=/data/tmp
else
  LOCK_DIR="${TMPDIR:-/tmp}"
fi
PUBLICATION_LOCK="$LOCK_DIR/fln-extern-builtin-census.lockfile"

OBSERVED="$ROOT/contracts/builtin_environment.tsv"
OBSERVED_001="$ROOT/contracts/builtin_environment.001.tsv"
OBSERVED_002="$ROOT/contracts/builtin_environment.002.tsv"
PARTITION="$ROOT/contracts/builtin_partition.tsv"

MODE="${1:-materialize}"
CANDIDATES=(
  "$ROOT/contracts/extern_census.tsv.candidate"
  "$OBSERVED.candidate"
  "$OBSERVED_001.candidate"
  "$OBSERVED_002.candidate"
  "$PARTITION.candidate"
  "$ENVELOPE.candidate"
)

note() { echo "[census_materialize] $*" >&2; }
setup_fault() { note "setup failure: $1"; exit 2; }
inconclusive() { note "inconclusive reason=$1: $2"; exit 3; }
violation() { note "violation reason=$1: $2"; exit 1; }

case "$MODE" in
  materialize|--verify-only) ;;
  --help|-h)
    sed -n '2,33p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
    exit 0
    ;;
  *) setup_fault "unknown mode '$MODE' (expected --verify-only or no argument)" ;;
esac

exec 200>"$PUBLICATION_LOCK"
if ! flock -w 2400 200; then
  inconclusive "publication_lock_timeout" \
    "could not serialize census verification/materialization"
fi

[ -r "$ENVELOPE" ] || setup_fault "missing publication envelope $ENVELOPE"
[ -r "$HANDOFF" ] || setup_fault "missing handoff document $HANDOFF"
[ -r "$SUITE_LOCK" ] || setup_fault "missing $SUITE_LOCK"

# An interrupted publication is neither the old census nor the new one. Refuse it
# before inspecting published paths; gen_extern_census.sh --recover is the one
# explicit recovery path.
for candidate in "${CANDIDATES[@]}"; do
  if [ -e "$candidate" ]; then
    inconclusive "stale_candidate" \
      "interrupted publication candidate ${candidate#"$ROOT/"} exists; recover it explicitly"
  fi
done

# ---- read the committed pins -----------------------------------------------------
envelope_field() {
  local key="$1" value
  value="$(awk -v key="$key" '$1 == key { print $2; exit }' "$ENVELOPE")"
  [ -n "$value" ] || setup_fault "envelope has no '$key' field"
  printf '%s\n' "$value"
}

# bytes= for one path out of the handoff document. Anchored on the path field so a
# key rename cannot silently select the wrong row.
handoff_bytes() {
  local relative="$1" value
  value="$(
    awk -v want="path=$relative" '
      { for (i = 1; i <= NF; i++) if ($i == want) { for (j = 1; j <= NF; j++) if ($j ~ /^bytes=/) { sub(/^bytes=/, "", $j); print $j; exit } } }
    ' "$HANDOFF"
  )"
  [ -n "$value" ] || setup_fault "handoff document has no bytes= for $relative"
  printf '%s\n' "$value"
}

ENV_SHA="$(envelope_field builtin-environment-sha256)"
PARTITION_SHA="$(envelope_field builtin-partition-sha256)"
PIN_TAG="$(sed -E 's/.*tag=([^ ]+).*/\1/' <<<"$(grep -E '^reference ' "$SUITE_LOCK")")"
[ -n "$PIN_TAG" ] || setup_fault "cannot read the Reference pin tag from $SUITE_LOCK"

# ---- verification against the committed pins -------------------------------------
# Returns 0 only when every shard is present, each shard's length equals the handoff
# bytes=, and both census group digests match the envelope. Length is checked per
# shard because the environment digest covers the ordered concatenation, so lengths
# are what fix each shard's boundary within it.
census_matches_pins() {
  local path relative expected actual
  for path in "$OBSERVED" "$OBSERVED_001" "$OBSERVED_002" "$PARTITION"; do
    [ -f "$path" ] || return 1
  done
  for path in "$OBSERVED" "$OBSERVED_001" "$OBSERVED_002" "$PARTITION"; do
    relative="${path#"$ROOT/"}"
    expected="$(handoff_bytes "$relative")"
    actual="$(stat -c %s "$path")"
    if [ "$actual" != "$expected" ]; then
      note "shard length mismatch: $relative is $actual bytes, pin says $expected"
      return 1
    fi
  done
  actual="$(cat "$OBSERVED" "$OBSERVED_001" "$OBSERVED_002" | sha256sum | cut -d' ' -f1)"
  if [ "$actual" != "$ENV_SHA" ]; then
    note "builtin-environment group digest mismatch: got $actual, pin says $ENV_SHA"
    return 1
  fi
  actual="$(sha256sum "$PARTITION" | cut -d' ' -f1)"
  if [ "$actual" != "$PARTITION_SHA" ]; then
    note "builtin-partition digest mismatch: got $actual, pin says $PARTITION_SHA"
    return 1
  fi
  return 0
}

any_shard_present() {
  [ -f "$OBSERVED" ] || [ -f "$OBSERVED_001" ] || [ -f "$OBSERVED_002" ] || [ -f "$PARTITION" ]
}

# ---- 1. already correct ----------------------------------------------------------
if census_matches_pins; then
  note "census already matches the committed pins (tag=$PIN_TAG); nothing to do"
  exit 0
fi

if [ "$MODE" = "--verify-only" ]; then
  if any_shard_present; then
    violation "census_pin_mismatch" \
      "census on disk does not match the committed pins; re-materialise it"
  fi
  inconclusive "census_absent" \
    "census is not on disk; run scripts/extract/census_materialize.sh"
fi

# A partial or wrong census must never be silently blended with a new source: the
# generator's own publication protocol refuses to overwrite a dirty state, and a
# half-replaced group would validate as neither the old census nor the new one.
if any_shard_present; then
  violation "census_pin_mismatch" \
    "census on disk disagrees with the committed pins; automatic materialization refuses to overwrite it"
fi

# ---- 2. regenerate from the pinned Reference -------------------------------------
LEAN="$HOME/.elan/toolchains/leanprover--lean4---$PIN_TAG/bin/lean"
if [ -x "$LEAN" ]; then
  note "regenerating census from the pinned Reference (tag=$PIN_TAG)"
  "$GENERATOR" generate || inconclusive "census_generate_failed" "gen_extern_census.sh could not publish"
  if census_matches_pins; then
    note "census regenerated from the pin and matches the committed pins"
    exit 0
  fi
  violation "census_pin_mismatch" \
    "regeneration from tag=$PIN_TAG did not reproduce the committed pins; the pin or the envelope has drifted"
fi

inconclusive "census_source_unavailable" \
  "no census on disk and no Reference toolchain at $LEAN (install: elan toolchain install leanprover/lean4:$PIN_TAG)"
