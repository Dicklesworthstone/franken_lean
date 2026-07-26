#!/usr/bin/env bash
# gen_core_ext_fixtures.sh — regenerate the fln-core EXTENDED observable fixtures from
# the pinned Reference binary (beads fln-it70, franken_lean-eh0c; Rule D5/D8-2: derived,
# never remembered).
#
# Sibling of gen_core_fixtures.sh, which mines the C0 corpus into fln-conformance. This
# one mines the surfaces C0 never reached — Name ordering/rendering/hygiene, Level
# arithmetic, KVMap, DataValue.sameCtor, FileMap positions — and its output is consumed
# by crates/fln-core/tests/pin_ext_observables.rs.
#
# The Reference participates here in exactly one legal capacity: fixture mine inside the
# conformance apparatus. The binary is located via elan and its commit is verified
# against SUITE.lock BEFORE a byte of output is trusted; the output is deterministic (no
# timestamps, no paths) so two runs are byte-identical.
# Output: crates/fln-core/fixtures/core_ext_observables.txt
#
# WHY THE HEADER IS NOT WRITTEN HERE (it is in gen_core_fixtures.sh): the generator emits
# its own header carrying `Lean.githash`, the binary's own report of what it is. A header
# written by this script would carry the commit read from SUITE.lock — a copy of the
# expectation, not an observation, and true even if the wrong binary produced the records.
# So this script verifies the binary before running it, then verifies that the header the
# binary just wrote names the pinned commit. The consuming test checks it a third time.
#
# Usage: scripts/extract/gen_core_ext_fixtures.sh [--check]
#   --check  regenerate to a scratch file and diff against the checked-in fixture
#            (CI drift mode; exit 1 on drift, 2 on setup failure)

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
GENERATOR="$ROOT/scripts/extract/gen_core_ext_fixtures.lean"
FIXTURE="$ROOT/crates/fln-core/fixtures/core_ext_observables.txt"
MODE="${1:-generate}"

note() { echo "[gen_core_ext_fixtures] $*" >&2; }

# ---- locate and verify the pinned Reference binary (D8: oracle-only) -------------------
PIN_LINE="$(grep -E '^reference ' "$ROOT/SUITE.lock")"
PIN_TAG="$(sed -E 's/.*tag=([^ ]+).*/\1/' <<<"$PIN_LINE")"
PIN_COMMIT="$(sed -E 's/.*commit=([0-9a-f]{40}).*/\1/' <<<"$PIN_LINE")"

LEAN=""
for candidate in "$HOME/.elan/toolchains/leanprover--lean4---$PIN_TAG/bin/lean" \
                 "$(command -v lean 2>/dev/null || true)"; do
  [ -n "$candidate" ] && [ -x "$candidate" ] && { LEAN="$candidate"; break; }
done
if [ -z "$LEAN" ]; then
  note "setup failure: no Reference binary for $PIN_TAG (install: elan toolchain install leanprover/lean4:$PIN_TAG)"
  exit 2
fi

VERSION="$("$LEAN" --version)"
if ! grep -q "$PIN_COMMIT" <<<"$VERSION"; then
  note "setup failure: binary commit does not match SUITE.lock pin"
  note "  binary : $VERSION"
  note "  pinned : $PIN_TAG @ $PIN_COMMIT"
  exit 2
fi
note "oracle: $VERSION"

# ---- generate --------------------------------------------------------------------------
emit() { # emit <dest>
  # Staged in the DESTINATION'S OWN directory, so the rename below is a
  # same-filesystem atomic swap rather than a cross-device copy. Generating straight
  # into place would leave a half-trusted fixture on disk whenever the provenance
  # check below fails — the artifact would exist, unverified, looking generated.
  local staged
  staged="$(mktemp "$(dirname "$1")/.$(basename "$1").tmp.XXXXXX")"

  # The generator writes the whole file, header included. See the note above.
  "$LEAN" --run "$GENERATOR" > "$staged"

  # The artifact must name the binary we verified. A generator that stopped recording
  # provenance, or recorded someone else's, fails here rather than in six months.
  if ! grep -q "^# Oracle: .*commit $PIN_COMMIT " "$staged"; then
    note "generated fixture does not record the pinned commit in its header"
    note "  header : $(sed -n '2p' "$staged")"
    note "  pinned : $PIN_TAG @ $PIN_COMMIT"
    # Kept, not deleted: on a provenance failure the useful thing is to read what the
    # binary actually produced. Dot-prefixed so it stays out of the way, and distinct
    # from the governed `.candidate` convention, which means something else here.
    note "  the rejected output is kept for inspection at: $staged"
    exit 2
  fi

  mv "$staged" "$1"
}

case "$MODE" in
  generate)
    mkdir -p "$(dirname "$FIXTURE")"
    emit "$FIXTURE"
    note "wrote $(grep -c '|' "$FIXTURE") records to ${FIXTURE#"$ROOT"/}"
    ;;
  --check)
    SCRATCH="$(mktemp "${TMPDIR:-/tmp}/core_ext_observables.XXXXXX.txt")"
    emit "$SCRATCH"
    if ! diff -u "$FIXTURE" "$SCRATCH" >&2; then
      note "DRIFT: checked-in fixture does not match the pin (see diff above)"
      exit 1
    fi
    note "no drift: fixture matches the pin"
    ;;
  *)
    note "unknown mode: $MODE"
    exit 2
    ;;
esac
