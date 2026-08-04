#!/usr/bin/env bash
# G0-1 ABI-resurrection rig: hold the real-mathlib fixture set to the prototype
# region reader against the pinned contracts (bead franken_lean-y24; plan
# §22.1-1; the review amendment's manifest-complete real-mathlib rows).
#
# For every manifest row the tracked fixture bytes are verified (sha256 + size)
# and then WALKED by the contract-driven region reader: object-graph integrity,
# import oracle (ordered rows with flags), and the amendment's extension-entry
# census — any mismatch, integrity fault, or unflagged opaque payload refuses.
# Negative control: one byte flipped in a copied fixture must die TYPED, never
# panic and never walk clean; recovery re-walks the pristine fixture green.
#
# Receipt: NDJSON, schema fln-g01-resurrection/1, written to
# crates/fln-conformance/evidence/g01_abi_resurrection/resurrection_<tag>.jsonl.
# Regeneration of the fixture BYTES is a deliberate act against the pin:
# --regenerate-mathlib-fixtures refetches the corpus cache and requires the
# manifest to hold byte-for-byte, and nothing else ever rewrites these bytes.
set -u -o pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
FIX="$ROOT/tribunal/fixtures/mathlib"
SCRATCH="${TMPDIR:-/tmp}/g01-resurrection-probe.$$"
MODE="${1:-probe}"

fail() {
  printf '[g01_resurrection_probe] REFUSED: %s\n' "$*" >&2
  exit 2
}

mapfile -t ref_rows < <(grep -E '^reference ' "$ROOT/SUITE.lock")
[ "${#ref_rows[@]}" -eq 1 ] || fail "SUITE.lock must have exactly one Reference row"
mapfile -t corpus_rows < <(grep -E '^corpus ' "$ROOT/SUITE.lock")
[ "${#corpus_rows[@]}" -eq 1 ] || fail "SUITE.lock must have exactly one corpus row"
PIN_TAG="" CORPUS_COMMIT=""
for field in ${ref_rows[0]}; do
  case "$field" in
    tag=*) PIN_TAG="${field#tag=}" ;;
  esac
done
for field in ${corpus_rows[0]}; do
  case "$field" in
    commit=*) CORPUS_COMMIT="${field#commit=}" ;;
  esac
done
[[ "$PIN_TAG" =~ ^v[0-9]+\.[0-9]+\.[0-9]+([.-][A-Za-z0-9.-]+)?$ ]] \
  || fail "Reference tag is malformed: $PIN_TAG"
[[ "$CORPUS_COMMIT" =~ ^[0-9a-f]{40}$ ]] \
  || fail "corpus commit is malformed: $CORPUS_COMMIT"

CORPUS="${FLN_MATHLIB_CORPUS:-/data/tmp/mathlib4-corpus}"

if [ "$MODE" = "--regenerate-mathlib-fixtures" ]; then
  # Deliberate regeneration: fetch the pinned corpus cache and require the
  # manifest to hold byte-for-byte. Never runs implicitly.
  [ -d "$CORPUS/.git" ] || fail "corpus checkout absent at $CORPUS"
  head="$(git -C "$CORPUS" rev-parse HEAD)" \
    || fail "cannot read corpus HEAD"
  [ "$head" = "$CORPUS_COMMIT" ] \
    || fail "corpus HEAD $head != pinned $CORPUS_COMMIT"
  LAKE="$HOME/.elan/bin/lake"
  [ -x "$LAKE" ] || fail "elan lake shim not installed"
  ( cd "$CORPUS" && "$LAKE" exe cache get ) \
    || fail "lake exe cache get failed"
  LIB="$CORPUS/.lake/build/lib/lean"
  mismatches=0
  while read -r sha bytes module file objects imports constants blocks entries; do
    case "$sha" in \#*|schema|"") continue ;; esac
    src="$LIB/${module//.//}.olean"
    [ -f "$src" ] || fail "regenerated artifact missing: $src"
    actual_sha="$(sha256sum "$src" | cut -d' ' -f1)"
    actual_bytes="$(stat -c%s "$src")"
    if [ "$actual_sha" != "$sha" ] || [ "$actual_bytes" != "$bytes" ]; then
      printf '[g01_resurrection_probe] MANIFEST DRIFT: %s (sha %s vs %s, bytes %s vs %s)\n' \
        "$module" "$actual_sha" "$sha" "$actual_bytes" "$bytes" >&2
      mismatches=$((mismatches + 1))
    fi
  done < "$FIX/MANIFEST.txt"
  [ "$mismatches" -eq 0 ] || fail "manifest drifted under regeneration: $mismatches rows"
  echo "[g01_resurrection_probe] regeneration verified: manifest holds byte-for-byte at $CORPUS_COMMIT"
  exit 0
fi

[ "$MODE" = "probe" ] || fail "unknown mode: $MODE"

# ---- fixture bytes are exactly the manifest ---------------------------------
while read -r sha bytes module file objects imports constants blocks entries; do
  case "$sha" in \#*|schema|"") continue ;; esac
  [ -f "$FIX/$file" ] || fail "tracked fixture missing: $FIX/$file"
  actual_sha="$(sha256sum "$FIX/$file" | cut -d' ' -f1)"
  actual_bytes="$(stat -c%s "$FIX/$file")"
  if [ "$actual_sha" != "$sha" ] || [ "$actual_bytes" != "$bytes" ]; then
    fail "FIXTURE DRIFT: $file (sha $actual_sha vs $sha, bytes $actual_bytes vs $bytes)"
  fi
done < "$FIX/MANIFEST.txt"

# ---- build the walker --------------------------------------------------------
TARGET_DIR="${CARGO_TARGET_DIR:-$ROOT/target}"
( cd "$ROOT" && CARGO_TARGET_DIR="$TARGET_DIR" cargo build -q --locked -p fln-olean --example walk_olean ) \
  || fail "cannot build walk_olean"
WALKER="$TARGET_DIR/debug/examples/walk_olean"
[ -x "$WALKER" ] || fail "walk_olean missing at $WALKER"

mkdir -p "$SCRATCH" || fail "cannot create scratch $SCRATCH"
RECEIPT_DIR="$ROOT/crates/fln-conformance/evidence/g01_abi_resurrection"
mkdir -p "$RECEIPT_DIR" || fail "cannot create $RECEIPT_DIR"
RECEIPT="$RECEIPT_DIR/resurrection_$PIN_TAG.jsonl"
: > "$RECEIPT"

# ---- walk every manifest row, compare every expected fact --------------------
rows=0
total_objects=0 total_constants=0 total_entries=0
while read -r sha bytes module file objects imports constants blocks entries; do
  case "$sha" in \#*|schema|"") continue ;; esac
  out="$SCRATCH/walk.$file.tsv"
  "$WALKER" "$FIX/$file" > "$out" 2> "$out.err" \
    || fail "fixture $module failed to walk: $(cat "$out.err")"
  read -r _path version w_objects w_imports w_constants w_blocks w_entries w_status < "$out"
  [ "$w_status" = "ok" ] || fail "fixture $module walked with status $w_status"
  [ "$w_objects" = "$objects" ] || fail "$module objects $w_objects != manifest $objects"
  [ "$w_imports" = "$imports" ] || fail "$module imports $w_imports != manifest $imports"
  [ "$w_constants" = "$constants" ] || fail "$module constants $w_constants != manifest $constants"
  [ "$w_blocks" = "$blocks" ] || fail "$module extension blocks $w_blocks != manifest $blocks"
  [ "$w_entries" = "$entries" ] || fail "$module extension entries $w_entries != manifest $entries"
  printf '{"schema":"fln-g01-resurrection/1","module":"%s","fixture":"%s","sha256":"%s","bytes":%s,"objects":%s,"imports":%s,"constants":%s,"extension_blocks":%s,"extension_entries":%s,"outcome":"ok"}\n' \
    "$module" "$file" "$sha" "$bytes" "$objects" "$imports" "$constants" "$blocks" "$entries" >> "$RECEIPT"
  rows=$((rows + 1))
  total_objects=$((total_objects + objects))
  total_constants=$((total_constants + constants))
  total_entries=$((total_entries + entries))
done < "$FIX/MANIFEST.txt"
[ "$rows" -eq 6 ] || fail "manifest must hold exactly 6 rows, walked $rows"

# ---- full pinned stdlib sweep: the 07-22 headline claim, receipted ----------
LIB="$HOME/.elan/toolchains/leanprover--lean4---$PIN_TAG/lib/lean"
if [ -d "$LIB" ]; then
  find "$LIB" -name '*.olean' | sort | xargs "$WALKER" > "$SCRATCH/library_walk.tsv" 2> "$SCRATCH/library_walk.err" \
    || fail "stdlib sweep reported faults: $(tail -2 "$SCRATCH/library_walk.err")"
  lib_total="$(wc -l < "$SCRATCH/library_walk.tsv")"
  lib_ok="$(grep -c $'\tok$' "$SCRATCH/library_walk.tsv" || true)"
  lib_objects="$(awk -F'\t' '$8=="ok"{s+=$3} END{print s}' "$SCRATCH/library_walk.tsv")"
  lib_consts="$(awk -F'\t' '$8=="ok"{s+=$5} END{print s}' "$SCRATCH/library_walk.tsv")"
  [ "$lib_total" -eq "$lib_ok" ] || fail "stdlib sweep: $lib_ok/$lib_total clean"
  [ "$lib_total" -ge 2000 ] || fail "stdlib sweep implausibly small: $lib_total files"
  printf '{"schema":"fln-g01-resurrection/1","stdlib_sweep":{"files":%s,"ok":%s,"objects":%s,"constants":%s},"outcome":"zero_faults"}\n' \
    "$lib_total" "$lib_ok" "$lib_objects" "$lib_consts" >> "$RECEIPT"
else
  # Typed, honest skip: no pinned toolchain on this host (RCH workers, CI).
  printf '{"schema":"fln-g01-resurrection/1","stdlib_sweep":null,"outcome":"skipped","reason":"reference_toolchain_absent","limitation":"L0: full-library sweep unverified on this host"}\n' \
    >> "$RECEIPT"
fi

# ---- import oracle: ordered rows with flags, duplicate-preserving ------------
# Bare fixture names on the command line keep the emitted fixture column equal
# to the oracle's flattened names (the C3 lane does the same cd-for-names).
( cd "$FIX" && "$WALKER" --imports-tsv "$SCRATCH/imports.tsv" \
  Order.Basic.olean Algebra.Group.Basic.olean Data.Real.Basic.olean \
  Tactic.Basic.olean Analysis.SpecialFunctions.Log.Basic.olean Algebra.Ring.Basic.olean \
  > /dev/null 2> "$SCRATCH/imports.err" ) \
  || fail "import-manifest walk failed: $(cat "$SCRATCH/imports.err")"
# The oracle's fixture column uses the flattened tracked names; strip its header.
grep -v '^#' "$FIX/IMPORTS.tsv" > "$SCRATCH/imports.expected"
grep -v '^#' "$SCRATCH/imports.tsv" > "$SCRATCH/imports.actual"
if ! diff -u "$SCRATCH/imports.expected" "$SCRATCH/imports.actual" > "$SCRATCH/imports.diff"; then
  fail "decoded import rows differ from the oracle (see $SCRATCH/imports.diff)"
fi
import_rows="$(wc -l < "$SCRATCH/imports.actual")"
printf '{"schema":"fln-g01-resurrection/1","import_oracle_rows":%s,"outcome":"all_rows_match"}\n' \
  "$import_rows" >> "$RECEIPT"

# ---- negative control: flipped byte dies typed, never panic, never clean -----
CORRUPT="$SCRATCH/corrupt.olean"
cp "$FIX/Order.Basic.olean" "$CORRUPT"
python3 -I -S - "$CORRUPT" <<'PYEOF'
import sys
path = sys.argv[1]
data = bytearray(open(path, "rb").read())
pos = 88 + ((len(data) - 88) // 2 // 8) * 8
data[pos] ^= 0x10
open(path, "wb").write(data)
PYEOF
set +e
"$WALKER" "$CORRUPT" > "$SCRATCH/corrupt.tsv" 2> "$SCRATCH/corrupt.err"
rc=$?
set -e
[ "$rc" -ne 0 ] || fail "corrupted fixture walked clean — integrity checking is not real"
if grep -q "panicked" "$SCRATCH/corrupt.err"; then
  fail "reader panicked on corrupted input (FL-INV-07 violation)"
fi
printf '{"schema":"fln-g01-resurrection/1","corruption_control":"flipped_byte","outcome":"typed_error","exit":%s}\n' \
  "$rc" >> "$RECEIPT"

# ---- recovery: pristine fixture walks green ----------------------------------
"$WALKER" "$FIX/Order.Basic.olean" > "$SCRATCH/recovery.tsv" 2> "$SCRATCH/recovery.err" \
  || fail "recovery walk not green: $(cat "$SCRATCH/recovery.err")"
printf '{"schema":"fln-g01-resurrection/1","recovery":"pristine_fixture_rewalk","outcome":"ok"}\n' \
  >> "$RECEIPT"

printf '{"schema":"fln-g01-resurrection/1","totals":{"fixtures":%s,"objects":%s,"constants":%s,"extension_entries":%s,"import_oracle_rows":%s},"corpus_commit":"%s","reference_tag":"%s","outcome":"pass"}\n' \
  "$rows" "$total_objects" "$total_constants" "$total_entries" "$import_rows" \
  "$CORPUS_COMMIT" "$PIN_TAG" >> "$RECEIPT"

echo "[g01_resurrection_probe] PASS: $rows fixtures, $total_objects objects, $total_constants constants, $total_entries extension entries, receipt at $RECEIPT"
