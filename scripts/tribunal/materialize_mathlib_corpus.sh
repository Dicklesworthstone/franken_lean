#!/usr/bin/env bash
# Materialize the pinned Corpus (SUITE.lock's `corpus` row) on this host, where the whole-Mathlib
# lanes look for it (bead franken_lean-z8j.1.15; kernel_replay.rs `mathlib_corpus_root`):
#
#   ${FLN_MATHLIB_CORPUS:-/data/tmp/mathlib4-corpus}: a real directory holding a git checkout whose
#   HEAD is the pinned commit, with the Reference-built oleans under .lake/build/lib/lean/Mathlib.
#
# The checkout is fetched at the pinned commit with git (D2's tool, as Lake fetches), and the oleans
# are hydrated by the pinned toolchain's `lake exe cache get` (Tribunal apparatus; the cache
# archives are content-addressed, and ~/.cache/mathlib is reused). Everything is assembled in a
# staging directory and renamed into place only once verified, so the lanes never see a half-built
# corpus (their preflight fails a misprovisioned root, and skips only an absent one).
#
# Idempotent: a root that already verifies is reported and left alone; a root that exists and does
# not verify is refused, never overwritten. The receipt (schema fln-mathlib-corpus/1) is written to
# crates/fln-conformance/evidence/mathlib_corpus/<reference tag>.json and into the corpus root.
set -u -o pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd)"
TARGET="${FLN_MATHLIB_CORPUS:-/data/tmp/mathlib4-corpus}"

fail() {
  printf '[materialize_mathlib_corpus] REFUSED: %s\n' "$*" >&2
  exit 2
}

mapfile -t ref_rows < <(grep -E '^reference ' "$ROOT/SUITE.lock")
[ "${#ref_rows[@]}" -eq 1 ] || fail "SUITE.lock must have exactly one reference row"
mapfile -t corpus_rows < <(grep -E '^corpus ' "$ROOT/SUITE.lock")
[ "${#corpus_rows[@]}" -eq 1 ] || fail "SUITE.lock must have exactly one corpus row"
PIN_TAG="" CORPUS_REPO="" CORPUS_TAG="" CORPUS_COMMIT=""
for field in ${ref_rows[0]}; do
  case "$field" in tag=*) PIN_TAG="${field#tag=}" ;; esac
done
read -r _ CORPUS_REPO _ <<< "${corpus_rows[0]}"
for field in ${corpus_rows[0]}; do
  case "$field" in
    tag=*) CORPUS_TAG="${field#tag=}" ;;
    commit=*) CORPUS_COMMIT="${field#commit=}" ;;
  esac
done
[[ "$PIN_TAG" =~ ^v[0-9]+\.[0-9]+\.[0-9]+([.-][A-Za-z0-9.-]+)?$ ]] || fail "Reference tag is malformed: $PIN_TAG"
[[ "$CORPUS_REPO" =~ ^[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+$ ]] || fail "corpus repository is malformed: $CORPUS_REPO"
[[ "$CORPUS_COMMIT" =~ ^[0-9a-f]{40}$ ]] || fail "corpus commit is malformed: $CORPUS_COMMIT"

LAKE="$HOME/.elan/bin/lake"
[ -x "$LAKE" ] || fail "elan's lake shim is not installed at $LAKE"
TOOLCHAIN="$HOME/.elan/toolchains/leanprover--lean4---$PIN_TAG"
[ -x "$TOOLCHAIN/bin/lean" ] || fail "the pinned Reference toolchain is not installed at $TOOLCHAIN"

RECEIPT_DIR="$ROOT/crates/fln-conformance/evidence/mathlib_corpus"
RECEIPT="$RECEIPT_DIR/$PIN_TAG.json"
LIBRARY_SUBPATH=".lake/build/lib/lean/Mathlib"

# verify <root>: the checks the lanes' preflight makes, plus completeness (every Mathlib source
# module has its olean). Prints "modules oleans olean_bytes" on success.
verify() {
  local root="$1" head modules oleans bytes missing
  [ -d "$root" ] && [ ! -L "$root" ] || { echo "not a real directory"; return 1; }
  head="$(git -C "$root" rev-parse --verify 'HEAD^{commit}' 2>/dev/null)" || { echo "not a git checkout"; return 1; }
  [ "$head" = "$CORPUS_COMMIT" ] || { echo "HEAD $head != pinned $CORPUS_COMMIT"; return 1; }
  [ "$(tr -d '[:space:]' < "$root/lean-toolchain")" = "leanprover/lean4:$PIN_TAG" ] \
    || { echo "lean-toolchain is not leanprover/lean4:$PIN_TAG"; return 1; }
  [ -d "$root/$LIBRARY_SUBPATH" ] && [ ! -L "$root/$LIBRARY_SUBPATH" ] \
    || { echo "no built olean root $LIBRARY_SUBPATH"; return 1; }
  modules="$(cd "$root" && find Mathlib -name '*.lean' | wc -l)"
  missing="$(cd "$root" && find Mathlib -name '*.lean' | sed 's/\.lean$//' | while read -r m; do
    [ -f ".lake/build/lib/lean/$m.olean" ] || echo "$m"; done | head -5)"
  [ -z "$missing" ] || { echo "modules without an olean (first 5): $missing"; return 1; }
  oleans="$(find "$root/$LIBRARY_SUBPATH" -name '*.olean' | wc -l)"
  bytes="$(find "$root/$LIBRARY_SUBPATH" -name '*.olean' -printf '%s\n' | awk '{s+=$1} END {print s+0}')"
  echo "$modules $oleans $bytes"
}

if [ -e "$TARGET" ] || [ -L "$TARGET" ]; then
  if facts="$(verify "$TARGET")"; then
    echo "[materialize_mathlib_corpus] present and verified at $TARGET (modules oleans bytes: $facts)"
    exit 0
  fi
  fail "$TARGET exists but is not the pinned corpus ($facts); it is left alone"
fi

STAGING="$TARGET.staging.$$"
mkdir -p "$STAGING" || fail "cannot create $STAGING"
echo "[materialize_mathlib_corpus] staging $CORPUS_REPO@$CORPUS_COMMIT in $STAGING"
git -C "$STAGING" init -q || fail "git init failed"
git -C "$STAGING" remote add origin "https://github.com/$CORPUS_REPO" || fail "git remote add failed"
timeout 3600 git -C "$STAGING" fetch -q --depth 1 origin "$CORPUS_COMMIT" || fail "fetching $CORPUS_COMMIT failed"
git -C "$STAGING" checkout -q --detach FETCH_HEAD || fail "checkout failed"
started="$(date +%s)"
( cd "$STAGING" && timeout 7200 "$LAKE" exe cache get ) || fail "lake exe cache get failed in $STAGING"
seconds=$(( $(date +%s) - started ))
facts="$(verify "$STAGING")" || fail "the staged corpus does not verify: $facts"
read -r modules oleans bytes <<< "$facts"

lean_sha="$(sha256sum "$TOOLCHAIN/bin/lean" | cut -d' ' -f1)"
script_sha="$(sha256sum "${BASH_SOURCE[0]}" | cut -d' ' -f1)"
packages="$(cd "$STAGING" && python3 -c 'import json; m = json.load(open("lake-manifest.json")); print(json.dumps({p["name"]: p.get("rev") for p in m.get("packages", [])}, sort_keys=True))')" \
  || fail "cannot read lake-manifest.json"
cache_archives="$(find "${MATHLIB_CACHE_DIR:-$HOME/.cache/mathlib}" -maxdepth 1 -name '*.ltar' 2>/dev/null | wc -l)"
receipt="$(printf '{"schema":"fln-mathlib-corpus/1","corpus_repository":"%s","corpus_tag":"%s","corpus_commit":"%s","reference_tag":"%s","lean_sha256":"%s","root":"%s","library_subpath":"%s","source_modules":%s,"oleans":%s,"olean_bytes":%s,"packages":%s,"cache_archives_on_host":%s,"hydration_seconds":%s,"host":"%s","materialized_at":"%s","script_sha256":"%s"}' \
  "$CORPUS_REPO" "$CORPUS_TAG" "$CORPUS_COMMIT" "$PIN_TAG" "$lean_sha" "$TARGET" "$LIBRARY_SUBPATH" \
  "$modules" "$oleans" "$bytes" "$packages" "$cache_archives" "$seconds" "$(hostname)" \
  "$(date -u +%Y-%m-%dT%H:%M:%SZ)" "$script_sha")"
printf '%s\n' "$receipt" > "$STAGING/.fln-corpus-receipt.json" || fail "cannot write the corpus receipt"
# Scratch-reclamation sweeps leave a directory holding this marker alone.
: > "$STAGING/.sbh-protect"
mv -T "$STAGING" "$TARGET" || fail "cannot rename $STAGING into place at $TARGET"
mkdir -p "$RECEIPT_DIR" || fail "cannot create $RECEIPT_DIR"
printf '%s\n' "$receipt" > "$RECEIPT" || fail "cannot write $RECEIPT"
echo "[materialize_mathlib_corpus] installed at $TARGET: $modules modules, $oleans oleans, $bytes bytes; receipt $RECEIPT"
