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
# module has its olean and every lake-manifest dependency checkout/build is verified).
# Prints JSON summary line on success, or diagnostic reason on failure.
verify() {
  local root="$1" head modules oleans bytes missing closure_json
  [ -d "$root" ] && [ ! -L "$root" ] || { echo "not a real directory"; return 1; }
  head="$(git -C "$root" rev-parse --verify 'HEAD^{commit}' 2>/dev/null)" || { echo "not a git checkout"; return 1; }
  [ "$head" = "$CORPUS_COMMIT" ] || { echo "HEAD $head != pinned $CORPUS_COMMIT"; return 1; }
  [ "$(tr -d '[:space:]' < "$root/lean-toolchain" 2>/dev/null)" = "leanprover/lean4:$PIN_TAG" ] \
    || { echo "lean-toolchain is not leanprover/lean4:$PIN_TAG"; return 1; }
  [ -d "$root/$LIBRARY_SUBPATH" ] && [ ! -L "$root/$LIBRARY_SUBPATH" ] \
    || { echo "no built olean root $LIBRARY_SUBPATH"; return 1; }
  closure_json="$(python3 -I -S - "$root" "$TOOLCHAIN/lib/lean" <<'PY'
import hashlib, json, subprocess, sys
from pathlib import Path

root = Path(sys.argv[1])
tc_lib = Path(sys.argv[2])
mathlib_src = root / "Mathlib"
mathlib_lib = root / ".lake/build/lib/lean"
mathlib_sub = mathlib_lib / "Mathlib"

sources = sorted(p.relative_to(root).with_suffix("").as_posix() for p in mathlib_src.rglob("*.lean"))
if not sources:
    print("ERR:no Mathlib/*.lean sources")
    sys.exit(1)
missing = [m for m in sources if not (mathlib_lib / f"{m}.olean").is_file()]
if missing:
    print("ERR:modules without an olean (first 5): " + " ".join(missing[:5]))
    sys.exit(1)

inv_hasher = hashlib.sha256()
mathlib_oleans = sorted(mathlib_sub.rglob("*.olean"))
mathlib_bytes = 0
for p in mathlib_oleans:
    if p.is_symlink():
        print(f"ERR:symlinked olean {p}")
        sys.exit(1)
    sz = p.stat().st_size
    mathlib_bytes += sz
    inv_hasher.update(f"Mathlib/{p.relative_to(mathlib_sub).as_posix()}\t{sz}\n".encode())

manifest_path = root / "lake-manifest.json"
if not manifest_path.is_file():
    print("ERR:missing lake-manifest.json")
    sys.exit(1)
manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
pkgs_revs = {}
pkg_oleans = {}
pkg_bytes = {}
dep_oleans_total = 0
dep_bytes_total = 0
for pkg in sorted(manifest.get("packages", []), key=lambda x: x["name"]):
    name = pkg["name"]
    rev = pkg.get("rev", "")
    pkgs_revs[name] = rev
    pkg_root = root / ".lake/packages" / name
    if not pkg_root.is_dir() or pkg_root.is_symlink():
        print(f"ERR:missing dependency package directory .lake/packages/{name}")
        sys.exit(1)
    try:
        actual_rev = subprocess.check_output(
            ["git", "-C", str(pkg_root), "rev-parse", "--verify", "HEAD^{commit}"],
            stderr=subprocess.DEVNULL,
            text=True,
        ).strip()
    except Exception:
        print(f"ERR:dependency package {name} is not a readable git checkout")
        sys.exit(1)
    if actual_rev != rev:
        print(f"ERR:dependency package {name} HEAD {actual_rev} != manifest {rev}")
        sys.exit(1)
    lib_dir = pkg_root / ".lake/build/lib/lean"
    p_oleans = sorted(lib_dir.rglob("*.olean")) if lib_dir.is_dir() else []
    # Cli is an executable-only dependency not imported by Mathlib modules; all 7 library deps must have built oleans.
    if name != "Cli" and not p_oleans:
        print(f"ERR:dependency package {name} has no built .olean files under {lib_dir}")
        sys.exit(1)
    p_bytes = 0
    for p in p_oleans:
        if p.is_symlink():
            print(f"ERR:symlinked dependency olean {p}")
            sys.exit(1)
        sz = p.stat().st_size
        p_bytes += sz
        inv_hasher.update(f"pkg:{name}/{p.relative_to(lib_dir).as_posix()}\t{sz}\n".encode())
    pkg_oleans[name] = len(p_oleans)
    pkg_bytes[name] = p_bytes
    dep_oleans_total += len(p_oleans)
    dep_bytes_total += p_bytes

tc_oleans = sorted(tc_lib.rglob("*.olean")) if tc_lib.is_dir() else []
if not tc_oleans:
    print(f"ERR:toolchain library {tc_lib} has no .olean files")
    sys.exit(1)
tc_bytes = sum(p.stat().st_size for p in tc_oleans)

print(json.dumps({
    "modules": len(sources),
    "oleans": len(mathlib_oleans),
    "bytes": mathlib_bytes,
    "packages": pkgs_revs,
    "package_oleans": pkg_oleans,
    "package_olean_bytes": pkg_bytes,
    "dependency_oleans": dep_oleans_total,
    "dependency_olean_bytes": dep_bytes_total,
    "toolchain_oleans": len(tc_oleans),
    "toolchain_olean_bytes": tc_bytes,
    "corpus_inventory_sha256": inv_hasher.hexdigest(),
}, sort_keys=True))
PY
)" || { echo "${closure_json#ERR:}"; return 1; }
  echo "$closure_json"
}

emit_receipt() {
  local target_root="$1" closure_json="$2" hydration_secs="$3"
  local lean_sha script_sha cache_archives host_name now_utc receipt
  lean_sha="$(sha256sum "$TOOLCHAIN/bin/lean" | cut -d' ' -f1)"
  script_sha="$(sha256sum "${BASH_SOURCE[0]}" | cut -d' ' -f1)"
  cache_archives="$(find "${MATHLIB_CACHE_DIR:-$HOME/.cache/mathlib}" -maxdepth 1 -name '*.ltar' 2>/dev/null | wc -l)"
  host_name="$(hostname)"
  now_utc="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  receipt="$(python3 -I -S - "$closure_json" "$CORPUS_REPO" "$CORPUS_TAG" "$CORPUS_COMMIT" "$PIN_TAG" "$lean_sha" "$target_root" "$LIBRARY_SUBPATH" "$cache_archives" "$hydration_secs" "$host_name" "$now_utc" "$script_sha" <<'PY'
import json, sys
c = json.loads(sys.argv[1])
(_, repo, ctag, ccommit, rtag, lean_sha, root, lib_sub, cache_cnt, secs, host, now_utc, script_sha) = sys.argv[1:]
# Keep exact deterministic key order compatible with MathlibCorpusReceipt::from_row.
out = {
    "schema": "fln-mathlib-corpus/1",
    "corpus_repository": repo,
    "corpus_tag": ctag,
    "corpus_commit": ccommit,
    "reference_tag": rtag,
    "lean_sha256": lean_sha,
    "root": root,
    "library_subpath": lib_sub,
    "source_modules": c["modules"],
    "oleans": c["oleans"],
    "olean_bytes": c["bytes"],
    "dependency_oleans": c["dependency_oleans"],
    "dependency_olean_bytes": c["dependency_olean_bytes"],
    "toolchain_oleans": c["toolchain_oleans"],
    "toolchain_olean_bytes": c["toolchain_olean_bytes"],
    "corpus_inventory_sha256": c["corpus_inventory_sha256"],
    "packages": c["packages"],
    "package_oleans": c["package_oleans"],
    "package_olean_bytes": c["package_olean_bytes"],
    "cache_archives_on_host": int(cache_cnt),
    "hydration_seconds": int(secs),
    "host": host,
    "materialized_at": now_utc,
    "script_sha256": script_sha,
}
print(json.dumps(out, separators=(",", ":")))
PY
)" || return 1
  printf '%s\n' "$receipt"
}

check_existing_root_receipt() {
  local root_receipt="$1" closure_json="$2"
  python3 -I -S - "$root_receipt" "$closure_json" "$CORPUS_REPO" "$CORPUS_TAG" "$CORPUS_COMMIT" "$PIN_TAG" "$LIBRARY_SUBPATH" <<'PY'
import json, sys
from pathlib import Path
rp = Path(sys.argv[1])
c = json.loads(sys.argv[2])
repo, ctag, ccommit, rtag, lib_sub = sys.argv[3:]
try:
    r = json.loads(rp.read_text(encoding="utf-8"))
except Exception as exc:
    print(f"unreadable root receipt {rp}: {exc}")
    sys.exit(1)
checks = [
    ("schema", r.get("schema"), "fln-mathlib-corpus/1"),
    ("corpus_repository", r.get("corpus_repository"), repo),
    ("corpus_tag", r.get("corpus_tag"), ctag),
    ("corpus_commit", r.get("corpus_commit"), ccommit),
    ("reference_tag", r.get("reference_tag"), rtag),
    ("library_subpath", r.get("library_subpath"), lib_sub),
    ("source_modules", r.get("source_modules"), c["modules"]),
    ("oleans", r.get("oleans"), c["oleans"]),
    ("olean_bytes", r.get("olean_bytes"), c["bytes"]),
]
if "corpus_inventory_sha256" in r:
    checks.append(("corpus_inventory_sha256", r.get("corpus_inventory_sha256"), c["corpus_inventory_sha256"]))
for name, got, exp in checks:
    if got != exp:
        print(f"root receipt mismatch on {name}: {got!r} != {exp!r}")
        sys.exit(1)
PY
}

if [ -e "$TARGET" ] || [ -L "$TARGET" ]; then
  if facts="$(verify "$TARGET")"; then
    if [ -e "$TARGET/.fln-corpus-receipt.json" ] || [ -L "$TARGET/.fln-corpus-receipt.json" ]; then
      [ ! -L "$TARGET/.fln-corpus-receipt.json" ] || fail "$TARGET/.fln-corpus-receipt.json is a symlink"
      reason="$(check_existing_root_receipt "$TARGET/.fln-corpus-receipt.json" "$facts")" \
        || fail "$TARGET receipt disagreed with materialized contents ($reason)"
    fi
    : > "$TARGET/.sbh-protect" || fail "cannot write $TARGET/.sbh-protect"
    if [ ! -f "$TARGET/.fln-corpus-receipt.json" ] || [ "${FLN_REFRESH_CORPUS_RECEIPT:-0}" = "1" ]; then
      receipt="$(emit_receipt "$TARGET" "$facts" 0)" || fail "cannot format corpus receipt"
      printf '%s\n' "$receipt" > "$TARGET/.fln-corpus-receipt.json" || fail "cannot write $TARGET/.fln-corpus-receipt.json"
      mkdir -p "$RECEIPT_DIR" || fail "cannot create $RECEIPT_DIR"
      printf '%s\n' "$receipt" > "$RECEIPT" || fail "cannot write $RECEIPT"
    fi
    echo "[materialize_mathlib_corpus] present and verified at $TARGET"
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
receipt="$(emit_receipt "$TARGET" "$facts" "$seconds")" || fail "cannot format corpus receipt"
printf '%s\n' "$receipt" > "$STAGING/.fln-corpus-receipt.json" || fail "cannot write the corpus receipt"
# Scratch-reclamation sweeps leave a directory holding this marker alone.
: > "$STAGING/.sbh-protect"
mv -T "$STAGING" "$TARGET" || fail "cannot rename $STAGING into place at $TARGET"
mkdir -p "$RECEIPT_DIR" || fail "cannot create $RECEIPT_DIR"
printf '%s\n' "$receipt" > "$RECEIPT" || fail "cannot write $RECEIPT"
echo "[materialize_mathlib_corpus] installed at $TARGET; receipt $RECEIPT"
