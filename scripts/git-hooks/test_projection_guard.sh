#!/usr/bin/env bash
# Exercises the projection guard against a throwaway repo shaped like the real
# one. Every case asserts the exit code AND that the refusal names its own
# reason, so a guard that refused everything for one generic reason would fail
# here rather than look correct.
set -uo pipefail

# Resolved before the first `cd`: the harness runs inside a throwaway repo, so a
# relative path handed in from the caller's directory would silently miss and
# every guard case would "fail" for want of a hook rather than for a reason.
abspath() { (cd "$(dirname "$1")" && printf '%s/%s\n' "$(pwd)" "$(basename "$1")"); }
HOOK=$(abspath "$1")
PUBLISHER=$(abspath "$2")
[ -x "$HOOK" ] || { printf 'harness: %s is not an executable hook\n' "$HOOK" >&2; exit 2; }
[ -x "$PUBLISHER" ] || { printf 'harness: %s is not an executable publisher\n' "$PUBLISHER" >&2; exit 2; }
LAB=$(mktemp -d "${TMPDIR:-/tmp}/fln-guard-lab.XXXXXXXX")
PASSES=0
FAILS=0

note() { printf '  %s\n' "$1"; }

check() {
    local name="$1" want_code="$2" want_text="$3" got_code="$4" got_text="$5"
    if [ "$got_code" != "$want_code" ]; then
        printf 'FAIL %s: wanted exit %s, got %s\n%s\n' "$name" "$want_code" "$got_code" "$got_text"
        FAILS=$((FAILS + 1))
        return
    fi
    if [ -n "$want_text" ] && ! printf '%s' "$got_text" | grep -qF "$want_text"; then
        printf 'FAIL %s: exit %s correct but reason did not mention %s\n%s\n' \
            "$name" "$want_code" "$want_text" "$got_text"
        FAILS=$((FAILS + 1))
        return
    fi
    printf 'ok   %s (exit %s)\n' "$name" "$got_code"
    PASSES=$((PASSES + 1))
}

# --- a repo shaped like franken_lean -----------------------------------------
mkdir -p "$LAB/repo/.beads" "$LAB/repo/ci" "$LAB/repo/tools/structure-guard/kernel-ownership-publisher"
cd "$LAB/repo" || exit 2
git init --quiet -b main .
git config user.email guard@test
git config user.name guard
git config core.hooksPath "$LAB/hooks"
mkdir -p "$LAB/hooks"
cp "$HOOK" "$LAB/hooks/pre-commit"
chmod +x "$LAB/hooks/pre-commit"

# The guard finds the publisher through CARGO_TARGET_DIR/debug.
mkdir -p "$LAB/target/debug"
cp "$PUBLISHER" "$LAB/target/debug/kernel-ownership-publisher"
export CARGO_TARGET_DIR="$LAB/target"

write_source() { printf '%s\n' "$@" > .beads/issues.jsonl; }
republish() { "$LAB/target/debug/kernel-ownership-publisher" --root . --wait-ms 30000 --robot >/dev/null; }

run_commit() {
    local out code
    out=$(git commit "$@" 2>&1)
    code=$?
    printf '%s' "$out"
    return $code
}

# Baseline: a consistent tree that commits cleanly.
write_source '{"id":"fln-a","title":"a"}' '{"id":"fln-b","title":"b"}'
republish
echo hello > README.md
git add -A
out=$(run_commit -q -m base 2>&1); code=$?
check 'baseline consistent commit is accepted' 0 '' "$code" "$out"

# --- case 1: source changes, projection absent from the commit ---------------
write_source '{"id":"fln-a","title":"a"}' '{"id":"fln-b","title":"b"}' '{"id":"fln-c","title":"c"}'
republish
git add .beads/issues.jsonl            # deliberately NOT the projection
out=$(run_commit -q -m 'source only' 2>&1); code=$?
check 'source without projection is refused' 1 'is not a projection of' "$code" "$out"
note 'refused because the working-tree projection is not in the commit'

# --- case 2: source and projection together ----------------------------------
git add ci/KERNEL_CONTRACT_OWNERSHIP.jsonl
out=$(run_commit -q -m 'source and projection' 2>&1); code=$?
check 'source with a matching projection is accepted' 0 '' "$code" "$out"

# --- case 3: equal record count, different ids (a count check would pass) -----
write_source '{"id":"fln-a","title":"a"}' '{"id":"fln-b","title":"b"}' '{"id":"fln-ZZZ","title":"z"}'
git add .beads/issues.jsonl
out=$(run_commit -q -m 'same count different ids' 2>&1); code=$?
check 'equal count with different ids is refused' 1 'is not a projection of' "$code" "$out"
note 'this is the case a record_count comparison would wave through'
republish; git add -A; run_commit -q -m 'resync' >/dev/null 2>&1

# --- case 4: a commit that does not touch the tracker export -----------------
echo more >> README.md
git add README.md
out=$(run_commit -q -m 'unrelated change' 2>&1); code=$?
check 'a commit that leaves the export alone is accepted' 0 '' "$code" "$out"

# --- case 5: git commit --only, whose index is not the working tree -----------
# The failure the swarm actually hits: `-o` commits working-tree content for the
# named paths and bypasses the index, so a guard reading the index alone would
# judge the wrong bytes.
write_source '{"id":"fln-a","title":"a"}' '{"id":"fln-b","title":"b"}' '{"id":"fln-new","title":"n"}'
out=$(run_commit -q -o .beads/issues.jsonl -m 'only the export' 2>&1); code=$?
check 'commit --only carrying just the export is refused' 1 'is not a projection of' "$code" "$out"
note 'proves the guard reads the prospective tree, not the index or the checkout'

republish
out=$(run_commit -q -o .beads/issues.jsonl ci/KERNEL_CONTRACT_OWNERSHIP.jsonl -m 'only, both' 2>&1); code=$?
check 'commit --only carrying both is accepted' 0 '' "$code" "$out"

# --- case 5b: the prospective tree is stale while the working tree is fresh ---
# The discriminating case, and the one the swarm actually produces: stage the
# export, republish afterwards, forget to `git add` the projection. The commit
# is stale even though the checkout is not, so a guard that hashes the working
# tree passes it. Cases 1 and 5 do NOT discriminate here — in both of them the
# two trees agree, so a working-tree-reading guard gets the right answer for the
# wrong reason. This was found by a surviving mutant, not by inspection.
write_source '{"id":"fln-a","title":"a"}' '{"id":"fln-b","title":"b"}' '{"id":"fln-late","title":"l"}'
git add .beads/issues.jsonl        # prospective projection is still the OLD one
republish                          # working-tree projection is now the NEW one
out=$(run_commit -q -m 'staged export, projection republished but unstaged' 2>&1); code=$?
check 'a stale commit under a fresh checkout is refused' 1 'is not a projection of' "$code" "$out"
note 'the checkout is consistent here; only the commit is not'
git add ci/KERNEL_CONTRACT_OWNERSHIP.jsonl
out=$(run_commit -q -m 'projection staged too' 2>&1); code=$?
check 'and is accepted once the projection joins the commit' 0 '' "$code" "$out"

# --- case 5c: the working tree is stale while the prospective tree is fresh ---
# The other direction, which must not produce a false refusal: a consistent pair
# is staged and the checkout then moves on. The commit is fine and must pass.
git add -A; run_commit -q -m sync >/dev/null 2>&1
write_source '{"id":"fln-a","title":"a"}' '{"id":"fln-b","title":"b"}' '{"id":"fln-late","title":"l"}' '{"id":"fln-p","title":"p"}'
republish
git add .beads/issues.jsonl ci/KERNEL_CONTRACT_OWNERSHIP.jsonl   # consistent pair staged
write_source '{"id":"fln-a","title":"a"}' '{"id":"fln-unstaged","title":"u"}' # checkout moves on
out=$(run_commit -q -m 'consistent commit under a moved-on checkout' 2>&1); code=$?
check 'a consistent commit is accepted even when the checkout has moved on' 0 '' "$code" "$out"
git checkout -- .beads/issues.jsonl 2>/dev/null || true

# --- case 9: the publisher cannot answer --------------------------------------
# A guard that cannot regenerate must refuse, not wave the commit through. Also
# found by a surviving mutant: nothing here covered the undecided path.
mv "$LAB/target/debug/kernel-ownership-publisher" "$LAB/publisher.real"
printf '#!/bin/sh\necho "publisher exploded" >&2\nexit 2\n' > "$LAB/target/debug/kernel-ownership-publisher"
chmod +x "$LAB/target/debug/kernel-ownership-publisher"
write_source '{"id":"fln-a","title":"a"}' '{"id":"fln-q","title":"q"}'
git add .beads/issues.jsonl
out=$(run_commit -q -m 'publisher broken' 2>&1); code=$?
check 'an unanswerable question refuses rather than passes' 1 'COULD NOT DECIDE' "$code" "$out"
mv "$LAB/publisher.real" "$LAB/target/debug/kernel-ownership-publisher"
republish; git add -A; run_commit -q -m 'recover' >/dev/null 2>&1

# --- case 6: a leftover candidate in the working tree ------------------------
write_source '{"id":"fln-a","title":"a"}' '{"id":"fln-b","title":"b"}' '{"id":"fln-new","title":"n"}' '{"id":"fln-x","title":"x"}'
republish
cp ci/KERNEL_CONTRACT_OWNERSHIP.jsonl ci/KERNEL_CONTRACT_OWNERSHIP.jsonl.candidate
git add .beads/issues.jsonl ci/KERNEL_CONTRACT_OWNERSHIP.jsonl
out=$(run_commit -q -m 'with a leftover candidate' 2>&1); code=$?
check 'a leftover candidate is refused' 1 'died mid-flight' "$code" "$out"
rm -f ci/KERNEL_CONTRACT_OWNERSHIP.jsonl.candidate
out=$(run_commit -q -m 'candidate cleared' 2>&1); code=$?
check 'the same commit is accepted once the candidate is gone' 0 '' "$code" "$out"

# --- case 7: removing the export entirely ------------------------------------
git rm --quiet --cached .beads/issues.jsonl
out=$(run_commit -q -m 'drop the export' 2>&1); code=$?
check 'removing the export is refused' 1 'cannot be derived from an absent source' "$code" "$out"
git reset --quiet

# --- case 8: the guard chains to an existing .git/hooks/pre-commit ------------
mkdir -p .git/hooks
printf '#!/bin/sh\necho CHAINED-GUARD-RAN >&2\nexit 7\n' > .git/hooks/pre-commit
chmod +x .git/hooks/pre-commit
echo chain >> README.md
git add README.md
out=$(run_commit -q -m 'chained' 2>&1); code=$?
# git reports 1 for ANY failed pre-commit hook, so the exit code cannot
# distinguish which hook refused. What proves the chain is that the other hook's
# output is present and this guard's refusal is not.
check 'a pre-existing .git/hooks/pre-commit still runs' 1 'CHAINED-GUARD-RAN' "$code" "$out"
if printf '%s' "$out" | grep -qF 'projection-guard: REFUSED'; then
    printf 'FAIL chaining: this guard refused instead of deferring\n%s\n' "$out"
    FAILS=$((FAILS + 1))
else
    printf 'ok   the chained hook decided, not this one\n'
    PASSES=$((PASSES + 1))
fi

# ...and it must still refuse on its own account before ever reaching the chain.
write_source '{"id":"fln-a","title":"a"}' '{"id":"fln-only-mine","title":"m"}'
git add .beads/issues.jsonl
out=$(run_commit -q -m 'stale, with a chained hook installed' 2>&1); code=$?
check 'a stale commit is refused by this guard even with a chain present' 1 'projection-guard: REFUSED' "$code" "$out"
if printf '%s' "$out" | grep -qF 'CHAINED-GUARD-RAN'; then
    printf 'FAIL chaining: the chain ran despite this guard refusing\n%s\n' "$out"
    FAILS=$((FAILS + 1))
else
    printf 'ok   a refusal short-circuits before the chain\n'
    PASSES=$((PASSES + 1))
fi
rm -f .git/hooks/pre-commit

printf '\n%s passed, %s failed\n' "$PASSES" "$FAILS"
[ "$FAILS" -eq 0 ]
