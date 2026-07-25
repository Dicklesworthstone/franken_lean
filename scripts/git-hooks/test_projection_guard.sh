#!/usr/bin/env bash
# Exercises the projection guard against a throwaway repo shaped like the real
# one. Every case asserts the exit code AND that the refusal names its own
# reason, so a guard that refused everything for one generic reason would fail
# here rather than look correct.
set -uo pipefail

[ "$#" -eq 5 ] || {
    printf 'usage: %s HOOK PUBLISHER VALIDATOR VERIFICATION_MANIFEST LIVE_TRACKER\n' "$0" >&2
    exit 2
}

# Resolved before the first `cd`: the harness runs inside a throwaway repo, so a
# relative path handed in from the caller's directory would silently miss and
# every guard case would "fail" for want of a hook rather than for a reason.
abspath() { (cd "$(dirname "$1")" && printf '%s/%s\n' "$(pwd)" "$(basename "$1")"); }
HOOK=$(abspath "$1")
PUBLISHER=$(abspath "$2")
VALIDATOR=$(abspath "$3")
VERIFICATION_MANIFEST=$(abspath "$4")
LIVE_TRACKER=$(abspath "$5")
[ -x "$HOOK" ] || { printf 'harness: %s is not an executable hook\n' "$HOOK" >&2; exit 2; }
[ -x "$PUBLISHER" ] || { printf 'harness: %s is not an executable publisher\n' "$PUBLISHER" >&2; exit 2; }
[ -f "$VALIDATOR" ] || { printf 'harness: %s is not a validator file\n' "$VALIDATOR" >&2; exit 2; }
[ -f "$VERIFICATION_MANIFEST" ] || {
    printf 'harness: %s is not a verification manifest\n' "$VERIFICATION_MANIFEST" >&2
    exit 2
}
[ -f "$LIVE_TRACKER" ] || { printf 'harness: %s is not a tracker export\n' "$LIVE_TRACKER" >&2; exit 2; }
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
mkdir -p \
    "$LAB/repo/.beads" \
    "$LAB/repo/ci" \
    "$LAB/repo/scripts" \
    "$LAB/repo/tools/structure-guard/kernel-ownership-publisher"
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

# This first lab isolates the projection law. Its prospective verification
# validator is deliberately a total pass fixture; the second lab below uses the
# real scripts/evidence.py and live adoption authority to exercise coverage.
printf '%s\n' \
    'import sys' \
    'if len(sys.argv) < 2 or sys.argv[1] != "validate-verification-manifest":' \
    '    raise SystemExit(2)' \
    'print("{\"schema\":\"fln.validation/1\",\"valid\":true}")' \
    > scripts/evidence.py
printf '%s\n' '{"fixture":"projection-only"}' > ci/VERIFICATION_MANIFEST.jsonl

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

# --- verification coverage: real validator over the prospective tree ---------
# This second lab starts from the repository's real frozen adoption authority.
# Unlike the projection-only fixture above, every refusal here comes from the
# checked-in validator that scripts/check.sh and cargo test also execute.
mkdir -p \
    "$LAB/coverage-repo/.beads" \
    "$LAB/coverage-repo/ci" \
    "$LAB/coverage-repo/scripts" \
    "$LAB/coverage-hooks" \
    "$LAB/coverage-target/debug"
cd "$LAB/coverage-repo" || exit 2
git init --quiet -b main .
git config user.email guard@test
git config user.name guard
git config core.hooksPath "$LAB/coverage-hooks"
cp "$HOOK" "$LAB/coverage-hooks/pre-commit"
chmod +x "$LAB/coverage-hooks/pre-commit"
cp "$PUBLISHER" "$LAB/coverage-target/debug/kernel-ownership-publisher"
cp "$VALIDATOR" scripts/evidence.py
cp "$VERIFICATION_MANIFEST" ci/VERIFICATION_MANIFEST.jsonl
cp "$LIVE_TRACKER" .beads/issues.jsonl
export CARGO_TARGET_DIR="$LAB/coverage-target"

coverage_republish() {
    "$LAB/coverage-target/debug/kernel-ownership-publisher" \
        --root . --wait-ms 30000 --robot >/dev/null
}

rewrite_tracker() {
    local bead_id=$1 bead_state=$2
    jq -c --arg bead "$bead_id" --arg state "$bead_state" \
        'if .id == $bead then .status = $state else . end' \
        .beads/issues.jsonl > .beads/issues.jsonl.next
    mv .beads/issues.jsonl.next .beads/issues.jsonl
}

canonicalize_manifest_with() {
    local extra_row=$1
    {
        jq -c . ci/VERIFICATION_MANIFEST.jsonl
        printf '%s\n' "$extra_row"
    } |
        jq -sSc '
            map(with_entries(
                if (.value | type) == "array" then .value |= sort else . end
            )) |
            sort_by(
                if .kind == "adoption" then [0, ""]
                elif .kind == "coverage" then [1, .bead]
                else [2, .scenario]
                end
            )[]
        ' > ci/VERIFICATION_MANIFEST.jsonl.next
    mv ci/VERIFICATION_MANIFEST.jsonl.next ci/VERIFICATION_MANIFEST.jsonl
}

# A real, currently valid tracker/manifest pair is the baseline.
coverage_republish
printf '%s\n' 'verification coverage prospective-tree harness' > README.md
git add \
    .beads/issues.jsonl \
    ci/KERNEL_CONTRACT_OWNERSHIP.jsonl \
    ci/VERIFICATION_MANIFEST.jsonl \
    scripts/evidence.py \
    README.md
out=$(run_commit -q -m 'coverage baseline' 2>&1); code=$?
check 'real verification coverage baseline is accepted' 0 '' "$code" "$out"

# A comment edits the tracker bytes but does not create a state obligation.
jq -c '
    if .id == "franken_lean-e5k7" then
        .comments = ((.comments // []) + [{
            "id": 999999999,
            "author": "guard-test",
            "text": "comment-only prospective-tree plant"
        }])
    else .
    end
' .beads/issues.jsonl > .beads/issues.jsonl.next
mv .beads/issues.jsonl.next .beads/issues.jsonl
out=$(run_commit -q -o .beads/issues.jsonl -m 'comment only' 2>&1); code=$?
check 'a comment-only tracker commit remains valid' 0 '' "$code" "$out"

# A new id with a fresh ownership projection but no verification row is the
# historical e5k7 failure: internally consistent projection, silently missing
# coverage. It must refuse for the coverage reason rather than the id-set reason.
printf '%s\n' '{"id":"franken_lean-hook-coverage-plant","status":"open"}' \
    >> .beads/issues.jsonl
coverage_republish
out=$(run_commit -q -o \
    .beads/issues.jsonl \
    ci/KERNEL_CONTRACT_OWNERSHIP.jsonl \
    -m 'new bead without coverage' 2>&1); code=$?
check 'a new bead without coverage is refused' 1 \
    'crossed the adoption boundary' "$code" "$out"
if printf '%s' "$out" | grep -qF 'projection-guard: REFUSED'; then
    printf 'FAIL new-bead coverage: projection guard masked the coverage reason\n%s\n' "$out"
    FAILS=$((FAILS + 1))
else
    printf 'ok   matching id projection reached the coverage authority\n'
    PASSES=$((PASSES + 1))
fi

planned_row='{"artifacts":[],"bead":"franken_lean-hook-coverage-plant","behavior_notes":["prospective-tree test fixture"],"boundary":[],"cancellation":[],"claim_ids":[],"claim_type":"bounded_model","error":[],"evidence_kind":"unit","failure_atomicity":[],"fault":[],"fuzz":[],"gate_ids":["W1"],"invariant_ids":[],"kind":"coverage","metamorphic":[],"mock_only":false,"mutation":[],"negative_recovery":[],"owner":"guard-test","parity_rows":[],"property":[],"requirement_ids":[],"resource":[],"scenarios":[],"schema":"fln.verification-manifest/2","skip":"none","unit":[],"workstream":"W1"}'
canonicalize_manifest_with "$planned_row"
out=$(run_commit -q -o \
    .beads/issues.jsonl \
    ci/KERNEL_CONTRACT_OWNERSHIP.jsonl \
    ci/VERIFICATION_MANIFEST.jsonl \
    -m 'new bead with planned coverage' 2>&1); code=$?
check 'a new bead with matching planned coverage is accepted' 0 '' "$code" "$out"

# Claiming the bead changes only the tracker. The same prospective judgment row
# remains valid because lifecycle is derived from the prospective tracker.
rewrite_tracker franken_lean-hook-coverage-plant in_progress
coverage_republish
out=$(run_commit -q -o \
    .beads/issues.jsonl \
    ci/KERNEL_CONTRACT_OWNERSHIP.jsonl \
    -m 'claim with derived coverage lifecycle' 2>&1); code=$?
check 'a claim needs no hand-maintained lifecycle transition' 0 '' "$code" "$out"

# A state field is now a defect, not a source of authority. Planting one must
# fail even when its value happens to match the tracker.
jq -c '
    if .kind == "coverage" and .bead == "franken_lean-hook-coverage-plant" then
        .state = "active"
    else .
    end
' ci/VERIFICATION_MANIFEST.jsonl > ci/VERIFICATION_MANIFEST.jsonl.next
mv ci/VERIFICATION_MANIFEST.jsonl.next ci/VERIFICATION_MANIFEST.jsonl
out=$(run_commit -q -o \
    ci/VERIFICATION_MANIFEST.jsonl \
    -m 'plant hand-maintained lifecycle' 2>&1); code=$?
check 'a hand-maintained lifecycle field is refused' 1 \
    'coverage shape differs' "$code" "$out"
jq -c '
    if .kind == "coverage" and .bead == "franken_lean-hook-coverage-plant" then
        del(.state)
    else .
    end
' ci/VERIFICATION_MANIFEST.jsonl > ci/VERIFICATION_MANIFEST.jsonl.next
mv ci/VERIFICATION_MANIFEST.jsonl.next ci/VERIFICATION_MANIFEST.jsonl

# Closing derives `complete`, but lifecycle derivation must not launder a
# sparse prospective row into terminal evidence. The close refuses until the
# bead owner supplies the human judgment fields.
rewrite_tracker franken_lean-hook-coverage-plant closed
coverage_republish
out=$(run_commit -q -o \
    .beads/issues.jsonl \
    ci/KERNEL_CONTRACT_OWNERSHIP.jsonl \
    -m 'close without complete judgment' 2>&1); code=$?
check 'a close without complete human judgment is refused' 1 \
    'requirement_ids must not be empty' "$code" "$out"
jq -c '
    if .kind == "coverage" and .bead == "franken_lean-hook-coverage-plant" then
        .artifacts = ["prospective-tree-complete-fixture"] |
        .boundary = ["prospective-tree-complete-boundary"] |
        .cancellation = ["prospective-tree-complete-cancellation"] |
        .claim_ids = ["HOOK-COVERAGE-COMPLETE"] |
        .error = ["prospective-tree-complete-error"] |
        .failure_atomicity = ["prospective-tree-complete-failure-atomicity"] |
        .gate_ids = ["W1"] |
        .negative_recovery = ["prospective-tree-complete-negative-recovery"] |
        .requirement_ids = ["HOOK-COVERAGE-COMPLETE"] |
        .resource = ["prospective-tree-complete-resource"] |
        .scenarios = ["quality_gate"] |
        .unit = ["prospective-tree-complete-unit"]
    else .
    end
' ci/VERIFICATION_MANIFEST.jsonl > ci/VERIFICATION_MANIFEST.jsonl.next
mv ci/VERIFICATION_MANIFEST.jsonl.next ci/VERIFICATION_MANIFEST.jsonl
out=$(run_commit -q -o \
    .beads/issues.jsonl \
    ci/KERNEL_CONTRACT_OWNERSHIP.jsonl \
    ci/VERIFICATION_MANIFEST.jsonl \
    -m 'close with complete judgment' 2>&1); code=$?
check 'a close with complete human judgment is accepted' 0 '' "$code" "$out"

# If the prospective validator itself cannot run, fail closed. The invalid
# script is never committed; restoring the fixture makes the worktree clean.
cp scripts/evidence.py "$LAB/coverage-validator.saved"
printf '%s\n' 'raise SystemExit("planted validator failure")' > scripts/evidence.py
out=$(run_commit -q -o scripts/evidence.py -m 'invalid validator' 2>&1); code=$?
check 'an invalid prospective validator refuses rather than passes' 1 \
    'planted validator failure' "$code" "$out"
mv "$LAB/coverage-validator.saved" scripts/evidence.py

printf '\n%s passed, %s failed\n' "$PASSES" "$FAILS"
[ "$FAILS" -eq 0 ]
