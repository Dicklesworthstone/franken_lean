#!/usr/bin/env bash
# marrow_sanitizer_guard.sh — the TWO-DETECTOR concurrency guard for Marrow
# (bead fln-nhf5; plan §18 "fault & recovery drills", D3 unsafe posture).
#
# WHY TWO DETECTORS AND NOT THE BETTER ONE. Neither subsumes the other, so a
# single detector agreeing with itself certifies nothing about what it cannot
# see. Miri interprets the program and finds UB that never misbehaves on this
# hardware — which is exactly the class the defect at commit 8cd1d3b belonged
# to, since aligned 32-bit loads do not tear, so no ordinary test could observe
# it. ThreadSanitizer runs real OS threads, the real allocator, and the syscalls
# Miri refuses, and reports what the schedule actually produced. Running one
# because it is stricter, or the other because it is faster, is choosing which
# half of the evidence to discard. This is B3's two-engines argument one layer
# down, applied to detectors instead of kernels.
#
# WHAT IT COVERS, stated so it is not read as broader than it is: the four tests
# in fln-unsafe-abi and fln-rt that actually spawn threads or contend on a
# shared artifact. NOT the whole crate — the other 38 tests are layout and codec
# assertions with no threads, and under Miri they exceed ten minutes and buy
# nothing. NOT fln-unsafe-region's mmap primitive (Miri cannot execute mmap).
# NOT the exported C surface under a real C caller; the stage0 ABI gauntlet is
# that instrument.
#
# THE TRAP THIS SCRIPT EXISTS TO NOT FALL INTO. ThreadSanitizer reports at
# process teardown, AFTER libtest has printed its verdict. On a real data race
# the output contains
#     test tests::mark_mt_negates_and_atomics_conserve ... ok
#     test result: ok. 1 passed; 0 failed; ...
# and the process then exits 66. A lane that greps for `test result: ok`, or
# reads the last line, reports a clean run while a race was detected and
# printed. THE EXIT CODE IS THE ONLY RELIABLE SIGNAL, and every check below is
# on the exit status. Measured on 2026-07-25 against the real crate with the
# dec_ref mode probe reverted to its pre-8cd1d3b `ptr::read`.
#
# Usage:
#   scripts/tribunal/marrow_sanitizer_guard.sh            # both detectors
#   scripts/tribunal/marrow_sanitizer_guard.sh miri       # one of them
#   scripts/tribunal/marrow_sanitizer_guard.sh tsan
# Exit 0 = every lane ran its named test and reported no finding.
# Exit 1 = a detector reported a finding, or a lane failed to run.
# Exit 2 = setup could not be established (missing component, no toolchain).
#          Typed separately because "we could not look" is not "we looked and
#          found nothing" (FL-INV-07).

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RUN_ID="marrow-sanitizer-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_DIR="$ROOT/target/e2e/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
mkdir -p "$(dirname "$ART_DIR")"
if ! mkdir "$ART_DIR" 2>/dev/null; then
  echo "[marrow_sanitizer_guard] setup failure: evidence directory already claimed: $ART_DIR" >&2
  exit 2
fi

TOOLCHAIN="$(sed -n 's/^channel = "\(.*\)"$/\1/p' "$ROOT/rust-toolchain.toml")"
TARGET="x86_64-unknown-linux-gnu"

# The sanitizer build must NOT share the workspace target directory:
# `-Zsanitizer=thread` invalidates every artifact built without it, so sharing
# would force a full rebuild for the next pane and another when they rebuild
# without it. Miri likewise keeps its own.
SAN_TARGET_DIR="${FLN_SANITIZER_TARGET_DIR:-$ROOT/target/sanitizer}"

emit() { printf '%s\n' "$1" >>"$LOG"; }
say() { printf '[marrow-sanitizer] %s\n' "$1" >&2; }

emit "{\"schema\":\"fln.marrow-sanitizer-guard/1\",\"event\":\"run_start\",\"run_id\":\"$RUN_ID\",\"toolchain\":\"$TOOLCHAIN\",\"target\":\"$TARGET\"}"

setup_failure() {
  say "SETUP FAILURE: $1"
  emit "{\"schema\":\"fln.marrow-sanitizer-guard/1\",\"event\":\"run_end\",\"verdict\":\"inconclusive\",\"reason\":\"$1\"}"
  exit 2
}

require_component() {
  rustup component list --toolchain "$TOOLCHAIN" 2>/dev/null \
    | grep -q "^$1.*(installed)" \
    || setup_failure "component_${1}_absent_for_pin"
}

FAILED=0
RAN=0

# Runs one detector lane. `$1` label, `$2` the EXACT test name that must appear
# as having run — a filter matching nothing also exits 0, so the exit code alone
# is not sufficient to prove a lane did anything.
#
# Exact, not a prefix: the first version of this passed the cargo FILTER as the
# expected name, and `concurrent_publication` is a prefix of
# `concurrent_publication_of_one_target_never_yields_a_mixture`, so the lane ran
# correctly and the guard reported `ran=no`. A guard that cannot tell "did not
# run" from "I do not recognise the name it ran under" is a guard that will be
# widened the first time it fires.
run_lane() {
  local label="$1" expect="$2"
  shift 2
  local out="$ART_DIR/$label.out"
  local start=$SECONDS
  "$@" >"$out" 2>&1
  local rc=$?
  local wall=$((SECONDS - start))
  local findings
  findings=$(grep -cE 'WARNING: ThreadSanitizer|error: Undefined Behavior' "$out" || true)
  local ran="no"
  grep -qE "^test .*${expect} \.\.\. ok" "$out" && ran="yes"
  RAN=$((RAN + 1))
  if [[ $rc -ne 0 || "$ran" != "yes" ]]; then
    FAILED=$((FAILED + 1))
    say "FAIL $label exit=$rc ran=$ran findings=$findings ($out)"
  else
    say "ok   $label exit=0 ran=yes findings=$findings wall=${wall}s"
  fi
  emit "{\"schema\":\"fln.marrow-sanitizer-guard/1\",\"event\":\"lane\",\"label\":\"$label\",\"exit\":$rc,\"executed\":\"$ran\",\"findings\":$findings,\"wall_s\":$wall}"
}

run_miri() {
  require_component miri
  export MIRIFLAGS="-Zmiri-disable-isolation -Zmiri-ignore-leaks"
  # -Zmiri-disable-isolation: the region publication test is ABOUT a real
  #   filesystem rename and cannot be stubbed.
  # -Zmiri-ignore-leaks: mt_object_dies_on_last_dec enables the ownership
  #   shadow, which QUARANTINES freed memory by design; Miri's leak checker
  #   correctly reports that intentional retention.
  run_lane miri_mt_stress mark_mt_negates_and_atomics_conserve \
    cargo "+$TOOLCHAIN" miri test -p fln-unsafe-abi --lib mark_mt_negates_and_atomics_conserve
  run_lane miri_mt_dies mt_object_dies_on_last_dec \
    cargo "+$TOOLCHAIN" miri test -p fln-unsafe-abi --lib mt_object_dies_on_last_dec
  run_lane miri_rc_balance rc_clone_and_drop_balance \
    cargo "+$TOOLCHAIN" miri test -p fln-unsafe-abi --lib rc_clone_and_drop_balance
  run_lane miri_publication concurrent_publication_of_one_target_never_yields_a_mixture \
    cargo "+$TOOLCHAIN" miri test -p fln-rt --test region_engine concurrent_publication
  unset MIRIFLAGS
}

run_tsan() {
  require_component rust-src
  export CARGO_TARGET_DIR="$SAN_TARGET_DIR"
  export RUSTFLAGS="-Zsanitizer=thread"
  export RUSTDOCFLAGS="-Zsanitizer=thread"
  # -Zbuild-std rebuilds std under the same sanitizer. Without it cargo refuses
  # with "mixing -Zsanitizer will cause an ABI mismatch", which is what made
  # TSAN look unavailable at this pin until rust-src was installed for it.
  run_lane tsan_mt_stress mark_mt_negates_and_atomics_conserve \
    cargo "+$TOOLCHAIN" test -Zbuild-std --target "$TARGET" \
      -p fln-unsafe-abi --lib mark_mt_negates_and_atomics_conserve
  run_lane tsan_mt_dies mt_object_dies_on_last_dec \
    cargo "+$TOOLCHAIN" test -Zbuild-std --target "$TARGET" \
      -p fln-unsafe-abi --lib mt_object_dies_on_last_dec
  run_lane tsan_rc_balance rc_clone_and_drop_balance \
    cargo "+$TOOLCHAIN" test -Zbuild-std --target "$TARGET" \
      -p fln-unsafe-abi --lib rc_clone_and_drop_balance
  run_lane tsan_publication concurrent_publication_of_one_target_never_yields_a_mixture \
    cargo "+$TOOLCHAIN" test -Zbuild-std --target "$TARGET" \
      -p fln-rt --test region_engine concurrent_publication
  unset RUSTFLAGS RUSTDOCFLAGS CARGO_TARGET_DIR
}

cd "$ROOT" || setup_failure "cannot_enter_repository_root"
command -v cargo >/dev/null || setup_failure "cargo_absent"
[[ -n "$TOOLCHAIN" ]] || setup_failure "toolchain_pin_unreadable"

# ANTI-RUBBER-STAMP. A guard that cannot fail is a green light with extra
# steps, and the two ways THIS one could silently stop guarding are: a lane that
# exits non-zero being read as fine, and a lane whose filter matches nothing
# being read as a pass. `--self-test` plants both and requires each to be
# reported as a failure. It costs one cargo invocation and no sanitizer build.
#
# The second case is not hypothetical — the first version of this script hit it
# for real, with a prefix-vs-exact name mismatch, and reported ran=no on a lane
# that had run correctly. That is the check working; this makes it standing.
self_test() {
  local before_failed=$FAILED
  run_lane selftest_filter_matches_nothing this_test_name_does_not_exist_anywhere \
    cargo "+$TOOLCHAIN" test -p fln-unsafe-abi --lib this_test_name_does_not_exist_anywhere
  local after_nothing=$FAILED
  run_lane selftest_command_fails mark_mt_negates_and_atomics_conserve \
    cargo "+$TOOLCHAIN" test -p fln-unsafe-abi --lib --no-such-flag
  local after_fail=$FAILED

  if [[ $after_nothing -ne $((before_failed + 1)) ]]; then
    say "SELF-TEST FAILED: a filter matching NOTHING was not reported as a failure"
    emit "{\"schema\":\"fln.marrow-sanitizer-guard/1\",\"event\":\"run_end\",\"verdict\":\"fail\",\"reason\":\"self_test_empty_filter_not_caught\"}"
    exit 1
  fi
  if [[ $after_fail -ne $((after_nothing + 1)) ]]; then
    say "SELF-TEST FAILED: a non-zero exit was not reported as a failure"
    emit "{\"schema\":\"fln.marrow-sanitizer-guard/1\",\"event\":\"run_end\",\"verdict\":\"fail\",\"reason\":\"self_test_nonzero_exit_not_caught\"}"
    exit 1
  fi
  say "VERDICT pass — self-test: both planted failures were reported as failures"
  emit "{\"schema\":\"fln.marrow-sanitizer-guard/1\",\"event\":\"run_end\",\"verdict\":\"pass\",\"reason\":\"self_test_discriminates\"}"
  exit 0
}

case "${1:-both}" in
  miri) run_miri ;;
  tsan) run_tsan ;;
  both) run_miri; run_tsan ;;
  --self-test) self_test ;;
  *) setup_failure "unknown_detector_${1}" ;;
esac

if [[ $RAN -eq 0 ]]; then
  setup_failure "no_lane_executed"
fi

if [[ $FAILED -ne 0 ]]; then
  say "VERDICT fail — $FAILED of $RAN lanes reported a finding or did not run"
  emit "{\"schema\":\"fln.marrow-sanitizer-guard/1\",\"event\":\"run_end\",\"verdict\":\"fail\",\"lanes\":$RAN,\"failed\":$FAILED}"
  exit 1
fi

say "VERDICT pass — $RAN lanes, every one executed its named test, no findings"
emit "{\"schema\":\"fln.marrow-sanitizer-guard/1\",\"event\":\"run_end\",\"verdict\":\"pass\",\"lanes\":$RAN,\"failed\":0}"
exit 0
