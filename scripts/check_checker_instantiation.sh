#!/usr/bin/env bash
# Focused checker validation; supplements rather than replaces scripts/check.sh.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
out="${1:?usage: check_checker_instantiation.sh EVIDENCE_DIRECTORY}"
mkdir -p "$out"
{
    git rev-parse HEAD
    rustc -Vv
    cargo -V
} > "$out/source-and-toolchain.txt"
# Keep the exact large planning inputs readable alongside this source revision.
git archive --format=tar.gz --output="$out/planning-inputs.tar.gz" HEAD \
    AGENTS.md COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md \
    IMPLEMENTATION_STATUS.md .beads/issues.jsonl

# This environment may be the first one with the pinned formatter available.
# Preserve the exact formatting-only delta; tests below use these exact bytes.
rustfmt --edition 2024 crates/fln-checker/src/instantiate.rs
git diff --binary -- crates/fln-checker/src/instantiate.rs \
    crates/fln-checker/src/instantiate > "$out/format.patch"
tar -czf "$out/tested-instantiation-source.tar.gz" \
    crates/fln-checker/src/instantiate.rs crates/fln-checker/src/instantiate

cargo test --locked -p fln-checker --lib 2>&1 | tee "$out/library-tests.log"
cargo test --locked -p fln-checker 2>&1 | tee "$out/package-tests.log"
cargo clippy --locked -p fln-checker --lib -- -D warnings 2>&1 | tee "$out/clippy.log"
cargo check --locked --workspace --all-targets 2>&1 | tee "$out/workspace-check.log"
