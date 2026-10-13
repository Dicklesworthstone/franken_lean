#!/usr/bin/env bash
# Compile and validate the prepared native-instance implementation in two stages.
# No PR, force push, test relaxation, file deletion, or external runtime fallback.
set -euo pipefail

patches=scripts/patches/instance-selection
core=(crates/fln-elab/src/instances.rs crates/fln-elab/src/instances/scoped.rs)
frontend=(
  crates/fln-parse/src/command_scope/instances.rs
  crates/fln-parse/src/command_scope/instances/erasure.rs
  crates/fln/src/source_check.rs
  crates/fln/src/source_check/scopes.rs
  crates/fln/src/source_check/scopes/instance_erasure.rs
  crates/fln/src/source_check/instance_attributes.rs
  crates/fln/tests/source_instance_erasure.rs
)

git config user.name 'github-actions[bot]'
git config user.email '41898282+github-actions[bot]@users.noreply.github.com'

gate_core() {
  cargo test --locked -p fln-elab --lib -- --test-threads=2
  cargo check --locked -p fln --lib
  cargo clippy --locked -p fln-elab --lib -- -D warnings
}

gate_frontend() {
  cargo test --locked -p fln-parse --lib -- --test-threads=2
  cargo test --locked -p fln --lib source_check::scopes -- --test-threads=2
  cargo test --locked -p fln --test source_instance_erasure -- --test-threads=2
  cargo test --locked -p fln --test source_olean_instances -- --test-threads=2
  cargo check --locked --workspace --all-targets
  cargo clippy --locked -p fln-elab -p fln-parse -p fln --lib -- -D warnings
}

publish() {
  local gate=$1
  for attempt in 1 2 3; do
    git fetch origin main
    # If main advanced, replay this commit without overwriting concurrent work
    # and run the same gate again on the actual tree that will be published.
    if [[ $(git rev-parse origin/main) != $(git rev-parse HEAD^) ]]; then
      git rebase origin/main
      "$gate"
    fi
    if git push origin HEAD:main; then
      printf 'Published validated stage: %s\n' "$(git rev-parse HEAD)"
      if [[ -n ${GITHUB_STEP_SUMMARY:-} ]]; then
        printf 'Published validated stage: `%s`\n\n' "$(git rev-parse HEAD)" >> "$GITHUB_STEP_SUMMARY"
      fi
      return 0
    fi
  done
  echo 'Concurrent main updates prevented a normal fast-forward push.' >&2
  return 1
}

# Stage one: native availability and cache/index isolation. It compiles before
# the frontend knows about erasure, and lands only after its own tests pass.
git apply --check "$patches/0002-scoped-reuse.patch"
git apply "$patches/0002-scoped-reuse.patch"
git apply --check "$patches/0003-lexical-erasure.patch"
git apply "$patches/0003-lexical-erasure.patch"
rustfmt --edition 2024 --config skip_children=true "${core[@]}"
git diff --check
gate_core
git add -- "${core[@]}"
git commit -m 'feat(elab): implement snapshot-isolated lexical instance erasure' -m 'Reuse validated registry views, reset scope-specific indexes, preserve reducibility metadata, and restore erased candidates on later registrations without changing their original tie position. Native elaborator library tests, facade library compilation and strict elaborator library Clippy passed on this stage with the repository-pinned compiler.'
publish gate_core

# Stage two: the actual source command, atomic public/private scope handling,
# and executable source-to-council regression cells.
git apply --check "$patches/0004-source-erasure.patch"
git apply "$patches/0004-source-erasure.patch"
rustfmt --edition 2024 --config skip_children=true "${frontend[@]}"
git diff --check
gate_frontend
git add -- "${frontend[@]}"
git commit -m 'feat(lean): execute lexical instance-removal attributes' -m 'Implement attribute [-instance] through the parser and source driver, including scoped in wrappers, name and alias resolution, rollback, and separate public/private state. Parser and scope tests, source-instance-erasure and serialized-instance integration tests, workspace all-target compilation and strict library Clippy passed. These native/model gates do not claim pinned-Reference or full-workspace test parity.'
publish gate_frontend
