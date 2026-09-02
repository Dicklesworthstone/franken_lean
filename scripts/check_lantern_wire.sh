#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd "$repo_root"

printf '==> Lantern wire: format\n'
cargo fmt --all -- --check

printf '==> Lantern wire: all fln-server targets\n'
cargo test --locked -p fln-server --all-targets --no-fail-fast

printf '==> Lantern wire: external tool boundaries\n'
cargo test --locked -p fln-server --test lsp_replay_cli --test lsp_validate_cli --test lsp_inspect_cli

printf '==> Lantern wire: model boundaries\n'
cargo test --locked -p fln-server --test transport_fragmentation --test modular_protocol_foundations

printf '==> Lantern wire: lint\n'
cargo clippy --locked -p fln-server --all-targets -- -D warnings

printf '==> Lantern wire: diff integrity\n'
git diff --check

printf 'Lantern wire gate passed.\n'
