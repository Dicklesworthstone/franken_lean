#!/usr/bin/env bash
# Provision the one currently linked FrankenSuite repository for clean CI builds.
# Cargo's relative path and SUITE.lock's commit are both authoritative.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.." && pwd -P)"
mapfile -t revisions < <(
  awk '$1 == "suite" && $2 == "asupersync" {
    for (i = 3; i <= NF; i++)
      if ($i ~ /^commit=/) print substr($i, 8)
  }' "$repo_root/SUITE.lock"
)
if [[ "${#revisions[@]}" -ne 1 ]] || [[ ! "${revisions[0]}" =~ ^[0-9a-f]{40}$ ]]; then
  echo "expected exactly one asupersync commit in SUITE.lock" >&2
  exit 2
fi
revision="${revisions[0]}"
dependency_root="$(dirname -- "$repo_root")/asupersync"

if [[ -e "$dependency_root" || -L "$dependency_root" ]]; then
  # Never reset or replace an existing developer checkout.
  if [[ -L "$dependency_root" || ! -d "$dependency_root/.git" ]]; then
    echo "asupersync must be a real Git checkout: $dependency_root" >&2
    exit 2
  fi
else
  git init --quiet "$dependency_root"
  git -c http.userAgent='franken_lean-agent (+https://github.com/Dicklesworthstone/franken_lean)' \
    -C "$dependency_root" fetch --depth=1 \
    https://github.com/Dicklesworthstone/asupersync.git "$revision"
  git -C "$dependency_root" checkout --quiet --detach "$revision"
fi

actual="$(git -C "$dependency_root" rev-parse --verify 'HEAD^{commit}')"
if [[ "$actual" != "$revision" ]]; then
  echo "asupersync checkout mismatch: $actual != $revision" >&2
  exit 2
fi
if [[ -n "$(git -C "$dependency_root" status --porcelain --untracked-files=normal)" ]]; then
  echo "asupersync checkout contains local changes: $dependency_root" >&2
  exit 2
fi
test -f "$dependency_root/Cargo.toml"
printf 'asupersync: %s at %s\n' "$actual" "$dependency_root"
