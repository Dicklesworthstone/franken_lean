#!/usr/bin/env bash
# Install this directory as the repository's hook path
# (bead franken_lean-projection-republish-mechanical-voz4).
#
# One command, idempotent, and safe to run from any pane. It sets
# core.hooksPath, which is per-clone rather than per-agent — and since every
# agent on this project works in the SAME clone, installing once covers the
# whole swarm. That is the property that makes the guard worth having: a hook
# each agent had to remember to install would reproduce the problem it exists
# to solve.
#
# core.hooksPath makes git ignore .git/hooks/ entirely. The pre-commit hook here
# chains to .git/hooks/pre-commit if one is present, so a guard installed there
# later — MCP Agent Mail's, most likely — keeps working.
#
# Uninstall with: git config --unset core.hooksPath

set -euo pipefail

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

hooks_relative='scripts/git-hooks'

if [ ! -x "$hooks_relative/pre-commit" ]; then
    printf 'install: %s/pre-commit is missing or not executable\n' "$hooks_relative" >&2
    exit 1
fi

current=$(git config --get core.hooksPath || true)
if [ "$current" = "$hooks_relative" ]; then
    printf 'install: already installed (core.hooksPath=%s)\n' "$current"
else
    if [ -n "$current" ]; then
        printf 'install: replacing core.hooksPath=%s\n' "$current"
    fi
    git config core.hooksPath "$hooks_relative"
    printf 'install: core.hooksPath=%s\n' "$hooks_relative"
fi

if [ -x '.git/hooks/pre-commit' ]; then
    printf 'install: .git/hooks/pre-commit exists and will still run (chained)\n'
fi

printf 'install: guarded — a commit changing .beads/issues.jsonl now needs a matching\n'
printf 'install:           ci/KERNEL_CONTRACT_OWNERSHIP.jsonl, or it is refused.\n'
