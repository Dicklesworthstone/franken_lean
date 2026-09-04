# Local source snapshots

Agents and reviewers that need an exact local build without a pre-existing clone can start from GitHub's repository archive and immediately bind the extracted tree to the public commit it represents.

## Current mainline snapshot

[Download the current `main` source archive](https://github.com/Dicklesworthstone/franken_lean/archive/refs/heads/main.tar.gz).

After extraction, record the live commit separately before treating any result as evidence:

```bash
git ls-remote https://github.com/Dicklesworthstone/franken_lean.git refs/heads/main refs/heads/master
sha256sum franken_lean-main.tar.gz
```

The archive is transport only. A verification receipt must state the resolved `main` commit, require `master` to resolve to the same commit, retain the archive SHA-256, and name the exact Rust toolchain and upstream Lean pin used. Do not infer a commit identity from the archive filename, filesystem timestamps, or a mutable branch name.

For reproducible long-lived evidence, replace `main` in the archive URL with the full 40-character commit SHA and retain that immutable URL in the receipt.
