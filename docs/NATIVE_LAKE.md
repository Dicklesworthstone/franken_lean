# Native Lake boundaries

`lake build` currently has no connected artifact compiler or module publisher.
It returns a nonzero unsupported result without creating output directories,
writing placeholder `.olean` files, or accepting existing files as cached builds.
Old placeholder files are not deleted or replaced. A successful source check or
an import-free environment snapshot is not a Lake module build.

`fln build explain` also returns a nonzero unsupported result. No recorded,
content-bound build provenance currently connects this command to the Ledger.
Source timestamps, output presence, and `-- fln-interface-change` comments cannot
establish cache validity or semantic early cutoff. No Reference or native rebuild
decision is invented, including with `--faithful-invalidation`. JSON diagnostics
use status `unsupported` and contain no build counts or cache outcomes.

`lake check-build` has the narrow meaning in the pinned Reference's
`Lake/CLI/Help.lean` and `Lake/CLI/Main.lean`: return zero exactly when default
build targets are specified. It does not check target validity, source, freshness,
or artifacts. Empty or omitted `defaultTargets` stay empty; a package name is
not a default target. Human success is silent. The native JSON extension labels
its check `default-target-presence`. Additional target arguments are rejected.

Executable `lakefile.lean` configuration is not implemented and is refused, not
replaced with metadata guessed from its directory name. Supported declarative
`lakefile.toml` configuration remains available. Malformed default-target array
elements are rejected, not silently filtered out.

These restrictions remove false successes; they do not complete the artifact
compiler, content-addressed build records, dependency installation, or Reference
Lake compatibility. Regression tests invoke the installed commands on invalid
source, absent targets, forged outputs, and changed source with existing outputs,
and require non-success plus byte-for-byte preservation of prior artifacts.
