# Native Lake boundaries

`lake build +Module:olean` now builds the checked `.olean` facet of a module
owned by a declared TOML `lean_lib`. It reads the complete local source import
closure, checks modules in dependency order through K1 and the independent
checker, and emits one pinned-format artifact per module. Each artifact contains
only that module's declarations and its actual imports. Source seeds and full
environment snapshots are never substituted for module products.

The output directory is `buildDir/lib/lean`, normally `.lake/build/lib/lean`.
Package `srcDir`, library `srcDir`, and library `roots` determine source paths.
Modules outside the requested import closure are not compiled. A module can be
selected without `+` when its name does not also name a declared target.

This example builds without an installed Reference toolchain: `prelude` makes
the files' lack of implicit `Init` explicit, and all declarations use the core
type theory.

```sh
mkdir -p Proofs
cat > lakefile.toml <<'EOF'
name = "checked_proofs"
defaultTargets = ["Proofs"]

[[lean_lib]]
name = "Proofs"
EOF
cat > Proofs/Base.lean <<'EOF'
prelude
def Proofs.identity (A : Type) (a : A) : A := a
theorem Proofs.keep (P : Prop) (h : P) : P := h
EOF
cat > Proofs.lean <<'EOF'
prelude
import Proofs.Base
def Proofs.again (A : Type) (a : A) : A := Proofs.identity A a
EOF

lake build +Proofs:olean
fln olean inspect --constants .lake/build/lib/lean/Proofs/Base.olean
fln olean inspect --constants .lake/build/lib/lean/Proofs.olean

# Check a downstream source against the emitted artifacts, not the source files.
mkdir -p consumer
cat > consumer/Use.lean <<'EOF'
prelude
import Proofs
theorem imported (P : Prop) (h : P) : P := Proofs.keep P h
EOF
LEAN_PATH="$PWD/.lake/build/lib/lean" fln check-source consumer/Use.lean
```

External imports are read from `LEAN_PATH`, or the pinned toolchain's `lib/lean`
when that variable does not supply a search path. Their entire `.olean` closure
is admitted again by both checkers. Every source file without `prelude` requires
the real `Init` import; absence or rejection of that dependency fails the build.
External dependencies can be inherited through local source imports. Builds
whose source modules require different external environments currently refuse
instead of exposing an unrelated sibling's imports.

Builds always recheck the current input bytes. Existing output files, their
timestamps, and old placeholder contents never authorize a cache hit. A source
edit with its old mtime restored still rebuilds. The JSON report uses
`fln.lake-build/2`, identifies the `olean` facet, lists the emitted paths, and
reports `modules_cached: 0`.

All selected module closures must finish checking and encoding before output
replacement starts. Parse, elaboration, kernel, import, and encoding failures
leave prior artifacts unchanged. Output destinations are preflighted; successful
file replacements use the existing atomic writer, with rollback on ordinary
publication errors. This is not a crash-atomic multi-file generation protocol.
A publication lock serializes native builders; an interrupted publication can
leave that lock and requires inspection before retrying. A failed rollback is
reported explicitly. Source and output symlinks are refused.

The current limits are 64 KiB of configuration, 1 MiB of source, 256 source
modules, 4,096 import rows, and 64 MiB of emitted artifacts. Compiler and checker
work also use the ordinary bounded source-check budgets. Resource exhaustion
is reported as non-authoritative failure, never as successful compilation.

Bare `lake build` of a library still refuses: its default `leanArts` facet also
requires products such as `.ilean` and compiler outputs. Executable/native
facets, dependency fetching, custom globs, custom compiler options, executable
`lakefile.lean` configuration, new module-system artifact families, and native
extension metadata without a pinned export encoding remain unsupported.
Unsupported TOML build settings are rejected rather than silently ignored.
These boundaries are not full Lake compatibility, fresh-artifact byte identity
with the Reference, or a claim that the Lake convergence bead is complete.

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

Installed-command tests in `crates/fln-cli/tests/lake_module_build.rs` inspect
every emitted artifact, import it into a separate downstream build, and check
proofs against the resulting artifact closure. Negative cases cover invalid
source, missing or cyclic imports, sibling-name leakage, unsupported facets and
settings, forged artifacts, source changes with preserved mtimes, output
preflight failures, symlinks, and source resource limits. Existing refusal and
build-provenance tests remain active.
