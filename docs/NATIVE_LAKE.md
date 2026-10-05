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
when that variable does not supply a search path. How their `.olean` closure
reaches the environment is the import posture (bead `fln-uyuz`), and every
report names it per closure (`import_posture`, and `imports[]` with `trust`,
`admission`, `closureKey`, `record`, `recordWrite`):

- `--import-posture reuse-verified`, the default here, for `fln check-source`, and
  for editor sessions (`fln serve-lsp`, `lean --server`; see
  NATIVE_EDITOR_PROOFS.md).
  The closure is keyed by one digest over every byte of every imported part, the
  import roots, the options and the running binary's own bytes. If this binary
  admitted those exact bytes before, its record is read back, the closure is
  rebuilt from the bytes, and it is used only if it reaches every logical root
  that admission reached (each module's, the declarations', and the result after
  metadata); otherwise both checkers admit it and the admission is recorded.
  Records live in `FLN_IMPORT_REUSE_DIR`, else `$XDG_CACHE_HOME/fln/import-reuse`,
  else `~/.cache/fln/import-reuse`. A record is a cache over a council admission,
  as trustworthy as the store it sits in; this is D6's single named carve-out.
- `--import-posture recheck` admits the whole closure again with both checkers
  and never reads or writes a record. `fln check-olean`, its `--continue` frontier
  and its receipts take no posture at all: G1 evidence is always `recheck`.
- `trust-producer` (plan §7.2) is refused as not implemented.

Every source file without `prelude` requires
the real `Init` import; absence or rejection of that dependency fails the build.
External dependencies can be inherited through local source imports. Builds
whose source modules require different external environments currently refuse
instead of exposing an unrelated sibling's imports.

Source modules are reused across builds by content, under the same posture
(bead `franken_lean-z8j.1.1`). Under `reuse-verified`, every module a successful
build elaborates leaves a record in the record directory's `source-modules/`.
The record is keyed by one digest over:
- the running binary's identity;
- the options;
- the logical root of the external import world;
- the module's name and source bytes;
- the ordered steps that build its imported environment, each local dependency
  named by the logical root of its checked environment.

A later build that reaches a module with that exact key re-admits the module from
its record instead of elaborating it:
- the recorded artifact's declarations are planned as `fln check-olean` plans
  them;
- both checkers admit them onto the module's real imported environment, which
  must have the recorded root;
- the recorded journal rows are replayed, and the result must reach the
  recorded root;
- re-encoding the result must give the recorded artifact byte for byte.

Any other record is refused by name (`refused:seal`, `refused:key`,
`refused:result-root`, ...): a damaged or misfiled record, one from another
binary, or one that fails any of those checks. The module is then elaborated
and its record rewritten. So:
- a no-op build, or a build after an mtime-only touch, elaborates nothing;
- a body edit elaborates the edited module and every module whose imported
  environment changed with it;
- an edit that leaves a module's checked declarations unchanged, such as a
  comment, elaborates that module only;
- a source edit with its old mtime restored still rebuilds.

Existing output files, their timestamps and old placeholder contents never take
part: a hit republishes the re-encoded artifact without reading the build
directory.

Re-admission does not show that the recorded declarations are the ones the
source elaborates to. Like an import record, a module record is only as
trustworthy as the store it sits in. Re-admission also still needs the module's
imported environment, so a module under the implicit `Init` pays for the reused
`Init` closure even when nothing changed. `--import-posture recheck` elaborates
every module and reads and writes no record.

The JSON report uses `fln.lake-build/2`, identifies the `olean` facet, and lists
the emitted paths. It also reports:
- `modules_cached`: modules re-admitted from records;
- `module_elaborations`;
- `module_checks_reused`: modules reused from an earlier target of the same
  invocation;
- `module_records`: `on`, `off`, or `unavailable` with
  `module_records_reason`;
- `modules[]`: each module's `decision` (`elaborated`, `cached` or
  `reused-in-session`), `key`, `record` lookup and `recordWrite`.

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

Every successful build writes a snapshot, `buildDir/fln-build.snapshot` (bead
`franken_lean-z8j.1.2`). For every module it records the source path and content
hash, the ordered imports, the output path and content hash, the record key and
the decision. It also records the content hash of every external `.olean` in the
closure, with that module's imports. The report says `"snapshot":"written"`, or
`"failed"` with `snapshot_reason`; a failed write does not fail a published
build. A failed build leaves the last successful snapshot in place. No build
reads the snapshot: module reuse is decided by the record store alone.

`fln build explain [--dir D] [--json] [MODULE]` compares that snapshot with the
current tree and reports why each module of the recorded build (or of `MODULE`'s
closure) would rebuild. It elaborates and admits nothing.
- The Reference decision follows Lake's file-cone model. A module rebuilds when
  its source bytes, its ordered imports, or the bytes of an external `.olean` in
  its import cone changed, or when a local import rebuilds.
- A missing output rebuilds that module alone. A changed output is listed under
  changed outputs and changes no decision.
- Each changed input is named with its old and new content hashes.
- The native decision is reported as `unavailable (no Ledger records)`: it would
  need Ledger demand records, which do not exist.

Source timestamps, output presence and the text of a file (comments,
`axiom `, `-- fln-interface-change`) never decide anything: only which files'
bytes changed. `--faithful-invalidation` is accepted and changes nothing,
because the Reference decision is already the file-cone model.

Exit codes: 0 with a decision. 5 when no snapshot exists, or when the decision
cannot be computed because an input cannot be read; the report then says which,
with status `incomplete` and decision `unknown`. 1 for a malformed snapshot or a
module outside the recorded build. JSON uses `fln.build-explain/2`.

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
