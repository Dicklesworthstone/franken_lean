# Native Lake boundaries

`lake build +Module:olean` now builds the checked `.olean` facet of a module
owned by a declared TOML or supported native Lean `lean_lib`. It reads the complete local source import
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

A package configured with `lakefile.lean` can use checked Lean definitions and
file-local notation to compute its source and build directories:

```lean
import Lake
open System Lake DSL

def sourceFolder (part : String) : FilePath := FilePath.mk ("sources/" ++ part)

package checked_proofs where
  srcDir := sourceFolder "lean"
  buildDir := FilePath.mk (".lake/" ++ "native")

@[default_target] lean_lib Proofs where
  srcDir := "library"
```

Here `lake build +Proofs:olean` reads `sources/lean/library/Proofs.lean` and
writes `.lake/native/lib/lean/Proofs.olean`. A library's default root is its
declared name, and `@[default_target]` selects the ordered default-target list.
Without explicit fields, package `srcDir` is `.`, `buildDir` is `.lake/build`,
and library `srcDir` is `.`. When both configuration files exist, TOML retains
precedence.

The native adapter handles `import Lake`, `package` and `lean_lib` itself.
It loads the real pinned `Init.System.FilePath` artifact closure using the
selected import posture; that closure must be available through `LEAN_PATH`
or the installed pinned toolchain. Every ordinary declaration and generated
field definition is checked before any configuration expression executes.
Fields have the actual `System.FilePath` type, including the imported String
coercion. Only the selected fields' String projections execute on Golem;
unused closed definitions are checked but are not evaluated. No upstream Lake
elaborator or loader executes, and no replacement logical FilePath is seeded.

This configuration slice supports the ordinary `import Lake` header,
top-level `package` and `lean_lib` after `open Lake DSL`, package `srcDir` and
`buildDir`, and library `srcDir`. Layout `where` fields and empty configurations
are supported. Additional imports, commands such as `require`, `lean_exe` or
scripts, other fields, custom roots, arbitrary declaration attributes,
same-line field separators, and trailing local `where` declarations are
explicitly refused. All configured directories must remain within the package.
Bad types, invalid later declarations, unsafe execution, or failed evaluation
prevent artifact publication.

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

Lean configurations additionally report their own checked import closure in
`configuration_imports[]`, separately from the compiled modules' `imports[]`.
This report is present even when every package module uses `prelude` and thus
has no external imports. `lake check-build --json` reports the configuration
closure as well.

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
facets, dependency fetching, custom globs, custom compiler options, Lake
configuration outside the slice above, new module-system artifact families, and native
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
closure) would rebuild. It elaborates and admits nothing, so this command still
requires a TOML configuration and explicitly refuses `lakefile.lean`.
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
`Lake/CLI/Help.lean` and `Lake/CLI/Main.lean`: load the configuration, then return
zero exactly when default build targets are specified. It does not build targets
or check package sources, freshness, or artifacts. Empty or omitted
`defaultTargets` stay empty; a package name is
not a default target. Human success is silent. The native JSON extension labels
its check `default-target-presence`. Additional target arguments are rejected.

The same checked native Lean configuration slice serves `check-build` and
`build`; unsupported configuration is never replaced with metadata guessed
from its directory name. Supported declarative `lakefile.toml` configuration
remains available. Malformed default-target array elements are rejected, not
silently filtered out.

`lake clean` removes the `buildDir` that `lakefile.toml` names, `.lake/build`
when it names none, and nothing else. A `buildDir` that is absolute, empty, or
leaves the package through `..` is refused with exit 1 and nothing is removed;
the pin removes whatever the configuration names, and this does not delete
outside the package on a configuration's say-so. A package configured only by
`lakefile.lean` gets exit 5, because its build directory is not known without
evaluating it; again nothing is removed.

`lake new NAME [TEMPLATE]` and `lake init [NAME] [TEMPLATE]` write the pin's
`std` template with a TOML configuration. When the pinned toolchain is
installed, `lake_new_writes_the_tree_the_pinned_lake_writes` in
`crates/fln-cli/tests/cli_personalities_and_verbs.rs` compares the tree with the
one the pinned `lake new` writes, byte for byte, apart from `lean-toolchain` and
`.git`. Another template or configuration language the pin knows (`exe`, `lib`,
`math-lax`, `math`; `.lean`) is refused with exit 5 before anything is created.
An unknown one gets the pin's own error and exit 1. Two things the pin does are
not done: no git repository is initialized, because git is spawned only to fetch
dependencies, and an existing `lean-toolchain` is left as it is.

`lake env` reports the sysroot from `LEAN_SYSROOT`, or from the toolchain layout
around the running binary. A binary outside a toolchain layout with
`LEAN_SYSROOT` unset gets exit 5 instead of an invented sysroot.

Installed-command tests in `crates/fln-cli/tests/lake_module_build.rs` inspect
every emitted artifact, import it into a separate downstream build, and check
proofs against the resulting artifact closure. Negative cases cover invalid
source, missing or cyclic imports, sibling-name leakage, unsupported facets and
settings, forged artifacts, source changes with preserved mtimes, output
preflight failures, symlinks, and source resource limits. Existing refusal and
build-provenance tests remain active.

`crates/fln-cli/tests/lake_lean_config.rs` exercises the installed binaries over
actual pinned FilePath imports: computed directories choose different source
trees, emitted artifacts decode and can be imported by a separate client, and
invalid configuration preserves previous outputs. The companion internal
configuration test bounds Golem instructions so accidentally evaluating an
unused ten-million-step computation fails, while the selected fields complete.
