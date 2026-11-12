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

Checked source simp registrations can accompany those artifacts. The supported
slice includes forward equality theorems and unfolding for definitions marked
`reducible` before their simp registration. The artifact retains each rule's
priority, discrimination keys and reflexivity flags as they were at registration
time. Later reducibility changes do not rewrite an earlier registration; adding
the attribute again captures the new state. Each module exports its own additions,
including when dependencies form a diamond or a build reuses persisted records.

An ordinary definition may need generated, checked equation theorems before its
simp registration can be exported. That generation, reverse or non-equality
rules needing auxiliary proofs, erasures, and imported-theorem re-registration
remain unsupported in this artifact path. Unsupported indexing or exhausted
metadata budgets also refuse artifact production. These export limits do not
remove existing native source simp support, and metadata never substitutes for
checking the underlying declarations.

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
file-local notation to compute its source directories, build directory, and
library module roots:

```lean
import Lake
open System Lake DSL

def sourceFolder (part : String) : FilePath := FilePath.mk ("sources/" ++ part)
def libraryRoots (suffix : String) : Array Lean.Name :=
  #[Lean.Name.str Lean.Name.anonymous ("Pro" ++ suffix), `Support]

package checked_proofs where
  srcDir := sourceFolder "lean"
  buildDir := FilePath.mk (".lake/" ++ "native")

@[default_target] lean_lib Bundle where
  srcDir := "library"
  roots := libraryRoots "ofs"
```

Here `lake build +Proofs:olean` reads `sources/lean/library/Proofs.lean` and
writes `.lake/native/lib/lean/Proofs.olean`. The same library also owns `Support`
and its submodules. Its declared name `Bundle` is not an additional root.
Without a `roots` field, a library's default root is its declared name; an
explicit `roots := #[]` instead leaves it with no roots. Root order and
duplicates are preserved. `@[default_target]` selects the ordered default-target list.
Without explicit fields, package `srcDir` is `.`, `buildDir` is `.lake/build`,
and library `srcDir` is `.`. When both configuration files exist, TOML retains
precedence.

The native adapter handles `import Lake`, `package`, `lean_lib`, and `lean_exe` itself.
It loads the real pinned `Init.System.FilePath` artifact closure using the
selected import posture; that closure must be available through `LEAN_PATH`
or the installed pinned toolchain. Every ordinary declaration and generated
field definition is checked before any configuration expression executes.
Directory fields have the actual `System.FilePath` type, including the imported
String coercion; library `roots` has type `Array Lean.Name`, and executable
`root` has type `Lean.Name`. Only the selected directory fields' String
projections and structural name projections execute on Golem;
unused closed definitions are checked but are not evaluated. No upstream Lake
elaborator or loader executes, and no replacement logical FilePath is seeded.
Names are read component by component, so the single quoted component `«A.B»`
cannot become the hierarchical module `A.B`. Anonymous names, numeric components,
and components containing dots, path separators, or other unsupported characters
are refused. Each roots field is bounded to 256 names, 128 components per name,
and 64 KiB of aggregate returned text. Execution budget exhaustion remains
inconclusive rather than being accepted as an empty configuration.

This configuration slice supports the ordinary `import Lake` header,
top-level `package`, `lean_lib`, and `lean_exe` after `open Lake DSL`, package
`srcDir` and `buildDir`, library `srcDir` and `roots`, and executable `srcDir`
and `root`. An executable's default root is its target name. Executable targets
must have distinct roots, even when their source directories differ.
`@[default_target]` also accepts executable targets. Layout `where` fields and
empty configurations are supported. Additional imports, commands such as
`require` or scripts, other fields, arbitrary declaration attributes,
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
  import roots, the options and the admission authority: a build-time digest of
  the kernel, checker and decoder crates and the toolchain the binary was built
  from (`fln_admission::AUTHORITY`), so a rebuild that changes only the
  elaborator keeps its records. If a binary with that authority admitted those
  exact bytes before, its record is read back, the closure is
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

### Running declared executables

`lake exe TARGET [ARGS...]` and its `lake exec` alias run a declared
`lean_exe` through the checked native Golem pipeline. The target may come from
`lakefile.toml` or the supported typed `lakefile.lean` configuration slice.
The entry source path combines package `srcDir`, target `srcDir`, and the
target's exact hierarchical root module name.

For example:

```toml
name = "native_program"
srcDir = "src"

[[lean_exe]]
name = "runner"
root = "App.Main"
srcDir = "application"
```

Place this program in `src/application/App/Main.lean`:

```lean
def main (args : List String) : IO UInt32 := do
  for value in args do
    IO.println value
  pure 7
```

With the pinned imports available, `lake exe runner --help "" "hello world"`
passes those three arguments to the program and preserves its nonzero status.
Every word after the target belongs to the program, including `--`, option-like
arguments, empty strings, and Unicode. Lake options, including `--dir`,
`--jobs`, `--import-posture`, `--fln-max-steps`, and `--fln-max-frames`, must
precede the target. Invalid UTF-8 and oversized argv are refused before any
Lean configuration is evaluated.

Local dependencies must belong to declared libraries with their configured
roots and source directories. Loose source files and other executable targets
do not become ambient libraries. The captured source closure goes through the
same import admission, module checking, and `main` contract as `lean --run`.
Implicit `Init` is loaded for ordinary files. Changes to local dependencies
are checked on the next invocation. A failed dependency prevents `main` from
running; completed frontend output precedes the single `main` invocation.

TOML executables can also use libraries from local packages. For example, the
root package can declare a sibling whose own `lakefile.toml` declares a
`Shared` library:

```toml
[[require]]
name = "shared"
path = "../shared"
```

An executable can then `import Shared` through the dependency's configured
package and library source directories. Local requirements are resolved
transitively before source checking. The resolver matches the pin's reverse
breadth-first selection: a package name selected earlier keeps its chosen path
when another requirement names it. Diamonds share that selection. The
requirement name determines package identity; a different `name` in the
dependency's own TOML does not rename it. Package dependency cycles and modules
claimed by distinct source owners are refused before `main` runs.

Each source path remains confined to its owning package; explicitly naming a
sibling dependency does not permit a package's `srcDir` to escape its root.
Resolution is bounded to 64 packages and 4096 declared requirement edges, in
addition to the executable source-closure limits. This initial local-package
path requires TOML configurations without existing `lake-manifest.json` or
`.lake/package-overrides.json` files. These files, Lean dependency
configurations, and non-path requirements are explicitly refused rather than
silently ignored. Resolution writes no manifest or build artifacts.

Local package requirements currently apply to `exe` and `exec`; artifact
builds and `build explain` retain their explicit dependency-resolution refusal.

Supported entry types are `IO Unit`, `IO UInt32`, and either of those with
one `List String` argument. Existing compiler, runtime-capability, and resource
limits still apply. VM exhaustion remains an inconclusive result.

This route executes source and does not emit a linked binary or a Lake build
snapshot. It inherits the caller's working directory and environment; Lake's
augmented subprocess environment is not installed. Native executable build
facets, linking, dependency fetching, and full Lake configuration remain
outside this execution path.

### Executable module companions

`lake build +Module:ir` additionally compiles native executable IR for that
module and every local source dependency. It requires module-system source
files (those beginning with `module`) and publishes each `.ir` together with
the checked `.olean`, `.olean.server`, and `.olean.private` family. The logical
companions also carry the signatures needed by downstream Lean compilation.
Mixed
`:ir` and `:olean` targets are supported; an admission-only target outside an
executable target's dependency closure does not acquire an IR requirement.

For example, a module under a declared `Demo` library root can contain:

```lean
module
prelude
public import Init.Notation
public def Demo.choose (flag : Bool) (left right : Nat) : Nat :=
  if flag then left else right
public def Demo.increment (n : Nat) : Nat := Nat.add n 1
public opaque Demo.answer : Nat := 42
```

With the pinned imports available, `lake build +Demo:ir` produces executable
companions under `.lake/build/lib/lean`. The compiler consumes the exact
checked implementation environment, including private bodies, on both fresh
and reused builds. It does not recover compiler authority from output files.
Supported source signatures use Nat, String, Bool, and the compiler's supported
function carriers; the backend handles pure closures, acyclic branches, and
the vetted explicit Nat operations and `String.append`. Imported typeclass
dictionaries, including the dictionary used by ordinary `n + 1`, can require
unsupported runtime layouts; use the explicit primitive when it has the same
intended operation. Source-body analysis also conservatively refuses some
multiargument calls and local Boolean bindings when it cannot establish the
pinned reduced calling convention. Supported carriers alone do not make every
pure body compilable. Unsupported definitions refuse the entire facet before
any existing output is replaced. Explicit noncomputable definitions and
theorem bodies need no executable entries.

Safe opaque definitions use their checked private implementation for code
generation while their logical declarations remain opaque. Compilation rechecks
the body through a fresh private alias, preserves the original exported ABI,
and never publishes that alias or changes the declaration's logical
transparency. Downstream execution consumes the emitted `.ir`; logical
consumers still cannot unfold the opaque body with `rfl`.

This remains a bounded compiler facet. Legacy modules require IR embedded in
their `.olean` and are refused here. Unsafe or partial exports, definitions
carrying executable-replacement or extern attributes, unsupported source
carriers, and cyclic control flow are also refused. Native object-code
generation, linking, and executable build facets remain unavailable.

The JSON report uses `fln.lake-build/2`, identifies `ir` when executable
companions are produced and otherwise `olean`, and lists every emitted path.
It also reports:

- `executable_modules`: modules with an emitted `.ir` companion;
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
requires products such as `.ilean` and additional compiler outputs. Executable
build facets and native linking, dependency fetching, custom globs, custom compiler
options, Lake configuration outside the slice above, and native
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

The same checked native Lean configuration slice serves `check-build`,
`build`, and `exe`; unsupported configuration is never replaced with metadata guessed
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

`crates/fln-cli/tests/lake_executable.rs` exercises installed Golem execution,
computed Lean executable roots and source directories, raw argv, local source
changes, output ordering, main types, exit status, import failures, and
nonpublication. Pin-dependent cases include actual Reference Lake consumers;
configuration controls retain type, name, duplicate-root, safety, and resource
refusals. The module artifact suite additionally checks opaque IR execution,
logical opacity in both readers, cache stability, and unsafe-export rollback.
