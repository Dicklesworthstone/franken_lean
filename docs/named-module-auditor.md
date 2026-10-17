# Check one compiled module and its imports

`fln check-module` is a standalone, read-only auditor for a named module in the
pinned Lean artifact format. It captures only the module's transitive import
closure, then checks every declaration through FrankenLean's existing K1 and
independent-checker council. It does not run the upstream compiler or trust its
kernel verdicts, cached admission records, or source files.

This is a narrower workflow than `fln check-olean --continue ROOT...`, which
surveys all the modules under supplied directories. A broken, unrelated artifact
elsewhere in a library does not prevent checking the selected closure.

## Build and use

From the repository:

```sh
cargo build --locked -p fln-cli --bin fln
```

For a standard Elan installation of the pinned reference toolchain:

```sh
target/debug/fln check-module --json --jobs 2 Init.Prelude \
  "$HOME/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean"
```

For a library that imports a second package, supply both artifact roots:

```sh
target/debug/fln check-module --json MyLibrary.Theorem \
  /path/to/my-library/.lake/build/lib/lean \
  /path/to/dependency/.lake/build/lib/lean \
  /path/to/pinned-toolchain/lib/lean
```

Use the artifact directory, not the source directory or an individual `.olean`
filename. Roots are explicit: the command does not consult `LEAN_PATH`, Elan,
Lake configuration, or any ambient import cache. A module occurring in more than
one root is an error, even when the files have identical bytes. Search order
therefore cannot select a different proof context silently.

The default captured-input allowance is 256 MiB across **all** public, server,
and private parts. `--max-bytes BYTES` changes that allowance; it is not a bound
on the checker's decoded-memory use. `--jobs N` accepts 1 through 64, defaulting
to serial checking. Parallel checks use each module's own admitted import
closure, with the same council and logical budgets as the serial path.

## What a successful result establishes

The `fln.check-module/1` JSON report has `outcome: "complete"` and
`authority: true` only after the complete captured closure succeeds. It names
the requested module, scope, module and declaration counts, distinct axiom
count in the checked environment, and the resulting logical root. Every module
row includes the repository's domain-separated artifact byte hashes for its
captured parts. These hashes describe the bytes that were actually checked,
not a later reread of mutable paths.

Axioms remain assumptions. A successful declaration check does not prove an
axiom, establish that a theorem used no `sorryAx`, interpret environment
extensions, execute code, certify source reproducibility, or prove that all
parts came from one upstream build. Use the existing trust-inventory tools for
further trust analysis; the named-module report does not replace a dependency
or axiom-use audit.

The command refuses missing dependencies, ambiguous module locations, malformed
or incompatible artifacts, import cycles, and incomplete module-system chains.
Companions must be beside their public artifact in the **same** search root.
Search roots themselves and traversed descendants may not be symlinks. Inputs
are captured before council admission, and this command writes no artifacts or
cache records. It is not a filesystem sandbox against concurrent adversarial
path replacement.

Machine-readable failures are also written to stdout when `--json` is selected,
with `authority: false`; the process exit status must always be checked:

| Exit | Meaning |
| --- | --- |
| 0 | Entire selected closure checked successfully. |
| 1 | Input, module graph, decoding, or checking failed. |
| 2 | Invalid command-line arguments. |
| 3 | Resource exhaustion or another inconclusive check. |
| 4 | Internal invariant or worker failure. |

This command makes the existing artifact checker easier to use on individual
libraries. It does not expand the checker's supported declaration classes and
is not a claim of G1 corpus closure, full source elaboration, or general Lean
and Mathlib compatibility.
