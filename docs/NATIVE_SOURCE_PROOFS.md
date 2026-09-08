# Native source proofs: equality, rewriting, and file checking

This is an implemented bounded source path, not a claim of complete Lean or mathlib compatibility. The equality/reflexivity integration landed in `551975d503d94b92584b0aa22b99ecabb788bac2`, rewriting in `ee81948539a78804182f3d130d7dcda688c60d3e`, and the admission-only command in `82870caabf358efc7acaac6888450298f784f813`.

## Run a real proof file

```bash
cargo run --locked -p fln-cli --bin fln -- check-source --json examples/native_equality.lean
```

An installed build uses the same path:

```bash
fln check-source --json examples/native_equality.lean
fln check-source --max-bytes 1048576 definitions.lean proofs.lean
```

The example contains one definition and five theorems: reflexivity, symmetry, congruence, transitivity, and predicate transport. It has been checked by the actual binary. The successful `fln.source-check/1` result includes the file, declaration and theorem counts, source-byte count, base/result logical roots, and `executed:false`.

Earlier declarations are visible to later commands and files. All supplied files must succeed before a success result is emitted. A late refusal exposes no advanced engine snapshot and emits no partial-success record. This command does not compile or run the source program and creates no output artifact. Kernel normalization during proof checking remains necessary and is not runtime program execution.

## Equality and rewriting

The source prelude now provides the ordinary indexed `Eq` inductive block, `Eq.refl`, its dependent `Eq.rec` eliminator, and an inferred-argument `rfl` abbreviation. K1 regenerates the eliminator; a forged eliminator regression must reject. Source `=` is propositional equality, distinct from Boolean `==`.

```lean
theorem self (x : Nat) : x = x := by rfl

theorem congruent (f : Nat -> Nat) (x y : Nat) (h : x = y) : f x = f y := by
  rw [h]

theorem transport (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by
  rw [← h]
  exact hx
```

`rfl` constructs a proof term; the kernel performs conversion, including the tested `2 + 3 = 5` case. A false equality such as `1 = 2` is not admitted.

`rw [h]`, `rw [← h]` (also `<-`), and ordered rule lists generate ordinary `Eq.rec` transports. The equality proof is retained in the final term. `rw` attempts reflexivity after the list; `rewrite [h]` leaves the resulting goal for a following tactic. Rules use normal source-term elaboration, including explicit applications. Tests cover introduced locals, dependent predicates, generic types and Type-valued transport. Matching and template reconstruction are metered, allocation-memoized DAG walks.

## APIs and limits

`Engine::admit_source_declaration` checks one definition or theorem without execution. `Engine::check_source_files` checks an ordered batch and returns a `SourceFileCheck` only on complete success. Both use the existing K1 plus independent-checker council and immutable publication path.

`SourceCheckLimits` bounds aggregate source bytes and command count, in addition to the caller's per-admission limits. CLI defaults are 1 MiB across all files and 4,096 commands. Resource and internal nonanswers remain distinct from kernel rejection. Failures identify source file, command and byte offset when available. The JSON result is a report of this run, not a portable proof certificate.

Current boundaries are explicit:

- `check-source` accepts import-free `def` and `theorem` files. Imports, `#eval` and `#check` are refused, not ignored. The separate execution and query commands retain their existing roles.
- Rewriting is goal-only and matches exact elaborated occurrences of already instantiated equality rules. Hypothesis locations (`at h`), occurrence controls, automatic instantiation of arbitrary rewrite lemmas, simplification and full Lean `rw` parity remain open.
- General typeclass synthesis, broad tactic coverage, arbitrary Lean source compatibility and the independent checker's remaining inductive frontier are not established by this increment.

## Verification

The equality and rewriting production commits were made only after actual source tests, engine council tests, Clippy with warnings denied and workspace all-target compilation passed. Rewriting run `34291847903` retained 382 passing elaborator/parser tests and 109 passing engine-library/equality/rewrite tests. Command run `34292521199` additionally verified the new source-file and installed-command tests before publication.

The final local scoped runs reported 382 elaborator/parser tests, 113 engine-library and focused proof tests, and all 70 CLI package tests passing, with zero failures or ignored tests. Package Clippy and workspace all-target compilation passed. These are scoped observations on the configured `nightly-2026-08-31` compiler, not a full workspace test-suite, Reference-parity, or release-gate claim.
