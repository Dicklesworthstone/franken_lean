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

## Quantified rewriting and explicit-set simplification

Quantified rewrite instantiation landed at `175bdcf73091da85ace6c97698e6a81541908c63`; source `simp only` landed at `3377252edda6a19f13a2a303ec86f5370be44336`. Rules can infer remaining expression and universe parameters from a matching goal occurrence. Propositional premises can be discharged by existing local proofs or equality reflexivity; unproved premises are never assumed. Failed matches roll back their assignments while retaining consumed work.

```lean
theorem contract (f : Nat -> Nat) (x : Nat) (h : f x = x) : f x = x := by
  exact h

theorem nested (f : Nat -> Nat) (x : Nat) (h : f x = x) : f (f (f x)) = x := by
  simp only [contract f]
```

`simp only [h, <- k]` repeatedly tries the explicit rules in deterministic order, searching occurrences inside-out, with fresh parameter instantiation for every application. Every productive equality rewrite creates an ordinary `Eq.rec` transport, or uses conversion when the endpoints are already definitionally equal. `simp only []` can close reflexive equalities using K1 conversion, including literal arithmetic. Unknown rules are errors even when the goal happens to be reflexive. Plain `simp` is not silently treated as an empty default simp set.

A bare safe definition in the list requests selected unfolding. For example, `simp only [twice, h]` unfolds the actual `twice` body at each occurrence's universe arguments, reduces beta/zeta redexes, then applies `h`. A named local let can be unfolded in the same way; local names shadow globals. Definition expansion does not request delta unfolding of unrelated definitions, although ordinary final kernel conversion still applies. Reverse definition unfolding is unsupported and explicitly refused.

```bash
fln check-source --json examples/native_simplification.lean
```

That runnable example contains one definition and five theorems: quantified conditional rewriting, repeated nested rewriting, selected unfolding, transport leaving a genuine goal for `exact`, and arithmetic conversion. Installed-command tests check its actual result and late-failure atomicity across multiple files.

Simplification is progress, not unconditional proof completion. A non-reflexive remaining goal must be solved by following tactics. Cyclic rule sets produce `SimplificationCycle`; productive steps are bounded at 256, in addition to the source heartbeat and kernel budgets. This bounded lane has no global simp registry, theorem ranking, automatic orientation, congruence-lemma database, or full Lean simp parity.

The source integration exposed two independent-checker conversion gaps, repaired in the checker rather than bypassing its veto. Reducible applications normalize before argument congruence, so discarded arguments cannot cause a false mismatch. Scoped let values now enter a private reduction overlay during body inference and are removed at scope exit; inferred local types remain the declared types. Original caller contexts are unchanged on success, cancellation, or failure. Kernel/checker implementations remain separate.

## APIs and limits

`Engine::admit_source_declaration` checks one definition or theorem without execution. `Engine::check_source_files` checks an ordered batch and returns a `SourceFileCheck` only on complete success. Both use the existing K1 plus independent-checker council and immutable publication path.

`SourceCheckLimits` bounds aggregate source bytes and command count, in addition to the caller's per-admission limits. CLI defaults are 1 MiB across all files and 4,096 commands. Resource and internal nonanswers remain distinct from kernel rejection. Failures identify source file, command and byte offset when available. The JSON result is a report of this run, not a portable proof certificate.

Current boundaries are explicit:

- `check-source` accepts import-free `def` and `theorem` files. Imports, `#eval` and `#check` are refused, not ignored. The separate execution and query commands retain their existing roles.
- Rewriting and simplification are goal-only. Quantified rules use the native bounded unifier, not general higher-order theorem search. Hypothesis locations (`at h`), occurrence controls, binder-opening congruence for arbitrary subterms, global `[simp]` sets and complete Lean `rw`/`simp` parity remain open.
- [Native instance synthesis](NATIVE_INSTANCES.md) now supports registered classes, local instances, named global instances and selected tactic-lemma arguments. Full Synod semantics, broad tactic coverage, arbitrary Lean source compatibility and the independent checker's remaining inductive frontier remain incomplete.

## Verification

The equality and rewriting production commits were made only after actual source tests, engine council tests, Clippy with warnings denied and workspace all-target compilation passed. Rewriting run `34291847903` retained 382 passing elaborator/parser tests and 109 passing engine-library/equality/rewrite tests. Command run `34292521199` additionally verified the new source-file and installed-command tests before publication.

The final local scoped runs reported 382 elaborator/parser tests, 113 engine-library and focused proof tests, and all 70 CLI package tests passing, with zero failures or ignored tests. Package Clippy and workspace all-target compilation passed. These are scoped observations on the configured `nightly-2026-08-31` compiler, not a full workspace test-suite, Reference-parity, or release-gate claim.

The proof-automation increment is additionally tested with the complete checker package, the complete parser/elaborator packages, the engine library and source equality/rewriting/file/automation targets, and the complete CLI package. Scoped Clippy with warnings denied and all-target workspace compilation are run before publication. The exact patch and command logs are retained by the source-simplification landing run; these checks do not close the full-workspace test, real-Prelude council, general elaboration, or release gates. The larger `fln-kpd` / `franken_lean-jxw` workstreams remain open.
