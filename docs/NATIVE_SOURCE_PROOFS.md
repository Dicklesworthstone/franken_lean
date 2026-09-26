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

## Anonymous examples

`example` checks an anonymous declaration and discards its environment successor.
It accepts propositions, data values, inferred result types, and the same explicit
and implicit binders as the ordinary declaration path:

```lean
example : 2 + 2 = 4 := by decide
example : Nat := 7
example := 8
example : Type := Nat
example {A : Type u} (x : A) : A := x
```

Examples use the current namespace, opened names, and section variables. Each
candidate passes K1 and the independent checker; repeated examples add no
constants, namespace names, or instance registrations. An example-only file has
identical input and output logical roots. `check-source` counts examples as
commands, with no theorem declaration added.

The `lean FILE` and `fln run FILE` paths also check examples silently between
ordinary definitions and queries. The body is never executed. A bad example
fails the complete command stream without releasing earlier buffered output.
Imported examples retain their dependency checks, so another module's
unimported declarations cannot become visible through an example.

This is elaboration and kernel checking support. Declaration modifiers on
examples remain unsupported, and complete Reference code-generation refusal
parity remains open under `franken_lean-z8j.1.6.6`; successful scratch checking
does not establish compiler parity for every possible example body.

## Generalized field notation

Dot notation resolves methods in the receiver type's namespace, including
`xs.length`, `xs.map f`, `xs.foldr f initial`, and proof methods such as
`h.symm` when the corresponding declaration is available. The receiver is
inserted at the first eligible parameter; preceding explicit parameters,
named arguments, implicit parameters, and partial applications retain their
ordinary application behavior.

Resolution checks each type alias's namespace before unfolding it, preserving
alias-specific methods and dictionary-projected receiver types. Function
receivers use the `Function` namespace. Existing physical and inherited record
fields retain their behavior. Inherited methods that require searching parent
namespaces in Lean's C3 order remain unsupported.

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

Quantified rewrite instantiation landed at `175bdcf73091da85ace6c97698e6a81541908c63`; source `simp only` landed at `3377252edda6a19f13a2a303ec86f5370be44336`. Rules can infer remaining expression and universe parameters from a matching goal occurrence. `rewrite` and `rw` retain unproved premises as explicit subgoals. `simp only` discharges premises using its selected proofs, selected rewrites/unfolding, or equality reflexivity; it does not search unselected hypotheses or assume missing premises. Failed matches roll back their assignments while retaining consumed work.

```lean
theorem contract (f : Nat -> Nat) (x : Nat) (h : f x = x) : f x = x := by
  exact h

theorem nested (f : Nat -> Nat) (x : Nat) (h : f x = x) : f (f (f x)) = x := by
  simp only [contract f]
```

`simp only [h, <- k]` repeatedly tries the explicit rules in deterministic order, searching occurrences inside-out, with fresh parameter instantiation for every application. Every productive equality rewrite creates an ordinary `Eq.rec` transport, or uses conversion when the endpoints are already definitionally equal. `simp only []` can close reflexive equalities using K1 conversion, including literal arithmetic. Unknown rules are errors even when the goal happens to be reflexive. Plain `simp` uses the native registered set described below; `simp only` never consults that set.

A bare safe definition in the list requests selected unfolding. For example, `simp only [twice, h]` unfolds the actual `twice` body at each occurrence's universe arguments, reduces beta/zeta redexes, then applies `h`. A named local let can be unfolded in the same way; local names shadow globals. Definition expansion does not request delta unfolding of unrelated definitions, although ordinary final kernel conversion still applies. Reverse definition unfolding is unsupported and explicitly refused.

```bash
fln check-source --json examples/native_simplification.lean
```

That runnable example contains one definition and five theorems: quantified conditional rewriting, repeated nested rewriting, selected unfolding, transport leaving a genuine goal for `exact`, and arithmetic conversion. Installed-command tests check its actual result and late-failure atomicity across multiple files.

Simplification is progress, not unconditional proof completion. A non-reflexive remaining goal must be solved by following tactics. Cyclic rule sets produce `SimplificationCycle`; productive steps are bounded at 256, in addition to the source heartbeat and kernel budgets. The native registry supplies explicit priorities, not theorem ranking, automatic orientation, a congruence-lemma database, or full Lean simp parity.

The source integration exposed two independent-checker conversion gaps, repaired in the checker rather than bypassing its veto. Reducible applications normalize before argument congruence, so discarded arguments cannot cause a false mismatch. Scoped let values now enter a private reduction overlay during body inference and are removed at scope exit; inferred local types remain the declared types. Original caller contexts are unchanged on success, cancellation, or failure. Kernel/checker implementations remain separate.

## Rewriting and simplifying named hypotheses and goals

Named locations are supported by the same native parser, elaborator, and checker council:

```lean
theorem useHypothesis (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by
  rw [h] at hx
  exact hx
```

Use `rewrite [h, ← k] at hx hy` to apply an ordered rule list to named hypotheses, or
`simp only [wrap, h, premise] at hx hy` to simplify their types using an explicit
set. Quantified rules infer their parameters afresh for each hypothesis.
Conditional `rewrite` rules leave real proof obligations; `simp only` must
prove conditions with its selected evidence. Hypothesis simplification without an explicit goal selector leaves
the main goal for subsequent tactics, rather than treating a changed hypothesis
as proof completion.

An explicit goal marker `⊢` (or the adjacent ASCII spelling `|-`) includes the
main goal: `rewrite [h] at hx ⊢` transforms `hx` first and then the goal with
oppositely directed checked transports. Named hypotheses are processed first,
regardless of where the goal marker appears in the list. `simp only [h] at hx ⊢`
shares its productive-step limit across both locations and accepts genuine
hypothesis progress even when the target is already simplified. Escaped names
such as `«⊢»` remain hypothesis names, not goal selectors.

Each changed hypothesis receives a fresh local identity and a checked transport
from the old one. A dependent hypothesis or goal keeps referring to the original
well-typed identity; the old identity is hidden from source name lookup when
necessary and otherwise removed from the live context. The final proof binds
the actual transport, so this does not mutate a local variable's type in place.
Local definitions, introduced variables, multiple locations, and Type-valued
transports use the same closure machinery. Failed tactic alternatives restore
the context and assignments without refunding consumed work.

```bash
fln check-source --json examples/native_hypothesis_rewriting.lean
```

The example includes nine theorems and two definitions. Installed-binary tests
also check that a failing later file emits no partial success and does not alter
source files or contaminate a subsequent check. Wildcard locations (`at *`), occurrence selectors, and full Lean simplifier
semantics remain outside this bounded explicit-location increment.

## Registered defaults and ordinary `simp`

`check-source` accepts standalone `attribute [simp] name` commands after the
named declaration is admitted. The default set is an immutable, versioned
environment journal. `simp`, `simp []`, and `simp [extraProof]` use it; `simp only`
and `simp only [...]` remain independent of the journal, including its errors.

```lean
def wrap.{u} {A : Sort u} (x : A) : A := x
theorem unwrap.{u} {A : Sort u} (x : A) : wrap x = x := by rfl
attribute [simp] unwrap
theorem nested (n : Nat) : wrap (wrap n) = n := by simp
attribute [-simp] unwrap
theorem explicit (n : Nat) : wrap n = n := by simp only [unwrap]
```

The same registered set works at named hypotheses and explicit goal locations.
Conditional equality rules must discharge their premises using the selected
evidence or checked reflexivity; registration cannot invent a premise. Safe
definitions can be registered for selected unfolding, while equality lemmas
retain their actual proof terms and fresh universe instantiation on each use.

`attribute [simp 1200] rule` sets a priority; `attribute [simp <- 1200] rule`
selects the reverse direction of an equality. Explicit tactic arguments are
tried first, then registered rules in descending priority with newer ties first.
Re-registering an identical row is a no-op. `attribute [-simp] rule` erases it
only from the returned snapshot, not from older engine snapshots. Names resolve
in the current namespace/open scope and are stored as structural global names;
later local shadowing cannot redirect a registered rule.

### Per-call exclusions and overrides

`simp [-rule]` removes a named global rule for that invocation only; the
environment journal and later calls are unchanged. Arguments are processed in
order: `simp only [rule, -rule]` removes the selection, while
`simp only [-rule, rule]` adds it back. Selecting `← rule` replaces that global
rule's default forward direction rather than retaining a cyclic pair.

Erasure resolves structural global names through the current namespace and
`open` scope. A same-named local cannot redirect it. An explicitly selected
local proof or applied lemma such as `(rule n)` is separate evidence and is not
removed by `-rule`. Parentheses around a bare global name retain its identity.
Unknown or ambiguous names are errors; a known declaration absent from the set
is a no-op (the Reference's warning for this case is not currently emitted).

Explicit definition unfolding uses the same namespace, root-escape, and local
shadowing rules as ordinary terms, including parenthesized selections. For
example, after `open Wrapper`, `simp [-unwrap, (wrap)]` unfolds the actual
`Wrapper.wrap` definition without modifying `Wrapper.unwrap`'s registration.
Exclusions work at supported named hypotheses and goal locations, with the
same checked transports and failure-atomic tactic alternatives. `[*]`, local
hypothesis erasure, and complete upstream selection semantics remain open.

A multi-name attribute command and a multi-file check publish only on complete
success. Unknown, ambiguous, unsafe, malformed or unsupported registrations
fail rather than being ignored. Corrupt journals and resource stops cannot be
caught as a successful `try`/`first` fallback or become empty default sets. The
journal has explicit row and payload limits in addition to the simplifier's
existing work and productive-step limits.

```bash
fln check-source --json examples/native_default_simp.lean
```

This is a native source profile, not the Reference's serialized simp extension
or a preloaded Init/mathlib simp database. Local/scoped attributes,
general proposition rule compilation, and the complete upstream
simplifier remain separate frontiers.

### Inline declaration attributes

`@[simp]` can also precede a definition, equality theorem or Iff theorem, on the same line or
on a preceding line. The supported direction and numeric priority forms are the
same as for standalone registration, for example `@[simp ← 900]`. Declaration
names retain their namespace, escaped components and universe parameters.

```lean
def wrap.{u} {A : Sort u} (x : A) : A := x
@[simp] theorem unwrap.{u} {A : Sort u} (x : A) : wrap x = x := by rfl
theorem nested (n : Nat) : wrap (wrap n) = n := by simp
```

The parser preserves the original attribute tokens in the declaration's syntax
tree; it does not strip a prefix and reparse shifted source. The registry is
updated only after K1 and the independent checker admit the declaration. Its
own attribute is therefore unavailable while proving that declaration. An
unsupported registration, failed declaration, or later batch error exposes no
successor snapshot or partial registry update.

This production accepts one global simp attribute on a definition or theorem.
Other attributes, attribute lists, local/scoped modifiers, pre/post phases and
annotated instances/inductives are refused. The admission APIs and `check-source`
publish inline attributes; the separate executable-definition entry point
refuses them instead of silently dropping their effects.

## APIs and limits

### Equivalence rewriting

`rw [h]`, `rewrite [h]`, and `simp only [h]` now accept a proof of `P ↔ Q`
as well as equality. The same path handles reversed rules, quantified parameters,
conditional premises, named hypotheses, and occurrences in `Prop -> Type`
contexts. Global Iff theorems may use `@[simp]` or `attribute [simp]`; existing
priorities, per-call exclusions, namespace resolution, and immutable snapshots
remain in effect.

The source seed explicitly admits the Reference's propositional-extensionality
axiom `propext : {P Q : Prop} -> (P ↔ Q) -> P = Q`. Each equivalence rewrite
retains its original proof in a `propext` application and an ordinary `Eq.rec`
transport. This is not a new kernel reduction rule, an assumed equivalence,
or an axiom for the user's theorem. Both admission seats still check the entire
proof; missing `propext`, forged relations, missing premises, and resource stops
cannot become successful rewrites. See the pinned `Init/Core.lean` declaration
and plan §4.2's named-axiom contract.

```bash
fln check-source --json examples/native_logical_rewriting.lean
```

Selected proposition proofs now compile to proof-producing rules `P = True`;
selected refutations (`¬ P` or `P -> False`) compile to `P = False`. Quantified
parameters are inferred from occurrences and conditional premises still require
selected evidence. Forward registered theorem rules support these conclusions
too. The generated equivalence keeps the original proof, `Iff.intro`, and, for
refutations, `False.rec`; the existing explicit `propext` path then supplies the
equality transport. A resulting `True` goal closes with checked `True.intro`.
No Boolean truth oracle, new axiom, or unselected local assumption is used.

These rules work in goals, named hypothesis types, and well-typed type-valued
contexts. Reversing a proposition fact's generated True/False rule is refused;
explicit Eq/Iff reverse rules retain their existing behavior. Binder-opening
congruence and complete Reference simp semantics remain outside this increment.

`Engine::admit_source_declaration` checks one definition or theorem without execution. `Engine::check_source_files` checks an ordered batch and returns a `SourceFileCheck` only on complete success. Both use the existing K1 plus independent-checker council and immutable publication path.

`SourceCheckLimits` bounds aggregate source bytes and command count, in addition to the caller's per-admission limits. CLI defaults are 1 MiB across all files and 4,096 commands. Resource and internal nonanswers remain distinct from kernel rejection. Failures identify source file, command and byte offset when available. The JSON result is a report of this run, not a portable proof certificate.

Current boundaries are explicit:

- `check-source` accepts import-free declaration files with its supported scope and registration commands, including standalone and inline simp attributes. Imports, `#eval` and `#check` are refused, not ignored. The separate execution and query commands retain their existing roles.
- Rewriting and simplification support goals and explicit named hypothesis locations (`at hx hy`). Quantified rules use the native bounded unifier, not general higher-order theorem search. Wildcard locations, occurrence controls, binder-opening congruence for arbitrary subterms, Reference simp-extension interchange and complete Lean `rw`/`simp` parity remain open.
- [Native instance synthesis](NATIVE_INSTANCES.md) now supports registered classes, local instances, named global instances and selected tactic-lemma arguments. Full Synod semantics, broad tactic coverage, arbitrary Lean source compatibility and the independent checker's remaining inductive frontier remain incomplete.

## Verification

The equality and rewriting production commits were made only after actual source tests, engine council tests, Clippy with warnings denied and workspace all-target compilation passed. Rewriting run `34291847903` retained 382 passing elaborator/parser tests and 109 passing engine-library/equality/rewrite tests. Command run `34292521199` additionally verified the new source-file and installed-command tests before publication.

The final local scoped runs reported 382 elaborator/parser tests, 113 engine-library and focused proof tests, and all 70 CLI package tests passing, with zero failures or ignored tests. Package Clippy and workspace all-target compilation passed. These are scoped observations on the configured `nightly-2026-08-31` compiler, not a full workspace test-suite, Reference-parity, or release-gate claim.

The proof-automation increment is additionally tested with the complete checker package, the complete parser/elaborator packages, the engine library and source equality/rewriting/file/automation targets, and the complete CLI package. Scoped Clippy with warnings denied and all-target workspace compilation are run before publication. The exact patch and command logs are retained by the source-simplification landing run; these checks do not close the full-workspace test, real-Prelude council, general elaboration, or release gates. The larger `fln-kpd` / `franken_lean-jxw` workstreams remain open.


### Selecting local evidence with `simp [*]`

`simp [*]` and `simp only [*]` select the current propositional hypotheses by
local identity, including shadowed hypotheses and checked local `have` values.
Equality and equivalence hypotheses become rewrite rules; other selected proofs
can close matching goals, discharge conditional rules, or use the existing
proved/refuted proposition compilation to True/False. Quantified hypotheses
remain polymorphic and are instantiated at each matching occurrence. Arbitrary
data variables are not guessed as missing theorem parameters. Repeated stars do
not duplicate evidence, and the persistent registry is unchanged.

At supported named locations, the hypothesis being simplified is excluded from
wildcard evidence, including conditional-premise discharge. Replacing a local
updates the wildcard identity for subsequent locations and the goal. The old and
new types are connected by ordinary checked transports; no type is retagged.
Failures roll back with the surrounding tactic alternative without refunding
work. Both declaration checkers retain their veto.

Run `fln check-source --json examples/native_simp_hypotheses.lean` for five
examples. This increment does not add `at *`, local-hypothesis erasure, automatic
rule orientation, or complete upstream simplifier semantics. `-name` retains its existing global-erasure meaning.


### Closing with `simpa`

`simpa [rules] using proof` simplifies the evidence's type and the goal with the
same selected set, then closes only when their resulting types match. `only`,
registered defaults, rule exclusions and wildcard local evidence use the same
selection code as `simp`. The evidence is elaborated by the ordinary heap term
driver and checked before a tactic alternative can commit. Its original type
and value remain in a checked let binding even when simplification discards
parts of that type. The supplied proof is not implicitly added as a rewrite
rule or as wildcard evidence.

Without `using`, `simpa` tries local assumptions in reverse declaration order,
normalizing each in an isolated trial. A failed candidate retains no semantic
state but does retain consumed work. As a final alternative, simplification can
close the goal without an assumption. Unlike `simp`, `simpa` must finish: a
changed but unsolved goal is a tactic failure, not permission for later tactics
to complete it. Resource and internal nonanswers still propagate.

Evidence and goal rewriting share the 256-step productive limit per candidate.
All generated transports and local evidence still pass both admission checkers.
`examples/native_simpa.lean` exercises defaults, explicit evidence, context
search, wildcard selection and reflexivity. This bounded form does not implement
`simpa!`, `simpa?`, custom dischargers/configuration, locations, or nested `by`
inside the `using` term. It does not claim complete Lean simplifier parity.
