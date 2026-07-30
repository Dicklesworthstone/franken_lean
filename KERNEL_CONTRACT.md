# KERNEL_CONTRACT.md — the Judgment Specification

**Version:** 1 (epoch `v4.32.0`) · **Bead:** franken_lean-79k · **Status:** normative

This document is the rule-by-rule account of the type theory FrankenLean implements
(plan §8.1b, Appendix A). Both kernel engines (K1, K2), the independent checker, and
the Tribunal's term generators are built **against this document**; the pinned
Reference C++ is what this document is *checked against*, rule by rule, by the
differential harness — the inversion that is itself a product.

**How to read a rule.** Every rule carries: a stable id (`KR-NNN`); one or more
`anchor:` lines naming the exact Reference source location at the pin, with an
`expect="token"` that must appear on that line (drift fails CI); a `fixtures:` line
naming the evidence (or `stub owner=<bead>` naming who will supply it); and an
unambiguous statement a second implementer can code from. The document is CI-checked
like code by `crates/fln-conformance/tests/kernel_contract.rs`.

**Resource law (constitutional).** Every resource hook in §KR-4xx is *counted, never
semantic*: exhaustion is a verdict about a **run**, never about a **term** — it
surfaces as `KernelInconclusive`, never as rejection or acceptance (FL-INV-07).

**Literature baseline.** Mario Carneiro, *The Type Theory of Lean* (2019) is the
standing reference for the metatheory; rules below cite the pin's code as the
behavioral authority and the thesis for justification. Where the plan text and the
pin disagree (see KR-313's note on `Nat.blt`), **the pin governs and the divergence
is recorded here**.

---

## 1. Typing rules (KR-1xx)

Dispatcher: `infer_type_core` switches on the expression kind and memoizes per
`infer_only` mode.

### KR-100 · Preconditions — closed terms, resource hook
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:270 (infer_type_core) expect="infer_type_core"
fixtures: stub owner=franken_lean-z6c
Every inference first rejects loose bound variables ("replace them with free
variables before invoking") and runs the counted resource hook (KR-400). Terms
reaching the kernel are closed with respect to de Bruijn variables.

### KR-101 · Bound variables are unreachable
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:287 (infer_type_core) expect="BVar"
fixtures: stub owner=franken_lean-z6c
Given KR-100 and binder telescoping (KR-106/107/108), a raw `bvar` at the dispatcher
is an internal invariant violation, not a user-reachable state.

### KR-102 · Free variables
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:84 (infer_fvar) expect="infer_fvar"
fixtures: stub owner=franken_lean-z6c
An `fvar` types as the type recorded in its local-context declaration; an unknown
free variable is an error.

### KR-103 · Metavariables are rejected
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:286 (infer_type_core) expect="MVar"
fixtures: stub owner=franken_lean-z6c
The kernel never types a metavariable: elaboration artifacts must be fully
instantiated before admission.

### KR-104 · Sort
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:289 (infer_type_core) expect="Sort"
fixtures: stub owner=franken_lean-z6c
`Sort u : Sort (u+1)`. In checking mode, `u` must reference only declared universe
parameters (KR-140).

### KR-105 · Constants
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:92 (infer_constant) expect="infer_constant"
fixtures: stub owner=franken_lean-z6c
`c.{ls}` requires the level-argument count to equal the declaration's
level-parameter count (both modes). In checking mode additionally: the unsafe
quarantine (KR-975), the partial quarantine (KR-976), and KR-140 on every level.
The type is the declaration's type with parameters instantiated by `ls`.

### KR-106 · Application
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:163 (infer_app) expect="infer_app"
fixtures: stub owner=franken_lean-z6c
Checking mode: the head's type is forced to a Π (via whnf; else "function
expected"); the argument's inferred type must be defeq to the domain (else "app type
mismatch"); the result is the codomain instantiated with the argument. Infer-only
mode walks the spine peeling syntactic Πs without the defeq domain checks. The
`eagerReduce` marker on an argument switches the defeq check into eager-reduction
mode for its duration.

### KR-107 · Lambda
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:116 (infer_lambda) expect="infer_lambda"
fixtures: stub owner=franken_lean-z6c
Telescoped: each domain (checking mode) must be a sort; the body is inferred under
the extended local context; the result is the Π-abstraction of the body type over
the telescope, after a cheap beta-reduction of the body type.

### KR-108 · Dependent function types — the imax rule
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:134 (infer_pi) expect="infer_pi"
fixtures: crates/fln-conformance/fixtures/core_observables.txt
`Π (x : A), B` where `A : Sort u` and `B : Sort v` types as
`Sort (imax u v)`, right-folded over the telescope. With KR-500's
`imax u 0 = 0` collapse this is exactly Prop impredicativity. Every domain must be a
sort even in infer-only mode (the universe is needed).

### KR-109 · Let
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:198 (infer_let) expect="infer_let"
fixtures: stub owner=franken_lean-z6c
Telescoped with value-carrying local declarations: in checking mode the declared
type must be a sort and the value's inferred type defeq to it ("def type
mismatch"). The body types under the extended context.

### KR-110 · Literals
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:282 (infer_type_core) expect="Lit"
fixtures: stub owner=franken_lean-z6c
A `Nat` literal types as `Nat`; a `String` literal as `String`. No premises.

### KR-111 · Metadata is transparent
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:283 (infer_type_core) expect="MData"
fixtures: stub owner=franken_lean-z6c
`mdata m e` types as `e`.

### KR-112 · Projections
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:221 (infer_proj) expect="infer_proj"
fixtures: stub owner=franken_lean-z6c
`proj I idx s`: the whnf of `s`'s type must be `I As` where `I` is an inductive with
exactly one constructor and `|As| = nparams + nindices`. The projected type is the
`idx`-th field domain of the constructor's telescope, with parameters instantiated
and earlier dependent fields substituted by nested projections of `s`. Prop guard:
see KR-901.

---

## 2. Weak-head normalization (KR-2xx)

### KR-200 · The whnf strategy
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:641 (whnf) expect="whnf"
fixtures: stub owner=franken_lean-z6c
Outer loop over: `whnf_core` (no delta), then native reduction (KR-318), then Nat
literal acceleration (KR-313), then one delta unfolding (KR-309's machinery); loop
until stable; positive results cached. Easy kinds (`bvar/sort/mvar/pi/lit`) return
immediately and are never cached.

### KR-201 · whnf-core performs no delta
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:401 (whnf_core) expect="whnf_core"
fixtures: stub owner=franken_lean-z6c
`whnf_core` handles metadata stripping, let-fvar zeta, beta, let-zeta, projection
reduction, and recursor dispatch — never definition unfolding and never normalizer
extensions. Results cache only when neither cheap flag is set.

### KR-202 · Beta
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:443 (whnf_core) expect="App"
fixtures: stub owner=franken_lean-z6c
Multi-argument beta in one batch: peel as many lambda binders as arguments are
available, instantiate, and continue reducing the residual application.

### KR-203 · Zeta — let and let-bound fvars
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:474 (whnf_core) expect="Let"
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:348 (whnf_fvar) expect="whnf_fvar"
fixtures: stub owner=franken_lean-z6c
`let x := v; b` reduces to `b[v/x]`; a let-bound free variable unfolds to its
recorded value.

### KR-204 · Projection reduction
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:359 (reduce_proj_core) expect="reduce_proj_core"
fixtures: stub owner=franken_lean-z6c
`proj I idx (mk As fs)` reduces to field `idx` (i.e. argument `nparams + idx`).
A `String` literal scrutinee is first expanded to its constructor form.

### KR-205 · Recursor dispatch
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:333 (reduce_recursor) expect="reduce_recursor"
fixtures: stub owner=franken_lean-z6c
When the application head is stable, quotient computation (KR-955) is tried first
(when initialized), then inductive iota (KR-316). Unfolds are recorded in
diagnostics when enabled (never limiting; KR-404).

---

## 3. Definitional equality (KR-3xx)

Entry: `is_def_eq`, with positive results cached in the equivalence manager.

### KR-300 · Resource hook and quick equality
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:1056 (is_def_eq_core) expect="is_def_eq_core"
fixtures: stub owner=franken_lean-z6c
Every defeq query runs the counted resource hook, then the quick check.

### KR-301 · Quick structural/hash equality
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:740 (quick_is_def_eq) expect="quick_is_def_eq"
fixtures: stub owner=franken_lean-z6c
Pointer/structural/cached equality via the equivalence manager; same-kind fast
paths: bindings (KR-302), sorts by level equivalence (KR-303), metadata by payload,
literals by value.

### KR-302 · Binder congruence
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:690 (is_def_eq_binding) expect="is_def_eq_binding"
fixtures: stub owner=franken_lean-z6c
Π/λ compare domain-wise then body-wise under a fresh local (introduced only when
the bound variable occurs).

### KR-303 · Level equality
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:719 (is_def_eq) expect="is_def_eq"
fixtures: crates/fln-conformance/fixtures/core_observables.txt
Sorts are defeq iff their levels are equivalent under level normalization (KR-500).

### KR-304 · The decide shortcut
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:1066 (is_def_eq_core) expect="m_eager_reduce"
fixtures: stub owner=franken_lean-z6c
When the left side is closed (or eager reduction is on) and the right side is the
constant `Bool.true`, a full whnf of the left side deciding to `Bool.true` closes
the query.

### KR-305 · Cheap normalization, projections deferred
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:1079 (is_def_eq_core) expect="whnf_core"
fixtures: stub owner=franken_lean-z6c
Both sides normalize without delta and with projection unfolding deferred, so
`a.i ≟ b.i` can first try `a ≟ b`.

### KR-306 · Definitional proof irrelevance in Prop
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:836 (is_def_eq_proof_irrel) expect="is_def_eq_proof_irrel"
fixtures: stub owner=franken_lean-z6c
If the type of the left side is a proposition, the two terms are defeq iff their
types are defeq. The sole condition is `is_prop` of the type.

### KR-307 · The lazy-delta ladder
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:973 (lazy_delta_reduction) expect="lazy_delta_reduction"
fixtures: stub owner=franken_lean-z6c
Loop: Nat offset check (KR-308); Nat/native literal reduction on closed sides; one
lazy delta step (KR-309); repeat until decided or stable.

### KR-308 · Nat successor offsets
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:961 (is_def_eq_offset) expect="is_def_eq_offset"
fixtures: stub owner=franken_lean-z6c
`Nat.succ`-shaped sides (including literals > 0 viewed as successors) compare by
peeling predecessors — large literals never unfold unarily.

### KR-309 · Delta ordering by definitional height
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:884 (lazy_delta_reduction_step) expect="lazy_delta_reduction_step"
fixtures: stub owner=franken_lean-z6c
When only one side has an unfoldable head, unfold it — except that a projection
application on the other side unfolds first. When both are unfoldable, the
`ReducibilityHints` comparison decides: the greater definitional height unfolds
first; at equal heights both unfold, but two applications of the *same* regular
definition first try level+argument congruence, with negative results cached.
Reducibility *attributes* never change kernel behavior — only the recorded hints
(height) do; this is the reducibility-independence law.

### KR-310 · Post-delta syntactic closure
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:1094 (is_def_eq_core) expect="is_constant"
fixtures: stub owner=franken_lean-z6c
Same-name constants with equivalent levels, identical fvars, and same-index
projections (whose scrutinees compare under lazy projection reduction) close the
query.

### KR-311 · Application congruence
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:815 (is_def_eq_app) expect="is_def_eq_app"
fixtures: stub owner=franken_lean-z6c
After a full-whnf projection retry, applications compare head-and-args pointwise.

### KR-312 · Eta — functions and structures
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:778 (try_eta_expansion_core) expect="try_eta_expansion_core"
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:793 (try_eta_struct_core) expect="try_eta_struct_core"
fixtures: stub owner=franken_lean-z6c
Function eta: a lambda against a non-lambda eta-expands the non-lambda through its
Π-type, both directions. Structure eta: `t ≟ mk as fs` for a one-constructor,
non-recursive, index-free structure holds when the types agree and every field
`fᵢ` is defeq to `t.i`, both directions.

### KR-313 · Nat literal acceleration — the exact operation set
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:609 (reduce_nat) expect="reduce_nat"
fixtures: stub owner=franken_lean-z6c
On `Nat` literals the kernel computes: `succ`, `add`, `sub`, `mul`, `div`, `mod`,
`gcd`, `pow` (exponent capped at 2^24), `beq`, `ble`, `land`, `lor`, `xor`,
`shiftLeft`, `shiftRight`. **Divergence note (pin governs):** the plan's Appendix A
lists `blt`; at this pin there is no `Nat.blt` acceleration — only `beq`/`ble`.
Gated on closed terms (or eager reduction).

### KR-314 · String literal rules
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:1030 (try_string_lit_expansion_core) expect="try_string_lit_expansion_core"
fixtures: stub owner=franken_lean-z6c
A `String` literal is defeq to its `String.ofList` constructor form, both
directions; projection and recursor machinery expand literals the same way.

### KR-315 · Unit-like eta
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:1044 (is_def_eq_unit_like) expect="is_def_eq_unit_like"
fixtures: stub owner=franken_lean-z6c
Two terms of the same one-constructor, zero-field structure type are defeq when
their types are.

### KR-316 · Iota — recursor computation
anchor: vendor/lean4-src/src/kernel/inductive.h:76 (inductive_reduce_rec) expect="inductive_reduce_rec"
fixtures: stub owner=franken_lean-z6c
A recursor application fires when its major premise (at
`nparams + nmotives + nminors + nindices`) reduces to a constructor of the right
inductive — after K conversion (KR-317), Nat/String literal-to-constructor
conversion, and structure-eta coercion. The matching rule's right-hand side is
instantiated with the recursor's levels, applied to params, motives, minors, the
constructor's fields, and trailing arguments.

### KR-317 · K-like reduction
anchor: vendor/lean4-src/src/kernel/inductive.cpp:551 (init_K_target) expect="init_K_target"
anchor: vendor/lean4-src/src/kernel/inductive.h:31 (to_cnstr_when_K) expect="to_cnstr_when_K"
fixtures: stub owner=franken_lean-z6c
A recursor supports K exactly when its inductive is non-mutual, Prop-valued, with
one constructor of zero fields. Then any major premise whose type is defeq to the
expected constructor type is replaced by the nullary constructor — reduction
without matching the syntactic proof.

### KR-318 · Native reduction hooks
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:546 (reduce_native) expect="reduce_native"
fixtures: stub owner=franken_lean-z6c
`Lean.reduceBool` / `Lean.reduceNat` evaluate via the compiled evaluator — the
`native_decide` trust surface. FrankenLean preserves the semantics and marks every
dependent theorem in provenance (plan §Limitations).

---

## 4. Resource accounting (KR-4xx) — counted, never semantic

### KR-400 · Inference hook
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:274 (infer_type_core) expect="check_system"
fixtures: stub owner=franken_lean-z6c
Every inference node counts.

### KR-401 · Normalization hook
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:402 (whnf_core) expect="check_system"
fixtures: stub owner=franken_lean-z6c
Every whnf-core entry counts.

### KR-402 · Defeq hook
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:1057 (is_def_eq_core) expect="check_system"
fixtures: stub owner=franken_lean-z6c
Every defeq query counts.

### KR-403 · The counter mechanism
anchor: vendor/lean4-src/src/runtime/interrupt.cpp:81 (check_system) expect="check_system"
fixtures: stub owner=franken_lean-z6c
The hook probes stack and memory, checks interruption, and increments the
thread-local heartbeat, throwing on exceeding the configured maximum. There is no
separate recursion-depth counter in the kernel proper; recursion is bounded by the
stack probe. In FrankenLean, every such exhaustion is a typed `KernelInconclusive`
(FL-INV-07): a verdict about the run, never about the term.

### KR-404 · Diagnostics are never limits
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:497 (unfold_definition_core) expect="unfold_definition_core"
fixtures: stub owner=franken_lean-z6c
Unfold counting is instrumentation only; no diagnostic state may influence a
verdict.

---

## 5. Universe levels (KR-5xx)

### KR-500 · Level normalization, including imax collapse
anchor: vendor/lean4-src/src/Lean/Level.lean:379 (normalize) expect="normalize"
fixtures: crates/fln-conformance/fixtures/core_observables.txt
The level language (`zero/succ/max/imax/param/mvar`) normalizes per the pin's
algorithm: offsets stripped and re-added, `max` flattened, normalized, sorted, and
subsumption-pruned; `imax u v` with never-zero `v` becomes `max`; the collapse laws
`imax u 0 = 0`, `imax 0 u = u`, `imax 1 u = u`, `imax u u = u` hold. Prop
impredicativity (KR-108) depends on the first law. Implemented and
oracle-verified in fln-core.

### KR-501 · Level equivalence
anchor: vendor/lean4-src/src/Lean/Level.lean:407 (isEquiv) expect="isEquiv"
fixtures: crates/fln-conformance/fixtures/core_observables.txt
Two levels are equivalent iff equal or normalize-equal. Kernel defeq of sorts
(KR-303) consults exactly this relation.

---

## 6. Inductive validation (KR-6xx)

### KR-600 · Block preliminaries
anchor: vendor/lean4-src/src/kernel/inductive.cpp:216 (check_inductive_types) expect="check_name"
fixtures: stub owner=franken_lean-z6c
Each type's name and its recursor name must be fresh; the type closed (no
mvars/fvars) and well-typed under the block's level params; duplicate level params
rejected; the parameter count must be machine-small.

### KR-601 · Shared parameters across a mutual block
anchor: vendor/lean4-src/src/kernel/inductive.cpp:223 (check_inductive_types) expect="is_pi"
fixtures: stub owner=franken_lean-z6c
The first `nparams` binders of every type in the block must be defeq to the first
type's parameters, and the counts must match exactly; the remaining binders are
indices, counted per type.

### KR-602 · One universe per mutual block
anchor: vendor/lean4-src/src/kernel/inductive.cpp:245 (check_inductive_types) expect="ensure_sort"
fixtures: stub owner=franken_lean-z6c
The residual type of each block member must be a sort; all members' levels must be
equivalent to the first's.

### KR-603 · Constructor validity
anchor: vendor/lean4-src/src/kernel/inductive.cpp:413 (check_constructors) expect="check_constructors"
fixtures: stub owner=franken_lean-z6c
Constructor names unique and fresh; types closed and well-typed; the first
`nparams` domains defeq to the datatype parameters; every further field domain a
type; the result an application of the constructor's own inductive (KR-605).

### KR-604 · Field universes — the Prop exception
anchor: vendor/lean4-src/src/kernel/inductive.cpp:435 (check_constructors) expect="ensure_type"
fixtures: stub owner=franken_lean-z6c
Each non-parameter field's universe must be ≤ the datatype's resultant level —
unless the datatype lives in Prop, where fields of any size are admitted.

### KR-605 · Valid recursive occurrence shape
anchor: vendor/lean4-src/src/kernel/inductive.cpp:338 (is_valid_ind_app) expect="is_valid_ind_app"
fixtures: stub owner=franken_lean-z6c
A legal occurrence `I As is` names the block member exactly, has
`nparams + nindices` arguments, passes the declared parameters syntactically, and —
soundness-critical — no index argument may mention any datatype being declared.

### KR-606 · Strict positivity
anchor: vendor/lean4-src/src/kernel/inductive.cpp:393 (check_positivity) expect="check_positivity"
fixtures: stub owner=franken_lean-z6c
Reducing each safe constructor field to whnf: no occurrence ⇒ accepted; a Π whose
domain mentions the block ⇒ rejected (non-positive occurrence), recursing into the
codomain; a valid occurrence (KR-605) ⇒ a recursive argument; anything else
mentioning the block ⇒ rejected. Skipped entirely for unsafe inductives.

### KR-607 · Recursivity and reflexivity flags
anchor: vendor/lean4-src/src/kernel/inductive.cpp:264 (is_rec) expect="recursive"
fixtures: stub owner=franken_lean-z6c
`is_rec` iff some field mentions a block member; `is_reflexive` iff some field is
itself a function type whose body mentions a block member. Both are recorded
observables (fln-env mirrors them).

### KR-608 · Nested inductives compile to mutual blocks
anchor: vendor/lean4-src/src/kernel/inductive.cpp:1116 (add_inductive) expect="add_inductive"
fixtures: stub owner=franken_lean-z6c
Nested occurrences are rewritten to auxiliary `_nested.*` mutual types, validated
as a mutual block, then translated back; nested parameters may not contain loose
bound variables. The kernel never validates nesting directly.

---

## 7. Elimination universes (KR-7xx)

### KR-700 · When elimination is restricted to Prop
anchor: vendor/lean4-src/src/kernel/inductive.cpp:479 (elim_only_at_universe_zero) expect="elim_only_at_universe_zero"
fixtures: stub owner=franken_lean-z6c
A possibly-Prop inductive eliminates only into Prop when the block is mutual or has
more than one constructor. An *empty* Prop inductive eliminates large. A
single-constructor Prop inductive is decided by KR-701.

### KR-701 · The subsingleton criterion
anchor: vendor/lean4-src/src/kernel/inductive.cpp:509 (elim_only_at_universe_zero) expect="cnstr"
fixtures: stub owner=franken_lean-z6c
Large elimination for a one-constructor Prop inductive requires every
non-parameter field to be a Prop or to occur among the constructor result's
arguments.

### KR-702 · The elimination level
anchor: vendor/lean4-src/src/kernel/inductive.cpp:537 (init_elim_level) expect="init_elim_level"
fixtures: stub owner=franken_lean-z6c
Restricted ⇒ level 0; otherwise a fresh universe parameter `u` (collision-avoided)
is added to the recursor's level parameters.

---

## 8. Recursor generation (KR-8xx)

### KR-800 · Motives and major premise
anchor: vendor/lean4-src/src/kernel/inductive.cpp:589 (mk_rec_infos) expect="mk_rec_infos"
fixtures: stub owner=franken_lean-z6c
Per datatype: indices are collected, the major premise is `t : I params indices`,
and the motive is `C : Π indices, I params indices → Sort elim`; mutual blocks
number their motives.

### KR-801 · Minor premises with induction hypotheses
anchor: vendor/lean4-src/src/kernel/inductive.cpp:621 (mk_rec_infos) expect="ind_type"
fixtures: stub owner=franken_lean-z6c
Per constructor: non-parameter fields, then for each recursive field an induction
hypothesis `Π xs, C (u xs)`, concluding in the motive at the constructor
application.

### KR-802 · The recursor type
anchor: vendor/lean4-src/src/kernel/inductive.cpp:759 (declare_recursors) expect="d_idx"
fixtures: stub owner=franken_lean-z6c
`Π params, Π motives, Π minors, Π indices, Π major, C indices major`, with strict
implicit inference; registered with `nparams/nindices/nmotives/nminors/rules/K/unsafe`.

### KR-803 · Iota right-hand sides
anchor: vendor/lean4-src/src/kernel/inductive.cpp:705 (mk_rec_rules) expect="mk_rec_rules"
fixtures: stub owner=franken_lean-z6c
Per constructor: `λ params Cs minors fields, minor fields ihs` where each ih is the
recursive call of the appropriate mutual recursor; the rule records the constructor
name and field count.

---

## 9. Structures and projections (KR-9xx)

### KR-900 · Projection typing
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:221 (infer_proj) expect="infer_proj"
fixtures: stub owner=franken_lean-z6c
As KR-112: one constructor, exact arity, telescope substitution with nested
projections for dependent fields.

### KR-901 · No data escapes Prop through projections
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:248 (infer_proj) expect="is_prop"
fixtures: stub owner=franken_lean-z6c
Projecting from a Prop-valued structure requires every traversed dependent field
and the projected type itself to be a Prop.

### KR-902 · Projection computation
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:359 (reduce_proj_core) expect="reduce_proj_core"
fixtures: stub owner=franken_lean-z6c
`(mk … aᵢ …).i ⟶ aᵢ` — see KR-204.

### KR-903 · Structure eta coherence
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:793 (try_eta_struct_core) expect="try_eta_struct_core"
fixtures: stub owner=franken_lean-z6c
As KR-312's structure half; the eligible class is exactly the non-recursive,
index-free, one-constructor structures, and the same coercion feeds recursor
reduction (KR-316).

---

## 10. Quotients (KR-95x)

### KR-950 · Initialization requires Eq
anchor: vendor/lean4-src/src/kernel/quot.cpp:19 (check_eq_type) expect="check_eq_type"
fixtures: stub owner=franken_lean-z6c
Quotients initialize only in an environment whose `Eq` is the expected
one-parameter, one-constructor equality with `Eq.refl` of the expected type.

### KR-951 · Quot
anchor: vendor/lean4-src/src/kernel/quot.cpp:59 (add_quot) expect="constant {u} quot"
fixtures: stub owner=franken_lean-z6c
`Quot.{u} : Π {α : Sort u}, (α → α → Prop) → Sort u`.

### KR-952 · Quot.mk
anchor: vendor/lean4-src/src/kernel/quot.cpp:63 (add_quot) expect="quot.mk"
fixtures: stub owner=franken_lean-z6c
`Quot.mk.{u} : Π {α : Sort u} (r : α → α → Prop), α → @Quot α r`.

### KR-953 · Quot.lift
anchor: vendor/lean4-src/src/kernel/quot.cpp:82 (add_quot) expect="quot.lift"
fixtures: stub owner=franken_lean-z6c
`Quot.lift.{u,v}` with the soundness premise `∀ a b, r a b → f a = f b`.

### KR-954 · Quot.ind
anchor: vendor/lean4-src/src/kernel/quot.cpp:92 (add_quot) expect="quot.ind"
fixtures: stub owner=franken_lean-z6c
`Quot.ind.{u}` eliminating into Prop-valued motives; initialization is then marked.

### KR-955 · Quot computation
anchor: vendor/lean4-src/src/kernel/quot.h:39 (quot_reduce_rec) expect="quot_reduce_rec"
fixtures: stub owner=franken_lean-z6c
`Quot.lift f h (Quot.mk r a) ⟶ f a` (mk at position 5, f at 3);
`Quot.ind p (Quot.mk r a) ⟶ p a` (mk at 4); trailing arguments preserved; active
only when initialized.

---

## 11. Declaration admission (KR-97x)

### KR-970 · One name, one constant
anchor: vendor/lean4-src/src/kernel/environment.cpp:102 (check_name) expect="check_name"
fixtures: stub owner=franken_lean-z6c
Every added constant's name must be fresh; fln-env enforces the same law as a typed
refusal.

### KR-971 · Distinct level parameters
anchor: vendor/lean4-src/src/kernel/environment.cpp:111 (check_duplicated_univ_params) expect="check_duplicated_univ_params"
fixtures: stub owner=franken_lean-z6c
A declaration's universe parameters must be pairwise distinct.

### KR-972 · Well-formed constant preamble
anchor: vendor/lean4-src/src/kernel/environment.cpp:127 (check_constant_val) expect="check_constant_val"
fixtures: stub owner=franken_lean-z6c
Fresh name, distinct level params, closed type (no mvars/fvars), and the type
itself checks to a sort.

### KR-973 · Axioms
anchor: vendor/lean4-src/src/kernel/environment.cpp:152 (add_axiom) expect="add_axiom"
fixtures: stub owner=franken_lean-z6c
An axiom is its checked type; no body, no defeq obligation.

### KR-974 · Definitions, theorems, opaques
anchor: vendor/lean4-src/src/kernel/environment.cpp:160 (add_definition) expect="add_definition"
anchor: vendor/lean4-src/src/kernel/environment.cpp:192 (add_theorem) expect="add_theorem"
anchor: vendor/lean4-src/src/kernel/environment.cpp:211 (add_opaque) expect="add_opaque"
fixtures: crates/fln-kernel/tests/k1_judgments.rs, crates/fln-kernel/tests/checked_declaration_capability.rs
The body's inferred type must be defeq to the declared type; theorems additionally
require a Prop-valued type; unsafe definitions check header-first to permit
recursion. Opaques are checked with the ordinary safe checker even when their
`isUnsafe` metadata bit is set; an accepted opaque publishes as opaque and its body
never becomes a delta-reduction rule.

### KR-975 · The unsafe quarantine
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:101 (infer_constant) expect="is_unsafe"
fixtures: stub owner=franken_lean-z6c
Safe code may not reference unsafe declarations; unsafe code may reference
anything. One-directional, no exceptions.

### KR-976 · The partial quarantine
anchor: vendor/lean4-src/src/kernel/type_checker.cpp:105 (infer_constant) expect="partial"
fixtures: stub owner=franken_lean-z6c
Safe definitions may not reference partial definitions.

### KR-977 · Mutual definitions are unsafe-only
anchor: vendor/lean4-src/src/kernel/environment.cpp:224 (add_mutual) expect="add_mutual"
fixtures: crates/fln-kernel/tests/k1_judgments.rs, crates/fln-kernel/tests/checked_declaration_capability.rs
A mutual definition block must be non-empty, must not be tagged safe, and all
members must share one safety annotation. Every header checks against the original
environment, every member is then visible in one private scratch environment, and
only then is each body checked defeq to its type under one shared budget. Failure
publishes no prefix. FrankenLean additionally applies KR-970 inside the private
scratch block and refuses a duplicate member name; the pin's unchecked `add_core`
loop would overwrite that malformed raw block member.

### KR-978 · The unchecked door is not a rule
anchor: vendor/lean4-src/src/kernel/environment.cpp:275 (lean_add_decl) expect="lean_add_decl"
fixtures: crates/fln-kernel/tests/checked_declaration_capability.rs, crates/fln-kernel/tests/consensus_seat.rs, crates/fln-kernel/tests/k1_judgments.rs
The Reference exposes an add-without-checking entry point. In FrankenLean nothing
outside `fln-kernel` can admit a constant (FL-INV-02); trust-level bypasses are
journaled and surfaced in receipts, never silent (plan §4.1 wire/CLI row). An
acceptance mints a private, non-serializable, single-use capability bound to the
exact declaration and immutable base environment; council agreement is the only
transition to publication. Multi-constant declarations stage their checked rows in
private persistent environments and expose only the complete final environment.
A duplicate, resource stop, cancellation, or internal fault at any member exposes
no accepted prefix.

---

## Revision law

This document is versioned per epoch. Amending a rule statement is a reviewed
change that must touch the rule's linked fixtures in the same change (enforced
during review; mechanized as part of the verification-manifest work under
franken_lean-rur). Anchors are re-verified against every epoch advance; a drifted
anchor blocks the epoch claim until the rule is re-confirmed or a Behavior Note
records the divergence.
