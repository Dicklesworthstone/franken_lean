# Native indexed inductive declarations

The source checker admits single indexed data families with uniform parameters,
dependent index telescopes and direct recursive fields. Indices may change across
constructors and recursive children. Parameters and universe arguments must remain
uniform. The primary kernel regenerates the recursor; the independent checker
separately derives its motive, minors and full reduction rules from the constructor
telescopes using checker-owned expression arenas.

```lean
inductive Vec (A : Type) : Nat -> Type where
  | nil : Vec A 0
  | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)

def two : Vec Nat 2 := Vec.cons 1 7 (Vec.cons 0 9 Vec.nil)
```

The expression after the colon in the family declaration is an index telescope
ending in a positive sort. Constructor result signatures must supply exactly its
indices. A constructor field is a recursive child only when its head is the same
family applied to the unchanged parameters and its own index expressions. Negative,
nested, higher-order and nonuniform recursion are refused. A recursive occurrence
cannot hide inside an index expression. All original annotations and unused source
arguments still reach a kernel type obligation before structural inspection.

## Dependent index domains and universal propositions

Typed `forall x : A, B` and `∀ x y : A, B` terms build ordinary dependent function
types. Domains are checked as types; the body is elaborated under fresh locals and
closed capture-avoidantly. Grouped names share their domain. The universe is the
ordinary impredicative `imax` of the domain and result universes, not a guessed
`Type`. This syntax also makes genuinely dependent family indices available:

```lean
inductive Witness (A : Type) (P : A -> Type) : forall a : A, P a -> Type where
  | intro (a : A) (value : P a) : Witness A P a value
```

The `a` in the family signature is not in a constructor's scope. Each constructor
introduces its own fields, whose types may depend on its previous fields. The
parser uses heap frames for nested quantifier domains and bodies and retains the
original source, including comments and CRLFs.

Run `fln check-source --json examples/native_indexed.lean`. Wrong vector lengths,
wrong index types, forged recursor indices, field-universe violations and false
proofs do not publish a successor environment. Resource exhaustion and cancellation
remain nonanswers. No axiom, external dependency or admission authority is added.

## Cases and induction

The source `cases` and `induction` tactics support indexed families when their
actual indices are distinct parameter locals, including dependent index
telescopes. They abstract those indices in family order, refine them to each
constructor's result indices, and generalize/reintroduce dependent locals and
lets. Induction hypotheses have the actual child's indices, not the original
discriminant's indices. Fixed family parameters cannot be generalized through
this path, and `cases` still hides recursive hypotheses.

`examples/native_indexed_elimination.lean` computes vector length and proves it
equals the type-level length for every vector. It also proves vector copy
identity and extracts a dependently indexed witness. Indexed iota reduction
preserves the distinction between the major's position (after indices) and the
rule's parameter/motive/minor prefix (without indices). Nat literals unify with
the canonical admitted zero/successor constructors one compact layer at a time,
including inference of a large literal's predecessor. No ordinary definition
unfolding policy or checking authority is widened.

This is not complete indexed elimination. Fixed expressions, repeated indices
and let-bound indices require index-equation refinement and currently refuse
instead of becoming independent variables.

## Constructor matches

Ordinary source matches support indexed families whose actual indices are distinct
parameter locals. Later index domains may depend on preceding indices in family
order; the motive closes that telescope without inventing index equations.
Constructor branches receive the
refined expected type, so a vector can be reconstructed at its original length:

```lean
def rebuild {A : Type} (n : Nat) (xs : Vec A n) : Vec A n := match xs with
  | .nil => Vec.nil
  | .cons k x tail => Vec.cons k x tail
```

Dependent ordinary parameters are generalized and specialized in each branch.
Instance-implicit parameters and local lets remain captured. A generalized local's
old version is cleared only when no retained type or let value needs it; this
matters to `assumption` and dictionary search. Pattern names shadow generalized
names without changing their core variable identities. The original discriminant
is still captured at its original type, so returning it directly from a branch
requiring another index is refused.

A final catch-all binds that branch's actual constructor value. A sole catch-all
performs no index refinement and becomes a checked let binding; this also permits
`match xs with | rest => rest` at a fixed index. Its discriminant remains in the
core term even when unused. Ordinary matches keep recursor hypotheses out of proof
and instance search. Every resulting term still crosses both checking engines.

Constructor matches with fixed/repeated indices or inaccessible patterns remain
unsupported. These are bounded source capabilities, not generated-matcher
name parity or full Lean match elaboration.

## Structural recursive functions

Root constructor matches can now elaborate structurally recursive definitions of
indexed data. For example, `copyVec n xs` may recursively call `copyVec k tail`
when `tail : Vec A k` is a direct recursive field. The recursor owns that child's
indices; source calls must supply those actual index expressions, not the outer
length or a guessed conversion. No recursive constant or axiom enters the environment.

Fixed family parameters remain fixed. Index-dependent ordinary arguments before
the decreasing input, and all trailing arguments, are generalized into the motive.
This supports changing accumulators and earlier proof or data arguments whose
types depend on the length. Implicit indices can be inferred. Each branch rebinds
the original index names to its constructor's result indices and the original
input name to the actual constructor, unless shadowed by a pattern binder.

The checked example `examples/native_indexed_recursion.lean` defines vector copy,
map, accumulation, and a computation using the current branch's length; it proves
copy and map identity for every vector. Run it with `fln check-source --json`.
Recursive calls lower to real induction hypotheses and retain every varying
argument, including unused values and annotations. Wrong indices, changed fixed
parameters, nondecreasing calls, and escaping recursive names are refused.

Dependent index domains are supported by both matching and recursive functions.
For `Trace A P a v` with `v : P a`, a child at `x, vx : P x` has a hypothesis at
those indices, not the outer `a, v`. Branch-local aliases for the original indices
have their domains specialized in telescope order. Prefix proofs or data depending
on these indices generalize together with trailing accumulators.

Fixed higher-order parameters can be supplied as exact eta expansions, such as
`fun x => P x`, which implicit inference commonly produces. Each lambda domain
must match the original function's dependent telescope, and every argument must
be its corresponding bound variable. This test does not beta-reduce arbitrary
source expressions or erase annotations. More elaborate inferred fixed arguments
can still require explicit parameter applications. The independent checker also
handles repeated exact eta layers with metered virtual shifts, rejecting capture
of any removed binder; this is not general Pi-driven extensionality.

`examples/native_dependent_indices.lean` checks copying and rebuilding a family
whose second index has type `P a`, with a generic copy-identity induction proof.
The final `rfl` performs ordinary checked conversion after selected simplification.
Run it with `fln check-source --json examples/native_dependent_indices.lean`.

The current recursive source lane uses distinct header-parameter indices and an
explicit result type. Fixed/repeated indices, grandchildren, mutual recursion,
well-founded measures and equation-style definitions remain outside this lane.

Prop-valued indexed family
admission, mutual/nested families, inaccessible patterns, index-equation solving
and explicit source universe declarations remain incomplete. Quantifier syntax
currently requires explicit unparenthesized typed names; grouped binder forms and
inferred-domain quantifiers remain unsupported.

Tests exercise both checkers through real source admission and directly forged
checker inputs. Package tests, scoped Clippy and workspace compilation are not full
Reference parity or a whole-workspace test claim.
