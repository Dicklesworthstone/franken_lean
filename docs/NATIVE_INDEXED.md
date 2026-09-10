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

## Current boundaries

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
instead of becoming independent variables. The source match and structural
recursion compilers still restrict their own lanes to non-indexed families.
Prop-valued indexed family
admission, mutual/nested families, inaccessible patterns, index-equation solving
and explicit source universe declarations remain incomplete. Quantifier syntax
currently requires explicit unparenthesized typed names; grouped binder forms and
inferred-domain quantifiers remain unsupported.

Tests exercise both checkers through real source admission and directly forged
checker inputs. Package tests, scoped Clippy and workspace compilation are not full
Reference parity or a whole-workspace test claim.
