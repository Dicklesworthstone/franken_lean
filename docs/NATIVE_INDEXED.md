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

This increment admits and constructs indexed data. The match, structural-recursion
and induction frontends still have their earlier non-indexed-family restriction;
it does not claim complete indexed elimination. Prop-valued indexed family
admission, mutual/nested families, inaccessible patterns, index-equation solving
and explicit source universe declarations remain incomplete. Quantifier syntax
currently requires explicit unparenthesized typed names; grouped binder forms and
inferred-domain quantifiers remain unsupported.

Tests exercise both checkers through real source admission and directly forged
checker inputs. Package tests, scoped Clippy and workspace compilation are not full
Reference parity or a whole-workspace test claim.
