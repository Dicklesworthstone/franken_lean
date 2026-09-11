# Native constructor equality

`injection h with h1 h2` derives constructor-field equalities from a local
homogeneous equality. The bare `injection h` form chooses fresh hypothesis names;
`assumption` can use them. Underscores leave a generated hypothesis anonymous.
Both endpoints must expose constructors of the same admitted data family.

For different constructors, `injection h` closes the goal by disjointness. For the
same constructor, it appends the supported homogeneous field equalities, in field
order, as checked local lets. The original equality remains available, including
when later hypotheses depend on its proof. Extra or duplicate names refuse.

```lean
theorem predecessor (x y : Nat) (h : Nat.succ x = Nat.succ y) : x = y := by
  injection h with predecessor_eq
  exact predecessor_eq

def impossible (x : Nat) (h : 0 = Nat.succ x) : String := by
  injection h
```

## Proof construction

There is no new axiom, trusted no-confusion primitive, or admission authority.
The tactic constructs an ordinary admitted recursor whose
branches select a field, using the actual left field as the other branches'
fallback. Applying `Eq.rec` to the supplied equality proves equality of those
selected values. Recursive hypotheses in the selector are bound but not used.
Indices are generalized by the recursor, so fixed/repeated input indices do not
require inventing branch equations merely to select an independent payload.

Disjointness constructs a type-valued discriminator: the left constructor maps
to `T -> T`, the right to the goal `T`. Transporting the identity function along
the actual equality proves the goal. Every branch and transport remains in the
final term submitted to K1 and the independent checker.

Proof-valued families are excluded: equality of proof constructors cannot expose
existential witnesses or distinguish disjunction evidence. Only the admitted
single-family, non-nested, direct-recursion lane is selected. Malformed source,
unsupported operations and failed files publish no successful environment prefix.

## Dependent fields and equality transport

A field whose type depends on preceding fields is selected with two recursors:
a type selector `D : F -> Sort u` and a value selector `d : (x : F) -> D x`,
both generalized over the family's indices. Equality induction produces
`cast (congrArg D h) (d left) = d right`. This is a homogeneous equality at the
right-hand field's type, with the actual type-equality transport retained in its
proof. It is not an unchecked heterogeneous comparison.

When the field domains are already convertible, the admitted equality K rule
makes the cast the identity and the tactic exposes the ordinary field equality.
This includes vector tails and data payloads of dependent records. Otherwise the
cast remains explicit. After substituting the preceding type equation, `subst`
can recognize a now-reflexive cast and solve the payload equation while retaining
the original witness in the parent proof:

```lean
structure Package where
  carrier : Type
  value : carrier

theorem package_transport (P : forall A : Type, A -> Prop)
    (A B : Type) (x : A) (y : B) (hx : P A x)
    (h : Package.mk A x = Package.mk B y) : P B y := by
  injection h with sameType sameValue
  subst sameType
  subst sameValue
  exact hx
```

Dependent proof-valued fields which need this selector construction are omitted;
they are not data injectivity goals. Families in `Prop` remain excluded entirely.
This does not introduce general heterogeneous-equality syntax, generated
`noConfusion` declarations, or full fixed/repeated-index elimination.

## Independent cast conversion

The checker's existing equality K reduction now consumes telescope arguments
capture-avoidantly: replacements are lifted over the remaining slots before
substitution. Open variables inside inserted arguments cannot be rewritten by a
later slot substitution. A metered application-congruence check can reduce
computed endpoint types by checker-owned weak-head reduction. Binder bodies which
would require a shifted context stay on the structural-only path. Unsafe and
partial definitions remain closed.

Work spent by a failed K gate remains charged, but is no longer mistaken for a
change to the compared term. The conversion worklist detects a zero-shift
structurally unchanged result instead of retrying the same stuck cast until the
budget expires. Distinct endpoints still remain stuck; neither resource
exhaustion nor failure of the sufficient conversion check implies equality.

## Automatic contradiction

`contradiction` searches local evidence in deterministic order. It eliminates
proofs of admitted empty families, combines a proof with a local function from
that proposition into an empty family, and detects constructor clashes under
nested constructor equalities using the same proof-producing selectors as
`injection`. Injected equalities can also discharge the domain of a negation.
Reflexive equality supplies evidence for a negation even without a named proof.

Unequal arbitrary-precision Nat literals are mapped by the admitted `Nat.beq`
primitive to a Bool constructor clash, with `Eq.rec` retaining the original
equality proof. Both checkers validate the arithmetic conversion. This avoids a
unary traversal even for adjacent numbers above 2^128. Consistent literal
identities and equalities between proposition constructors do not close goals.
Work is metered and repeated endpoint pairs are memoized with their allocations
pinned for the request. No temporary selector, axiom or unproved declaration is
registered in the environment.

```bash
fln check-source --json examples/native_constructor_equality.lean
```

The example includes dependent transport across differing payload types, obtained
by combining `injection` and `subst`, as well as record fields, nested clashes and
a 129-bit Nat contradiction.
This is bounded constructive reasoning, not a complete contradiction solver.
