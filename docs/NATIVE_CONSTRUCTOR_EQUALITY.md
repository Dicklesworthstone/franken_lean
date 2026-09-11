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

There is no new axiom, no trusted no-confusion primitive, and no semantic change
in either checker. The tactic constructs an ordinary admitted recursor whose
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

## Scope

A selector must have a fixed result type under its whole constructor telescope.
Fields depending on another constructor field cannot in general use such a
selector. They are not silently cast or assigned a homogeneous equality. The
current tactic returns only independently selectable, same-typed fields, in
original order. For example, vector indices and element payloads can be selected,
while the length-dependent tail generally cannot. Full heterogeneous dependent
injection, index-equation refinement and generated `noConfusion` declarations
remain separate work.
