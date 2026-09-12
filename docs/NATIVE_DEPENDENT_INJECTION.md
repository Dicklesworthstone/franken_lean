# Dependent constructor fields

Native `injection` now retains fields whose types depend on preceding fields or
family indices. If the original selector construction cannot expose every field,
the elaborator constructs a continuation proof using the ordinary admitted family
recursor and `Eq.rec`. Both checking engines still check the completed source
term. There is no additional admission authority or axiom.

```lean
structure Package where
  carrier : Type
  value : carrier

theorem values (A B : Type) (a : A) (b : B)
    (h : Package.mk A a = Package.mk B b) : HEq a b := by
  injection h with types values
  subst types
  exact heq_of_eq values
```

The existing selector path still gives `A = B` and a checked cast-based value
equation. After substituting the type equation, `heq_of_eq` converts the resulting
ordinary equality into HEq. No equality between ill-typed endpoints is invented.
The source seed contains checked `HEq`, `HEq.refl`, and `HEq.rec`. K1 regenerates
the family and its eliminator; the independent checker validates its canonical
shape separately.

## Continuation construction

At the original constructor, the family recursor returns
`(fieldEq1 -> ... -> fieldEqN -> target) -> target`. Its reflexive proof supplies
`Eq.refl` or `HEq.refl` for every field to the continuation. Transport along the
actual constructor equality yields that continuation at the other constructor.
The remaining source proof becomes its argument, abstracted over fresh field
proofs. Constructor fields and recursor hypotheses are bound in the generated
minor premises; no hidden induction hypothesis becomes a source assumption.

The recursor abstracts the full index telescope. When the selector path cannot
expose every field, this fallback supplies the complete field list, using HEq
where field domains depend on preceding values or indices. Independent payloads
keep ordinary equalities. This includes proof-valued fields of data records; a
record with a type, a value, and a proof about that value keeps all three fields.
Names follow complete constructor order; `_` is anonymous, and duplicate or
excessive names still refuse. Successful existing selector paths retain their
original cast-based equations, including homogeneous vector-tail equations.

The original equality and its proof-dependent users remain in scope. Generated
field hypotheses stay branch-local and close with the descendant proof. Invalid
annotations, unused ill-typed arguments and false field proofs are not erased
before checking. The existing selector-based contradiction search, empty-family
elimination, negation handling, and compact large-Nat proofs are preserved.

## Checked equality bridges and heterogeneous substitution

Five ordinary, universally quantified seed theorems connect the relations:
`heq_of_eq`, `eq_of_heq`, `type_eq_of_heq`, `HEq.symm`, and `HEq.trans`. Both
checking engines admit their full proof terms. They are not axiom declarations,
unifier exceptions, or instructions to change an expression's recorded type.
In particular, `eq_of_heq` eliminates HEq with an additional type-equality
argument and an explicit Eq.rec cast before specializing that argument to
reflexivity. This needs no assumed proof irrelevance.

`subst h` accepts a named HEq hypothesis. If endpoint types are convertible it
applies `eq_of_heq` and uses the existing dependent-substitution engine. If the
types differ and one can be eliminated as a local type variable, it first uses
`type_eq_of_heq`, transports the dependent context, and then substitutes the
values. These are at most two explicit equality transports, not unbounded
recursive tactic execution. Local lets, data, and hypotheses depending on the
original HEq proof are reintroduced under fresh identities. The consumed proof
name is hidden, but its actual evidence remains in the generated core term.

```lean
def recover (A B : Type) (a : A) (b : B) (h : HEq a b) : A := by
  subst h
  exact b

theorem predicate_transport (A B : Type) (a : A) (b : B)
    (h : HEq a b) (P : forall T : Type, T -> Prop) (pa : P A a) : P B b := by
  subst h
  exact pa
```

`rfl` constructs HEq.refl for heterogeneous goals only after constraining both
domains and endpoints. `injection` and `contradiction` can consume same-type HEq
through `eq_of_heq`, preserving their previous constructor and compact-literal
proof paths. Heterogeneous endpoints at genuinely unrelated type applications
are not presumed to have injective type constructors: unsupported substitutions
remain typed refusals. The variable-name form `subst x` retains its existing
ordinary-equality semantics; heterogeneous substitution selects its witness.

This is not complete index-equation refinement. Proof-valued families and
families of unknown proposition/data status are not injective computational data.
Existential-proof equality cannot expose hidden witnesses. No named noConfusion
declarations or primitive equality axioms are generated.

```bash
fln check-source --json examples/native_constructor_equalities.lean
fln check-source --json examples/native_heterogeneous_equality.lean
```

The constructor example checks nine commands and seven theorems; the heterogeneous
example checks ten commands and eight theorems. Source tests also
cover mixed field ordering, indexed tails, core proof dependencies, negative
proof-irrelevance cases and multi-file failure isolation. Package-level results
are not a full Reference conformance or whole-workspace test claim.
