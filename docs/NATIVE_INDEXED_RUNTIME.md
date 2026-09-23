# Native execution of value-indexed data

The native runtime accepts admitted single inductive families with independent
`Nat`, `Bool`, or `String` index domains and uniform executable field layouts at
fixed type parameters. Length-indexed vectors can be constructed, matched,
folded, mapped and returned at refined indices. Multiple indices and multiple
direct recursive fields are supported. The seed's ordinary kernel and independent
checker still admit every original declaration and application first.

`examples/native_indexed_vectors.lean` maps an index-preserving function over a
vector and sums the result to 42. It runs through `fln run` and `lean`; its emitted
FLBC also runs independently of source elaboration.

## Representation and evaluation

A separate, bounded type-erasure worklist removes index arguments from runtime
family identities. It does not alter logical normalization or checker inputs.
All lengths at the same type parameters share a layout; different element types
retain distinct field layouts. Nested collections and record fields may contain
these indexed values. Type-only local obligations retained by source matching
are substituted only after admission, not compiled as executable callbacks.

Constructor fields, explicit function/index arguments and recursive-call indices
remain ordinary, strict runtime computations. Recursive calls reconstruct their
indices from each admitted constructor-field telescope, with prior fields rebound
to actual projections. They do not guess lengths or evaluate the receiver to find
its type. Every used induction hypothesis is let-bound once; unused hypotheses
remain lazy, following the existing recursive runtime lowering.

A motive may depend logically on the indices while its erased runtime result is
uniform, including `Vec A n` and fixed-representation accumulator functions. The
runtime checks that removed motive binders have no remaining occurrences. Proof
fields and evidence use the existing post-admission proof erasure; observable
`Decidable` tags are not collapsed. No private runtime representation is published
as a logical declaration.

## Boundaries

Type-indexed GADTs, index domains depending on prior indices, mutually indexed
families, indexed function-valued recursive children and genuinely value-dependent
field representations remain unsupported. Scalar indices alone are not sufficient:
the full constructor layout must be representable. This is a native FIR profile,
not Reference packed-ABI parity. Index-refining matches using canonical equality transports are supported when
the erased source and target layouts agree; see `NATIVE_EQUALITY_TRANSPORT.md`.
Checked eliminations of supported zero-constructor families can execute in
impossible branches; see `NATIVE_EMPTY_ELIMINATION.md`. This does not add general
source-pattern coverage or automatic proofs for omitted branches.

Regression coverage includes invalid-length rejection, preserved logical roots,
strict ordinary computation, shared recursive work, deterministic resource-stop
recovery, type-indexed/existential representation refusal, small-stack type erasure,
both installed entry points, imports and independent serialized FLBC replay.
