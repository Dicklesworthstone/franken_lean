# Native execution of mutually indexed families

After ordinary kernel and independent-checker admission, native runtime
preparation supports mutually recursive inductive families with independent
`Nat`, `Bool`, and `String` indices and uniform layouts at fixed type parameters.
Each sibling can have a different number and kind of indices; an unindexed
member can participate in the same group. Constructor tags remain family-local.
The logical declarations and both admission engines are unchanged.

`examples/native_mutual_indexed.lean` maps an index-preserving transformation
over a mutually recursive Tree/Forest group, returns newly constructed owned
objects, and sums the result to 42. Installed tests exercise both `fln run` and
`lean`, imported modules, deterministic recovery, and independent FLBC replay.

## Per-member layouts and recursive interfaces

Layout discovery validates the whole admitted group at common static type
parameters. Indices disappear from runtime type identities only; distinct type
parameters retain distinct field layouts. Proof fields use the existing checked
proof erasure. A sibling's index telescope is never inferred from the selected
member's arity or constructor fields.

Mutual recursors become typed native peer-closure groups. Each member receives
its own scalar indices, major premise, and accumulator arguments and can return
a different represented result. Motives may depend on indices when their erased
result is uniform, including indexed objects. The runtime still rejects
remaining value-dependent representation choices. Tests cover heterogeneous
String/Nat-function motives, three-member cycles, ground type specializations,
proof fields, captures and partial accumulator application.

Actual recursive child indices are recovered from the original admitted
constructor telescope. Earlier constructor fields are rebound to their actual
projections before the next field is inspected. A recursive call receives its
target sibling's indices, not the parent's indices. Used induction hypotheses
are let-bound once per field and unused hypotheses remain lazy. This is not
memoization across separate fields or unrelated calls.

Ordinary index arguments and constructor fields still execute strictly. A plain
case split evaluates all explicit indices once, in source order, before its
major premise. Index-dependent helper computations in peer calls are retained.
Step-growth regressions compare zero and costly inputs to detect omitted or
duplicated work independently of the returned answer.

## Source matching and callable results

Nested source matches and supported impossible indexed arms execute through the
existing checked equality-transport and empty-elimination paths. The full
representation-equality guard is unchanged. Revisited private projection keys
must belong to a constructor of the receiver's actual family; sibling keys are
rejected. Boolean decisions inside indexed minors can use logically dependent
motives when that dependence vanishes under the same representation erasure.
Their runtime branches and strict arguments are not substituted away.

Applications of a recursor's returned callback are separated from the
recursor's own arguments. Captured and partially applied fold accumulators are
supported. There is no implicit conversion between recursively staged callback
interfaces and flat multiargument interfaces. A deeper nested source match
returning another callback still encounters this existing `LambdaResultType`
refusal; the regression verifies successful source checking and precise runtime
refusal rather than claiming that shape executes.

## Boundaries and validation

Type-indexed GADTs, dependent index domains, genuinely value-dependent layouts,
and mutually defined empty groups remain unsupported. Function-valued mutual
children now execute in the uniform-layout profile described in
`NATIVE_MUTUAL_FUNCTION_CHILDREN.md`. This does not add mutually recursive source `def`
syntax, Reference packed-ABI compatibility, or a new logical admission path.

Regressions additionally cover inconsistent recursor metadata, group layout
reuse, independent element representations, checked impossible patterns,
invalid indices and reachable branch omissions, preparation/VM resource stops,
unchanged logical roots, and byte-identical recovery. Public source checking
still precedes execution and a stopped batch never publishes partial success.
