# Native equality transport and index-refining matches

After ordinary kernel and independent-checker admission, the native runtime can
lower the canonical seeded `Eq.rec` to its transported payload when both endpoint
types erase to exactly the same runtime type. It checks the full seeded equality
family, constructor and recursor metadata, not just the spelling `Eq.rec`.

This enables explicit proof-justified casts of scalar values, ground objects and
callbacks, including length-indexed vectors. It also enables source matches whose
constructor fields refine indices: the elaborator's existing checked transports
can run without changing or bypassing the proof-generating match elaborator.
`examples/native_equality_transport.lean` recursively copies a `Walk n` using such
matches, folds it, and transports the result to produce 42. The installed tests
run it through both source entry points and independent serialized FLBC replay.

## Evaluation and representation

Runtime equality evidence remains erased, but ordinary endpoint values and the
transported payload are evaluated in source order and shared in strict lets.
Type-valued endpoints are static. A syntactic lambda constructs no computation;
fully supplied transports of literal lambdas can expose their beta spine while
retaining strict initializer and argument evaluation. Reassociation of a let in
function position lifts application arguments capture-avoidantly and never
substitutes its initializer, preserving sharing.

Transport accepts equality of the complete erased source and target types. Merely
having the same FIR machine category is insufficient: two constructor layouts
with different field types cannot be used interchangeably. Logical equality of
indices may change an indexed type such as `Vec Nat n` without changing its
runtime family layout. Ground type equality such as `Nat = Nat` is also supported
after ordinary type specialization. No test claims to fabricate evidence for a
false equality; a separate internal negative control checks that even fabricated
post-admission evidence cannot bypass the representation guard.

## Limits

This remains a bounded native profile, not general dependent-runtime or Reference
ABI parity. Representation-changing casts, opaque or noncanonical equality
families, unresolved type parameters and unsupported carrier/result layouts are
refused. Bare partially supplied recursor constants are not a new callable
surface; ordinary checked wrapper functions and transported callbacks can be
partially applied. Source elimination requiring proof of impossible branches may
still need a separate runtime lowering for the empty eliminator. Neither checker
nor logical environment semantics are changed.
