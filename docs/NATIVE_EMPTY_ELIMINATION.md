# Native execution of empty elimination

After ordinary kernel and independent-checker admission, native execution can
compile eliminations of supported zero-constructor families. `False.rec` and the
ordinary checked `False.elim` definition now work in impossible branches of
proof-constrained programs. `examples/native_empty_elimination.lean` selects the
head of a nonempty length-indexed vector and handles an `Option NeverValue` to
produce 42. The installed tests use both source personalities, imports, and
independent serialized FLBC replay.

## A non-returning operation, not an invented value

The compiler exposes a typed empty-case binding whose only terminal operation
is an existing FIR/FLBC panic. There is no return edge and no synthesized default
Nat, String, object, or callback. The binding is untrusted compiler input, not
logical evidence of emptiness; normal FIR, ownership, and bytecode validation
still apply. Lower-level tests deliberately execute these calls with fabricated
runtime arguments and verify that they panic rather than return a value.

The runtime recognizes empty eliminators from admitted inductive and recursor
metadata: one family, zero constructors, one motive, zero minors and reduction
rules, matching parameter/index counts, and the actual major-premise family in
the instantiated telescope. The seeded `False` family and its recursor receive
an additional full-object identity check. Private callable names cannot shadow
admitted declarations. Neither logical checker is modified.

Proofs remain checked before the existing proof-erasure pass removes their
computations. Ordinary value parameters, indices, and empty data arguments
remain strict and retain their source evaluation order. A non-returning call
precedes any overapplication arguments, even when its nominal result is a
callback. Empty arms remain lazy under matches and recursive eliminators; a
reachable ordinary constructor field is not erased merely because it is unused.

## Supported data and result types

Empty data types have zero-constructor layouts; no runtime constructor is added.
They can appear inside otherwise inhabited records, variants and collections,
including `Option Void`. Ground type parameters and supported scalar indices
use the existing runtime specialization and index-erasure machinery. Empty
propositions with ordinary value parameters are also supported.

Results may be Nat, Bool, String, represented objects, or typed closures. This
allows proof-constrained vector heads to return records and captured functions,
not only scalars. Both `False.rec` and user-defined empty recursors can appear
inside checked wrapper functions, curried callbacks, and overapplications.
The source seed now wires in the existing ordinary definitions `False.elim` and
`Ne`; these add no axioms and still pass both admission seats.

## Boundaries and evidence

This is a bounded native runtime surface, not complete dependent-pattern
compilation or Reference ABI parity. It does not automatically prove omitted
source branches impossible. Arbitrary impossible index combinations of an
otherwise inhabited family do not become empty-case bindings. Mutually defined
empty groups, unresolved or representation-dependent result types, and bare
partially supplied recursor constants are outside this increment. A checked
wrapper can be partially applied using the existing callable machinery.

Open proposition-parameter decision computations are a separate runtime gap;
this change does not claim arbitrary proof-directed conditionals now execute.
A closed-proposition conditional with an explicitly supplied checked decision
is covered.

Regressions exercise proof-constrained vector heads, empty data nested inside
inhabited values, indexed empty data, erased proofs, strict ordinary fields,
owned and callable results, metadata/name guards, bounded preparation, unchanged
logical environments, invalid-evidence nonpublication and deterministic recovery.
