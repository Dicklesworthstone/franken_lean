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
compilation or Reference ABI parity. The existing source branch-omission prover
can now compile its supported constructor clashes through the empty eliminator;
see the section below. Arbitrary impossible index combinations of an otherwise
inhabited family do not become empty-case bindings. Mutually defined
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

## Ordinary nonempty patterns

`examples/native_impossible_patterns.lean` uses an ordinary `match` to obtain
`A` from `Vec A (Nat.succ n)` without writing a dummy nil arm or a manual proof
argument. It also selects the sole possible constructor of a Boolean-indexed
sum whose other constructor has a different payload type. Both logical checkers
still check the elaborator's generated evidence before runtime preparation.

Constructor discrimination now first derives `False` in `Prop`, then uses the
ordinary `False.rec` at a data-valued target. Previously, its intermediate type
code could require an impossible transport between incompatible data layouts.
The runtime representation-equality guard was correct and is unchanged. The
new proof construction also serves `cases`, `contradiction`, and `injection`.
Minimal embedding environments without the exact False family and recursor keep
the prior proof-construction scheme; no seed or assumption is synthesized there.

No source coverage shortcut was added: omitting an inhabited arm is still an
error, explicitly supplied arms remain type-checked even when their index is
impossible, and invalid applications never produce an executable artifact.
Engine and installed-command regressions cover scalar, String and object heads,
large literal index clashes, imports, independent replay and failure recovery.

Nested dependent tail/head composition now executes with the unchanged default
one-million-node preparation budget. The scope-transform preflight charges the
subtrees the core actually visits rather than a product including unrelated
closed proofs; see `NATIVE_DEPENDENT_PROGRAMS.md`. Genuine preparation exhaustion
still refuses without publication and recovers with a sufficient caller budget.
Escaping generated proof continuations can now perform strict work and return
owned callbacks. Ordinary omitted-pattern vector heads therefore also support
captured and multiargument callback payloads. Local lambda spines are registered
at their real arity, with a represented function suffix returned as a closure;
strict work is not eta-expanded across this local boundary. Typed annotations
inside the prefix let the existing compiler independently check the returned
lambda, captures, calls and ownership. The global flat-function ABI is unchanged.

`examples/native_staged_callbacks.lean` combines a strict local factory with an
ordinary nonempty-vector head and independent installed FLBC replay. Tests compare
VM work for cheap/costly prefixes to verify that discarding the returned callback
does not discard prefix computation, repeated invocations share it, and merely
constructing the outer lambda does not run its body. Returned callbacks can be
stored in records and collections after their prefix has completed.

This does not coerce different closure ABIs. A recursively staged returned
callback has a different interface from a flat multiargument callback; the
compiler still rejects a mismatched return interface. General adaptation between
these interfaces is outside this increment and is covered as a typed refusal,
not as supported execution. Neither checker nor the compiler's exact lambda-spine,
return-type, capture, argument or ownership checks were weakened.
