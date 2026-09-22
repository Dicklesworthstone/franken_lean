# Native execution of mutual data

The checked-source execution path accepts a `mutual` inductive block as one
admission unit. Every member and generated declaration still passes the kernel
and independent checker before it can supply executable metadata. The parser
retains original module offsets, and imported blocks retain their ownership.

Runtime preparation derives every member layout together at the same closed
type arguments. Constructor tags are family-local; projections and cases select
the exact constructor layout, not a global tag. Ground instantiations such as
`Tree Nat`, `Tree String`, and `Tree (Nat -> Nat)` have distinct metadata. Direct
self and sibling fields are constructor objects; nondependent function payloads
are owned closures with checked call interfaces.

Ordinary matches, nested matches, and matches that return functions execute
natively. Preparation opens the selected minor premises with private induction-
hypothesis markers and admits this case-only path only when no marker survives.
It does not invent an induction hypothesis or evaluate an irrelevant sibling
recursor. A syntactic lambda argument is an inert function value and can be
beta-substituted while exposing those premises; computed function arguments keep
their strict let binding. Constructor fields remain strict and branches lazy.

`examples/native_mutual_data.lean` executes through `fln run` and the `lean`
personality and emits FLBC that an independent `fln flbc run` process replays.
Engine tests compare work counts, resource-stop recovery, distinct ground types,
and deterministic bytecode. CLI tests cover imports, false theorem suffixes,
malformed groups, positivity violations, and no output/artifact publication on
failure.

This increment supports closed, non-indexed families with uniform static type
parameters and representable, nondependent fields. Proof/value-dependent fields,
higher-order recursive fields, nested recursive type constructors, and full
mutual folds are not added by the case-only path. Unsupported layouts or folds
remain typed refusals. These are native FIR layouts, not a claim of Reference
packed-object ABI parity or completion of the Golem integration workstream.