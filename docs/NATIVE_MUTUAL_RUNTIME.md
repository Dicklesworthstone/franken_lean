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

## Full mutual folds

Ground primitive recursors such as `Tree.rec` and `Forest.rec` also support
induction hypotheses. Every member is lowered into a member of one native
mutually recursive closure group. The compiler supplies a shared acyclic capture
environment, including outer values read only by a sibling; no reference-counted
closure cycle or unchecked global helper is introduced.

Each motive supplies its own checked runtime interface. Peers can return
different scalar/object types and have different nondependent accumulator
telescopes. Partial recursive applications remain typed closures. Used induction
hypotheses are let-bound once per recursive field; unused hypotheses never force
their sibling subtrees. Nested folds are prepared with explicit heap frames.
Dependency discovery reaches a fixed point over newly prepared peer bodies,
including intrinsics and ordinary functions absent from the selected member.

`examples/native_mutual_folds.lean` demonstrates type-parameter specialization,
different peer arities, and an offset captured by only the Tree peer. Tests also
cover three-member groups, heterogeneous String/Nat motives, returned sibling
objects, nested group dependencies, deterministic replay, resource-stop recovery,
and preparation in a 128 KiB host thread. The shared-IH regression computes
2^28 from a shared tree in fewer than 10,000 VM steps, instead of recursively
duplicating a used hypothesis. It does not claim global memoization across
separate constructor fields.

This increment supports closed, non-indexed families with uniform static type
parameters and representable, nondependent fields. Proof/value-dependent fields,
higher-order recursive fields, nested recursive type constructors, and dependent
motives remain unsupported. Source-level mutually recursive `def` groups are not
added: full folds use the already checked primitive mutual recursors. Unsupported
layouts or folds remain typed refusals. These are native FIR layouts, not a claim of Reference
packed-object ABI parity or completion of the Golem integration workstream.