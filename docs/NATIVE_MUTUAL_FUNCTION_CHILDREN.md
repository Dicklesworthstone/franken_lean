# Native execution of function-valued mutual children

After admission by both logical checkers, mutually recursive families can contain
function fields returning any member of the group. Independent scalar indices
may depend on callback arguments and earlier constructor fields. Unindexed and
indexed members may coexist. The complete group must have uniform represented
fields at its fixed type parameters; recursive positivity is still checked at
logical admission, not inferred from the runtime layout.

`examples/native_mutual_function_children.lean` maps over a mutually recursive
Tree/Forest group, returns new objects with owned child closures, and traverses
those closures after the map returns to compute 42. Both installed source entry
points, imports, and standalone serialized FLBC replay exercise the same program.

## Recursive callbacks

The original checked constructor telescope determines each recursive field's
target, callback arguments, and actual indices. Runtime index erasure does not
erase ordinary index computations. Each generated induction-hypothesis closure
captures the appropriate peer and preceding fields. It accepts the child's
arguments followed by that peer's accumulator arguments, which can differ from
the current member's signature. Accumulator insertion shifts recovered indices
only past the new binders, preserving callback-argument scope.

Creating the hypothesis closure does not invoke the child or compute its indices.
Each call does both in the ordinary evaluation order. Unused hypotheses remain
lazy. Repeated calls are not memoized; only the closure itself is shared in its
let binding. Exact VM-step-growth tests distinguish zero, one, and two calls,
including the constructor's index and the peer-call index. Case-only lowering
recognizes function-valued hypotheses too, rejecting that shortcut when any
private hypothesis survives in the minor premise.

## Representation, validation, and limits

Data anchors for all siblings allow mutually recursive callback layouts to be
discovered without recursive host-stack traversal. Failure or resource exhaustion
removes every new executable anchor, interface, and constructor. A retry using
the descriptive shape cache produces the same bindings as clean discovery.
Different ground element types retain distinct layouts. Proof arguments use the
existing post-admission inert slots, without accepting invalid evidence.

Tests cover different peer index counts and callback/accumulator arities,
three-member cycles, ground specializations, proof arguments, nested matches,
owned mapped closures, strictness, invalid-index/positivity refusal, preparation
and VM resource stops, unchanged logical roots, and byte-identical recovery.
Neither kernel, independent checker, source elaborator, equality transport guard,
nor flat-versus-staged callable-interface validation is weakened.

Type-indexed GADTs, dependent callback argument representations, nested recursive
containers, genuinely value-dependent layouts, and mutually empty groups remain
unsupported. The deeper recursively staged match-result limitation documented
in `NATIVE_MUTUAL_INDEXED_RUNTIME.md` is unchanged. This does not add source
mutual-def syntax or establish Reference packed-ABI parity or a performance win.