# Composing native dependent programs

Ordinary nonempty-vector head and tail APIs compose under the existing default
one-million-node runtime preparation budget. The pipeline in
`examples/native_dependent_vector_pipeline.lean` drops two elements and returns
42, using omitted impossible branches and their checked index refinements. The
same path supports generic element types and owned record payloads, both installed
source entry points, imports, and independently replayable serialized FLBC.

## Scope-transform work, not a larger budget

The previous preflight charged the product of the entire body and replacement
syntax sizes before every substitution. That included closed proof syntax and
unused replacements even when the core only cloned an existing subtree. A small
nested head/tail program consequently exhausted its default preparation budget.

The new heap-backed preflight mirrors the existing core transforms' cached
loose-variable cutoffs. It charges every visited enter/reconstruction, and each
required replacement lift at the actual binder depth, before invoking the core.
Closed subtrees and depth-zero lifts are constant-time clones. This does not erase
executable initializers or change source evaluation order: it changes only the
conservative work envelope for capture-avoiding scope operations. The default
budget and every logical admission check are unchanged.

Accounting counts syntax presentations, not allocation identities or hash-table
iteration order. Equal shared and unshared inputs therefore consume the same
budget, even though the core's internal memoization may make actual work smaller.
Deep input uses an explicit worklist, and variable-width overflow remains an
error. Unit controls distinguish the cheap closed substitution the old bound
incorrectly refused from open substitutions requiring actual work under binders,
which still stop before transformation when their budget is insufficient.

## Evidence and boundaries

The nested pipeline regression compiled and exhausted the default preparation
budget before this change. Tests now execute it at that unchanged budget. Small
caller budgets still stop without changing the logical input; recovery produces
the same bytecode. Invalid lengths and malformed imported definitions still
prevent artifact publication. Successful definition execution preserves the
check-only logical environment. Standalone bytecode replay checks the executable
result independently of source preparation.

This is a native-runtime capability correction, not a measured speedup over the
Reference or a general bound on all elaboration work. Neither checker, the core
scope-transform implementation, nor the representation-changing-cast guard is
modified. Unsupported dependent layouts and other documented native profile
boundaries remain unsupported.
