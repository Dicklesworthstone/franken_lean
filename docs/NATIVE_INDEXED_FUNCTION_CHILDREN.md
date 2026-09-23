# Native indexed function-valued recursive children

Admitted single inductive families with uniform runtime layouts and independent
Nat, Bool or String indices can contain positive recursive children selected by
functions. A field `(i : Nat) -> Tree i` is an owned closure. Its result index may
depend on the callback arguments and earlier constructor fields. Source structural
recursion and induction on these children execute through the existing checked
recursor and native closure pipeline.

`examples/native_indexed_function_children.lean` maps an index-preserving function
over a branching indexed tree, then traverses the returned child closures to
produce 42. Both installed source entry points and independent serialized FLBC
replay exercise that example. Ground element-type specializations, several child
arguments and indices, captured accumulators, and checked proof arguments are
covered by engine regressions.

## Keep the actual indices in the right scope

Layout derivation still erases indices from runtime type identities, not from
ordinary computations. The recursor now opens the actual constructor-field type
through precisely the checked callback telescope. Its domains must erase to the
same argument representations as the field's runtime interface, and its target
must remain the same indexed family. No child is executed to discover its type,
and no fabricated index is substituted.

The recovered index expressions are scoped under the child argument binders.
Generating the recursive hypothesis adds accumulator binders after those arguments;
only those additional binders shift the index expressions. Preceding constructor
fields, selected child arguments, and captured outer values retain their original
scope. A structural unit control checks the resulting expression with two child
arguments and two added accumulators independently of source elaboration.

Calling a recursive hypothesis computes its actual indices, invokes the selected
child, and then invokes the recursive function, retaining ordinary evaluation
order. Unused hypotheses still do not invoke children or their index computations.
Repeated calls of a child function are not memoized. Tests compare the exact VM
step growth of one versus two ordinary index computations, rather than accepting
a constant result as proof that those computations were retained.

## Authority and limits

Both original admission engines check the complete source first. Invalid child
indices, nonpositive fields and nondecreasing recursion still fail without
publication. Resource exhaustion retains the logical input; a successful retry
produces byte-identical artifacts. Mutually indexed families with direct recursive
fields are supported separately (`NATIVE_MUTUAL_INDEXED_RUNTIME.md`); function-valued
mutual recursive children, type-indexed GADTs, dependent callback argument
representations, and value-dependent runtime layouts remain unsupported. Neither checker, the logical constructor or
recursor metadata, nor the runtime representation-equality guard is weakened.
