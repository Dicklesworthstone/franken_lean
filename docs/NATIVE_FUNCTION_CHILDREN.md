# Checked function-valued recursive children

A constructor field may be a dependent function returning the same inductive
family, with the original parameters and universes and potentially changing
indices. Its argument domains cannot contain the family. For example:

```lean
inductive Branching where
  | leaf (value : Nat)
  | node (children : Nat -> Branching)
```

The `node` branch of induction receives `children : Nat -> Branching` and
`ih : forall n, motive (children n)`. Dependent arguments and result indices are
preserved. Ordinary case analysis and `match` open the same recursor telescope
but do not expose induction hypotheses to source proofs or instance search.

The candidate generator and the independent checker build the corresponding
function-valued induction hypotheses and recursive reduction rules separately.
The checker relocates ambient bounds without moving the recursive function's
own binders. It derives the recursive/reflexive flags from constructor types,
checks field universe bounds, and rejects negative occurrences and forged rules.
K1 independently regenerates the candidate using its existing implementation.
No primary-kernel change or new axiom is needed.

This enables accessibility-shaped propositions:

```lean
inductive Accessible (A : Type) (R : A -> A -> Prop) : A -> Prop where
  | intro (x : A) (next : forall y : A, R y x -> Accessible A R y) : Accessible A R x
```

Its singleton eliminator can compute dependent data: the data field `x` is
exposed in the result index and `next` is a proof. An existential-style predicate
with a hidden data field still cannot eliminate into data. This is checked by
both engines, not asserted by the caller or a metadata flag.

## Automatic source recursion on applied children

Ordinary source definitions can call themselves on an immediate function-valued
constructor field after supplying that field's complete argument telescope:

```lean
def follow (t : Branching) (route : Nat) : Nat := match t with
  | .leaf n => n
  | .node children => follow (children route) (route + 1)
```

The call becomes `ih route (route + 1)`: the recursor's actual function-valued
hypothesis receives the child-function arguments before any generalized function
arguments. Dependent proof arguments and the child's actual indices are retained.
Fixed/repeated-index recursion uses the same rule, followed by its checked
conditional index equations. Multiple recursive fields of different arities keep
their original hypothesis order. Equation-style declarations, later structural
columns, recursive matrices and partial self-applications after the child are
supported by the existing shared lowering paths.

An accessibility fold can therefore be written without manually spelling an
induction proof:

```lean
def foldRecursive (A : Type) (R : A -> A -> Prop) (P : A -> Type)
    (step : forall x : A, (forall y : A, R y x -> P y) -> P x)
    (a : A) (h : Accessible A R a) : P a := match h with
  | .intro x next => step x (fun y hy => foldRecursive A R P step y (next y hy))
```

This consumes explicit accessibility evidence. It does not infer well-foundedness
or prove a decrease for an arbitrary relation. The resulting core term contains
the admitted recursor, not a recursive axiom or a self-referencing definition.
The example evaluates a genuine predecessor call under a two-point relation,
in addition to the empty-relation case and a universal induction proof about a
function-child recursive program.

The structural field is identified from its admitted constructor slot, never by
guessing from a function's return type. Calls are lowered while local aliases and
lambda arguments still have their actual scope; the private hypotheses remain
hidden from ordinary proof and instance search. A shadowed function returning the
original input cannot impersonate the child. Every supplied child argument is
traversed and retained, including ignored arguments and type annotations. Nested
valid child calls are lowered; a hidden nondecreasing call still refuses. Partial
child functions are not accepted as data children. Resource stops remain
nonanswers and failed file suffixes expose no successful successor environment.

Run `fln check-source --json examples/native_function_children.lean` to check
construction, matching, function-valued induction, source recursion and both
forms of dependent accessibility folding.

This is single-family strictly positive function recursion, not nested or mutual
inductive support. The existing explicit result-type, root-match and immediate
child restrictions remain. General well-founded termination synthesis,
grandchild/course-of-values recursion and `termination_by` are separate layers.
Kernel conversion and source admission are exercised; full execution-backend,
Reference syntax/generated-name parity and the pinned Prelude council are not
established by the scoped tests.


## Native runtime execution

The native runtime accepts admitted non-indexed, single-family data whose
recursive fields return that family after taking nondependent runtime arguments.
For example, `children : Nat -> Branching` is stored as an owned closure, not
expanded into a tree while compiling or constructing its parent.

Source matches and structural recursive calls on applied children execute through
the existing checked recursor and native closure paths. Child functions can have
multiple arguments, including explicitly bound callbacks. Ground type parameters,
owned string payloads, changing accumulators, and maps returning new child
closures are supported. `examples/native_function_child_runtime.lean` maps a tree and
later traverses its returned closures, producing `42`.

The representation worklist uses provisional data anchors to resolve callbacks
whose result is their enclosing family. A refused or exhausted discovery removes
every new anchor, callable interface, and constructor binding; it does not expose
a partially validated runtime layout. This affects post-admission compilation
only. Both logical checkers still check the original source declarations.

An induction hypothesis for a function field is itself a closure: applying it
selects the child and invokes the recursive computation. Its native lambda spine
includes both child arguments and the motive's accumulator arguments. Unused
hypotheses do not invoke child functions; computed constructor fields remain
strict. This is not memoization of repeated applications of a child function.

The regression targets are `runtime_function_children` in `fln`, the layout
discovery unit tests, and `source_mutual_data` in `fln-cli`. The installed tests
also run serialized FLBC in a new process without the source environment.

Value-dependent fields and motives, indexed runtime families, proof erasure,
nested recursive containers, and mutually recursive function fields remain
outside this increment. Inline lambda arguments to dynamic callback calls retain
the existing runtime limitation; explicitly bound local callbacks are supported.
No full Reference ABI parity, whole-program performance claim, or Golem parent
bead closure is implied.