# Source recursion at constrained indices

Structural recursive definitions can now have fixed, repeated, shared, and
computed expressions in their input indices. Later index domains may depend on
earlier ones. The source body must be a root constructor `match`, the result type
must be explicit, and every recursive call must supply an immediate recursive
constructor child. The existing index-polymorphic recursion path remains intact.

```lean
inductive Walk : Nat -> Type where
  | done (n : Nat) : Walk n
  | step (n : Nat) (child : Walk n) : Walk n

def copy (w : Walk 7) : Walk 7 := match w with
  | .done n => Walk.done n
  | .step n child => Walk.step n (copy child)

theorem identity (w : Walk 7) : copy w = w := by
  induction w with
  | done n => rfl
  | step n child ih => simp only [copy, ih]
```

Uniform family parameters and their type dependencies stay fixed. Other source
arguments are generalized in the recursor motive: accumulators, dependent proofs,
and nonuniform prefix parameters can change on recursive calls. A source call
supplies its actual arguments to the corresponding child hypothesis. Generated
Eq/HEq premises are supplied reflexivity only after their types and endpoints
compare equal. An unresolved child-index condition is a refusal, not an assumed
equality or a guessed constructor.

Partial recursive applications are supported after the structural child has been
supplied. Remaining parameters become fresh lambda binders with their dependent
domains; outer loose variables are lifted before closing those binders. This
preserves capture avoidance even beneath a source lambda. A recursive function
cannot escape before its structural argument is supplied.

## Checking boundary

The equation compiler retains the recursor, index equations, dependent context,
and proofs of impossible branches. Recursive calls are lowered across the whole
branch expression, including unused let values and written type annotations.
The recursive source name is a private elaboration marker, never a declaration.
Only its validated calls on direct children become applications of actual
recursor hypotheses. Those hypotheses are hidden during user-term elaboration,
including ordinary proof tactics and instance search.

Dependent index refinement may rebuild local identities. Private checked aliases
connect each surviving constructor child to its actual hypothesis; source names
are not authority for a decrease. Temporary contexts used to apply hidden
hypotheses or complete partial calls are restored on success and failure. The
complete declaration still crosses K1 and the independent checker.

Equality transports exposed two conversion requirements. The source reducer now
has a sufficient gate for admitted nullary K recursors: the spine-instantiated
major domain must equal the nullary constructor result before an unknown proof
can reduce. The independent checker's K gate additionally compares a compact Nat
literal with one explicit admitted constructor layer. This never expands a large
integer into a unary value or accepts distinct endpoints.

## Examples and boundaries

```bash
fln check-source --json examples/native_constrained_recursion.lean
```

The example checks fixed-index copy and its universal induction proof, changing
accumulators, a repeated-index tree with two recursive children, partial
applications beneath a lambda, and a telescope with dependent computed indices.
Source tests reject nondecreasing calls, changed uniform parameters, unresolved
child indices, false branch proofs, hidden recursive calls, and forbidden
proof-to-data elimination. An installed-CLI test checks a successful file, a late
invalid suffix with no partial success output, and recovery.

This is bounded direct-child structural recursion. Grandchild/course-of-values,
mutual, nested-family, and well-founded recursion remain separate work. Arbitrary
casts or computations are not interpreted as structural children. No general
injectivity of an index function is assumed. Multi-discriminant or nested-pattern
compilation and full equation-lemma/name parity are not established by this path.
The tests cover source admission and checked conversion, not execution-backend
parity or a complete pinned Prelude/corpus conformance run.

## Multiple input patterns

A constrained structural input can also be the first discriminant of a root
pattern matrix. Other columns are elaborated in the generalized recursive
context. See [Native matrix recursion](NATIVE_MATRIX_RECURSION.md) for the
checked alias/hypothesis tracking and the immediate-child restriction.
