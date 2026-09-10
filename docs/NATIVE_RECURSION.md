# Native structural recursion

The source checker elaborates primitive structural recursion through the same
admitted recursors used by constructor matches. No temporary recursive axiom or
unchecked self declaration is inserted into the environment.

```lean
def sumTo (n : Nat) : Nat := match n with
  | .zero => n
  | .succ k => sumTo k + n

theorem sum_ok : sumTo 4 = 10 := by rfl

inductive Tree where
  | leaf (value : Nat)
  | fork (left right : Tree)

def treeSum (tree : Tree) : Nat := match tree with
  | .leaf value => value
  | .fork left right => treeSum left + treeSum right
```

The decreasing argument is inferred from the match at the root of the function
body. In this increment it must be the final explicit header parameter, and the
result type must be explicit. Earlier parameters, including implicit type
parameters and instance dictionaries, remain fixed. Recursive calls may occur
inside branch expressions, lets, lambdas and nested matches, provided they use
an immediate recursive constructor field of that root match.

The recursive name is represented temporarily by a private local, then each
permitted call is replaced by the corresponding recursor hypothesis. The final
candidate has no self-reference, unresolved hole or escaping free variable.
Every constructor branch and every retained argument is checked by the ordinary
kernel and independent checker. Nondecreasing calls, changed fixed parameters,
partial self-applications and recursive names stored as arbitrary values refuse;
unused lets and type annotations cannot hide them.

The original major is removed from the recursive branch context and its source
name is rebound to that branch's constructor value unless shadowed by a pattern
binder. Capturing the original major instead would miscompile functions such as
`sumTo`. The recursor motive is dependent when the result type requires it.
Failed nonrecursive attempts and termination failures retain spent work, but
never publish a speculative environment.

This is not complete Lean termination elaboration. Varying extra arguments,
course-of-values recursion on grandchildren, indexed or mutual families,
well-founded measures, recursive `where`/`let rec`, equation-style definitions
and `termination_by` clauses are not implemented here. A parameterized recursive
family may additionally be outside the independent checker's supported shapes;
that checker is never bypassed to make a recursive source example pass.

Regression coverage lives in `crates/fln/tests/source_recursion.rs`; it exercises
real source parsing, inference, recursor construction and both checking engines.
