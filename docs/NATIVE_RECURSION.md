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
body. It must be an explicit header parameter, and the result type must be
explicit. Earlier parameters, including implicit type parameters and instance
dictionaries, remain fixed. Later parameters may vary at each call. Recursive calls may occur
inside branch expressions, lets, lambdas and nested matches, provided they use
an immediate recursive constructor field of that root match.

The recursive name is represented temporarily by a private local, then each
permitted call is replaced by the corresponding recursor hypothesis. The final
candidate has no self-reference, unresolved hole or escaping free variable.
Every constructor branch and every retained argument is checked by the ordinary
kernel and independent checker. Nondecreasing calls, changed fixed parameters,
recursive names escaping without a structural child refuse;
unused lets and type annotations cannot hide them.

Trailing arguments are universally quantified in the recursor motive. Each
induction hypothesis is therefore a function of their new values, not a result
capturing the outer arguments. This supports accumulators, changing type
arguments, implicit binders, dictionaries and proof arguments whose types depend
on the decreasing input:

```lean
def sumAcc (n : Nat) (acc : Nat) : Nat := match n with
  | .zero => acc
  | .succ k => sumAcc k (acc + n)

theorem acc_ok : sumAcc 4 7 = 17 := by rfl

def checkedSteps (n : Nat) (h : n = n) : Nat := match n with
  | .zero => 0
  | .succ k => checkedSteps k rfl + 1
```

After supplying the fixed prefix and a direct child, a recursive call may be
partially applied: `let smaller := add k; smaller (m + 1)` retains the actual
function-valued induction hypothesis. A bare `add` remains unsupported. All
varying and extra result-function arguments are retained and checked, including
nested recursive calls within them. Pattern names shadow same-named header
parameters without deleting the generalized argument's binder.

The original major is removed from the recursive branch context and its source
name is rebound to that branch's constructor value unless shadowed by a pattern
binder. Capturing the original major instead would miscompile functions such as
`sumTo`. The recursor motive is dependent when the result type requires it.
Failed nonrecursive attempts and termination failures retain spent work, but
never publish a speculative environment.

## Computed types during source elaboration

The source weak-head reducer now follows admitted non-indexed recursor rules,
not only beta, let, definition and projection reductions. Recursive type-valued
definitions can therefore supply the actual function domains needed by lambdas:

```lean
def Tower (n : Nat) : Type := match n with
  | .zero => Nat
  | .succ k => Tower k -> Tower k

def identity : Tower 1 := fun x => x
def higherIdentity : Tower 2 := fun f => f
theorem higher_ok : higherIdentity identity 12 = 12 := by rfl
```

Projection and recursor continuations use a heap worklist. Stuck discriminants
stay stuck; the reducer does not guess a constructor or widen definition/local
let transparency. A Nat literal exposes one constructor layer and keeps its
predecessor compact, using the existing bignum module. The reduction is metered
by the same source heartbeat budget, and exhaustion remains a resource stop.
Original source branch terms and their typing obligations are still checked
by the final checking engines. This is not the full independent unifier's
conversion procedure or support for indexed/K/quotient elaboration rules.

This is not complete Lean termination elaboration. Course-of-values recursion
on grandchildren, indexed or mutual families,
well-founded measures, recursive `where`/`let rec`, equation-style definitions
and `termination_by` clauses are not implemented here. Generic lists and trees
with uniform parameters and direct recursive fields now have independent
admission support; see [Native parameterized recursion](NATIVE_PARAMETERIZED_RECURSION.md).
Other unsupported family shapes remain vetoes, never checker bypasses.

Regression coverage lives in `crates/fln/tests/source_recursion.rs`; it exercises
real source parsing, inference, recursor construction and both checking engines.
The installed CLI checks `examples/native_recursion.lean` with
`fln check-source --json examples/native_recursion.lean`. This is admission and
kernel conversion, not a claim that the native execution backend now supports
every recursive definition.
