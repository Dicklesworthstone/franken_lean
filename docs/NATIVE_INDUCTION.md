# Native cases and induction

The import-free source proof checker supports case analysis and structural
induction on locals and elaborated expressions of an admitted single inductive
family. Dependent index telescopes and the existing constrained-index lane are
supported. See `NATIVE_INDEXED.md`, `NATIVE_CONSTRAINED_INDUCTION.md` and the runnable
`examples/native_indexed_elimination.lean` example.
These tactics construct applications of that family's ordinary recursor. They
never add an axiom, accept a proof, or bypass K1 or the independent checker.

```lean
def copy (n : Nat) : Nat := match n with
  | .zero => 0
  | .succ k => Nat.succ (copy k)

theorem copy_ok (n : Nat) : copy n = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp only [copy, ih]
```

`induction n with ...` names the constructor fields followed by its recursive
hypotheses. A branching tree has one hypothesis for each direct recursive field.
`cases n with ...` exposes the fields but does not expose those hypotheses, even
to `assumption` or instance search. The unused recursor hypothesis binders remain
in the generated core term, where they are checked and then ignored.

Constructor labels can be qualified or relative to the selected family. Each
constructor must occur exactly once; alternatives may be written in any order.
Duplicate, foreign, missing or excessively named alternatives are refused. An
underscore or an omitted name leaves the corresponding binder anonymous.

Each alternative owns a complete tactic sequence. Nested eliminations use
strictly deeper indentation. Goals produced by `apply`, rewriting, simplification
or another elimination must all finish inside that branch. A branch cannot borrow
tactics from its sibling, and an extra instruction after its last goal is an error.
The bare forms `cases n` and `induction n` instead expose constructor-ordered goals
to the remaining enclosing tactic sequence. Empty families need no branch proof.

## Dependent contexts and generalized hypotheses

The discriminant and the transitive cone of locals depending on its type or value
are removed from the branch context. Dependent parameters and let definitions are
abstracted into the motive, then reintroduced using the actual constructor and
fresh field locals. Let definitions retain their values. Independent locals stay
in scope; the original discriminant is not secretly retained under its old name.
This supports a dependent record elimination whose output is `package.carrier`.

Explicit `generalizing` names extend that dependency cone and, for induction,
make the hypotheses functions of those new argument values:

```lean
def zeroAcc (n : Nat) (acc : Nat) : Nat := match n with
  | .zero => 0
  | .succ k => zeroAcc k (acc + 1)

theorem zeroAcc_ok (n acc : Nat) : zeroAcc n acc = 0 := by
  induction n generalizing acc with
  | zero => rfl
  | succ k ih => exact ih (acc + 1)
```

Locals depending on the discriminant, including proof arguments, are generalized
even without an explicit list. Generalization that would invalidate the fixed
discriminant type is refused. Branch binder names may shadow outer source names,
but never change their core variable identities or capture another branch's data.

## Computed expressions and branch equations

`cases (f x)` and `induction (f x)` elaborate the discriminant through the ordinary
native term driver. A local variable, including a parenthesized local, retains
the dependency-aware behavior above. A computed expression is generalized in
the goal before applying the family's checked recursor. `induction` still exposes
real recursive hypotheses and supports an explicit `generalizing` list.

The optional equation form retains the connection to the original expression:

```lean
theorem keep (f : Nat -> Bool) (n : Nat) (P : Bool -> Prop)
    (p : P (f n)) : P (f n) := by
  cases h : f n with
  | false => rw [<- h]; exact p
  | true => rw [<- h]; exact p
```

Here `p` still refers to the original computation. The branches receive the actual
equations `h : f n = false` and `h : f n = true`. `induction h : expression` uses
the same mechanism. `_ : expression` keeps an inaccessible equation. Names can
be shadowed in nested branches without changing their core identities.

The generated universal proof is specialized at the original expression and,
when requested, `Eq.refl` of that expression. Both the universal type and the
original input remain checked in the final term. A discarded, ill-typed input
cannot become valid just because all branches ignore it. The normal restrictions
on eliminating propositions into data remain in force.

```bash
fln check-source --json examples/native_expression_elimination.lean
```

This example exercises an equation-dependent proof, induction on a function
application, a dependent record result, and a fixed-index case split. Engine and
installed-CLI tests exercise these paths, failures and subsequent recovery.
Parser tests cover comments, CRLF, escaped names and nested expression splits on
a 128 KiB thread stack.

This increment accepts one discriminant. Generalization selects exact elaborated
occurrences, not occurrences modulo arbitrary definitional equality; ascriptions
remain real checked terms. Parenthesize nested `match` expressions to distinguish
their `with` from the tactic's alternatives. Nested `by` or `calc` proofs inside
the discriminant, multiple discriminants and user-selected `using` recursors
remain explicitly unsupported.

## Simplification and checking

Selected recursive definitions now expose their admitted recursor computations
to `simp only`. The same explicit definition set normalizes the selected lemmas'
types, while their actual proof values are retained. This lets an induction
hypothesis rewrite a recursive call after the selected function has unfolded.
No unselected ordinary definition is unfolded by this change. A no-op source
reduction preserves the original expression allocation and its DAG sharing.

Every branch remains an ordinary checked minor premise. Wrong branch types,
invalid unused arguments and false reflexivity proofs still receive kernel
rejection. Failed branch construction, a later command or a later input file
exposes no successful environment prefix. Exhaustion is a typed nonanswer, not a
false theorem or a mathematical rejection.

Run the checked example with:

```bash
fln check-source --json examples/native_induction.lean
```

The installed-binary regression uses that exact example. Engine tests cover open
Nat and tree equations, dependent data and proof contexts, accumulators, local
lets, nested scopes, false proofs, resource stops and independent-checker vetoes.
Parser tests retain original comments and CRLF bytes and exercise deeply nested
branch syntax on a small thread stack.

## Remaining scope

This is not full Lean elimination elaboration. Mutual families,
multiple discriminants, `using` recursors, `case`/bullet
selectors, inaccessible patterns and higher-order/nested recursive fields are not
supported by this tactic lane. Uniformly parameterized families with direct
recursive fields now have constructor-derived independent admission support;
see [Native parameterized recursion](NATIVE_PARAMETERIZED_RECURSION.md). Shapes
outside that documented lane remain explicit checker vetoes.
The source proof state is not yet a complete interactive MCP/LSP tactic service.
