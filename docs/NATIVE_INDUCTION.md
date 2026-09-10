# Native cases and induction

The import-free source proof checker supports case analysis and structural
induction on a named local of an admitted, single, non-indexed inductive family.
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

This is not full Lean elimination elaboration. Indexed and mutual families,
non-local discriminants, `cases h : expression`, `using` recursors, `case`/bullet
selectors, inaccessible patterns and higher-order/nested recursive fields are not
supported by this tactic lane. Uniformly parameterized families with direct
recursive fields now have constructor-derived independent admission support;
see [Native parameterized recursion](NATIVE_PARAMETERIZED_RECURSION.md). Shapes
outside that documented lane remain explicit checker vetoes.
The source proof state is not yet a complete interactive MCP/LSP tactic service.
