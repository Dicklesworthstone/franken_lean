# Native constructor proof construction

`constructor` applies the first admitted constructor whose result can unify with
the current target. `left` and `right` choose the first or second constructor of
a family with exactly two constructors. They work for source-defined propositions
and data types, including indexed families and dependent records.

```lean
theorem pair (P Q : Prop) (p : P) (q : Q) : Both P Q := by
  constructor
  exact p
  exact q
```

The tactics reuse ordinary application and instance search. Inferred parameters
are skipped; unsolved fields become real proof-state goals. Fields are scheduled
in telescope order so a witness or type can be provided before a later dependent
field. A constructor whose index does not match is retried transactionally: no
speculative metavariables, equations, generated identities, or goals survive,
while spent work is retained. This is constructor selection, not proof search
through the subsequent field goals.

Completed values contain the actual constructor application. Introduced local
contexts close only after their descendants are solved, and unused annotations
remain ordinary kernel obligations. Abstract targets, empty families, unfilled
fields, invalid witnesses, and extra tactics after completion refuse. Neither
checker, the seed, nor the declaration-admission path is changed.

This bounded syntax does not implement constructor configuration options or
constructor offsets. Run the real file-checking path with:

```bash
fln check-source --json examples/native_constructor_tactics.lean
```
