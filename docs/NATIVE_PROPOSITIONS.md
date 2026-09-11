# Native inductive propositions and relations

Source `inductive` declarations can end in `Prop`, including indexed predicates
with uniform parameters, dependent constructor fields, and direct recursive proof
fields. The candidate generator, K1, and independent checker separately derive the
eliminator. No proposition is introduced as an axiom and no declaration skips the
ordinary two-checker admission path.

```lean
inductive Below (a : Nat) : Nat -> Prop where
  | refl : Below a a
  | step (n : Nat) (h : Below a n) : Below a (Nat.succ n)

theorem transitive (a b : Nat) (hab : Below a b)
    (c : Nat) (hbc : Below b c) : Below a c := by
  induction hbc with
  | refl => exact hab
  | step n h ih => exact Below.step n ih
```

## Elimination is determined by constructor shape

An empty predicate can eliminate into any sort. A one-constructor predicate can
also do so when every constructor field is either a proof or occurs verbatim as
one of the result indices. A field merely occurring inside a compound index is
not sufficient. All other predicates eliminate only into `Prop`: there is no
extra motive-universe parameter on their recursor.

Consequently, a conjunction can expose its proof fields, disjunction can be
analyzed to prove another proposition, and existential evidence can be transported
to another existential proposition. Existential witnesses may live at arbitrary
universes because `Prop` is impredicative. This does not make their data available
through a large eliminator. Distinguishing disjunction constructors by returning
0 or 1, or extracting an existential witness into its data type, is refused.

```lean
inductive HasWitness (A : Type) (P : A -> Prop) : Prop where
  | intro (a : A) (h : P a)

theorem transport (A : Type) (P Q : A -> Prop)
    (f : forall a : A, P a -> Q a) (h : HasWitness A P) : HasWitness A Q := by
  cases h with
  | intro a hp => exact HasWitness.intro a (f a hp)
```

Source field-universe observations help construct candidates, but do not certify
them. The independent checker infers those universes in checker-owned contexts,
checks the exact index exposure condition, reconstructs the motive and all minor
premises and reduction rules, and verifies the recursor's universe parameters and
K-target flag. K1 independently regenerates the same declaration. Forging a large
motive, a more restrictive small eliminator, or a K-target flag does not pass by
altering candidate metadata.

Ordinary source matches and weak-head reduction handle both eliminator-universe
layouts. `cases` and `induction` retain their existing branch isolation, dependent
context generalization, and hidden-hypothesis rules. All original annotations and
unused arguments remain checked obligations. Failed files publish no successful
prefix and cancellation/resource exhaustion remains a nonanswer.

Run the real source/CLI example:

```bash
fln check-source --json examples/native_propositions.lean
```

The tests include independently written positive and forged checker inputs, source
proofs and forbidden proof-to-data eliminations, plus installed multi-file CLI
checking. These are synthetic and real-source tests, not an observation of the
pinned `Init.Prelude` council: its `Nat.le`-shaped blocker motivates this support,
but the full pinned companion-artifact run is a separate evidence obligation.

This remains the single-family direct-recursion lane. Mutual, nested and
higher-order recursive predicates, general fixed/repeated index-equation
refinement, inductives at universe `u` of unknown proposition/data status, and
complete Reference-source elaboration are not claimed. Existing special-cased
primitive families keep their existing independent admission routes.
