# Native local proof declarations

Proof scripts support named and anonymous `have` declarations, inferred local
fact types, transparent tactic `let` declarations, and directly nested `by`
proofs. These are real local values, not assumptions added to the environment.

```lean
theorem congruence (n m : Nat) (h : n = m) : Nat.succ n = Nat.succ m := by
  have same : n = m := by exact h
  rw [same]

theorem quantified (n : Nat) : n = n := by
  have all : forall x : Nat, x = x := by
    intro x
    rfl
  exact all n
```

`have h := term` infers the type from the term. An anonymous declaration such as
`have : n = n := rfl` uses the local name `this`. A name becomes visible only after
its own value is elaborated, so shadowing refers to the preceding binding in the
right-hand side and cannot create a circular proof. Named local facts participate
in ordinary term elaboration and can be explicitly selected by `rw` or `simp only`.

`let x : T := value` exposes a transparent local definition, while `have` exposes
an opaque local parameter during subsequent source elaboration. Both are closed
into ordinary checked let terms with their actual value and written annotation.
Unused local declarations remain typing obligations: `have unused : String := 1`
is still rejected by K1 even when the rest of the theorem ignores it. An unresolved
hole or false inner proof cannot be published as a completed declaration.

A nested `by` body owns its entire indented tactic sequence. Its inner names and
unfinished goals cannot escape into the enclosing proof, and its scope does not
cross sibling constructor alternatives. Dependent local types, local lets,
substitution and induction retain the existing proof-producing transport paths.
Temporary construction never introduces a constant, axiom or admission authority.
All completed declarations still cross K1 and the independent checker.

The parser plans nested local proofs on the same heap worklist as scoped
elimination. The source elaborator also schedules annotation and value visits on
its existing term worklist, rather than recursively calling the proof parser or
elaborator for each nested declaration. Original leaves, comments, CRLF positions,
semicolons and branch syntax are retained. Parsing has a 300-level, 128 KiB-stack
regression, alongside malformed-scope and round-trip cases.

## Bounded syntax

A local declaration takes one simple name (optional for `have`), an optional type
annotation and `:= value`. For function-valued local lemmas, write a `forall` or
function type and a lambda or `by intro ...` body. The abbreviated local telescope
form `have h (x : T) : P x := ...` is not yet supported. Direct nested proofs belong
to the declaration's right-hand side; parenthesized nested tactic proofs in
arbitrary tactic argument positions are a separate parser capability. Inferred
`by` values that need an expected target require an explicit type annotation.
Semicolons within an indented nested proof belong to that proof; return to the
outer indentation for the next outer instruction. This does not add `suffices`,
`show`, `calc`, local recursion, or the complete Lean tactic combinator grammar.

Run the installed source-check path:

```bash
fln check-source --json examples/native_local_proofs.lean
```

The example proves generic facts with nested local lemmas, a quantified local
induction lemma for a recursive function, and dependent predicate transport. It
also constructs values through transparent lets and dependent records.
The CLI regression checks the whole prefix, rejects an invalid unused local value
in a later file without emitting partial success, and successfully rechecks the
same prefix afterwards. Package tests are not a full Reference conformance claim.
