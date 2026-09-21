# Native whole-context simplification

`simp_all`, `simp_all [rules]`, and `simp_all only [rules]` select the current
propositional hypotheses and simplify their types repeatedly until no hypothesis
changes. Unlike a single `simp [*] at *` traversal, a later transformed equality
can simplify an earlier hypothesis on the next pass. The final goal uses the
same selected evidence and the same productive-step budget.

```lean
theorem fixedPoint (P : Nat -> Prop) (f : Nat -> Nat) (x y z : Nat)
    (hp : P (f y)) (he : f x = z) (hxy : x = y) : P z := by
  simp_all only
```

Each transformation constructs the existing checked transport and introduces a
fresh local identity. Dependent uses retain the original well-typed identity;
local types are never retagged in place. A hypothesis cannot serve as its own
rewrite evidence or discharge its own conditional premise. Explicitly selected
proofs and their dependency telescopes are preserved while automatic selections
follow replacement identities. Backtracking restores semantic state and pending
closures without refunding consumed work.

Ordinary `simp_all` reads the immutable registered simp set; `only` does not.
Explicit selections, global exclusions, priorities, and selected unfolding use
the existing simp rule machinery. Rule ordering is deterministic. All rounds
share the 256 productive-step limit, source heartbeat budget, and per-location
cycle histories. A cycle is a typed tactic failure; resource and internal
nonanswers do not become successful tactic alternatives.

Run the real source-checking path, including both declaration checkers:

```bash
cargo run --locked -p fln-cli --bin fln -- check-source --json examples/native_simp_all.lean
```

This is a bounded native tactic, not complete upstream `simp_all` parity.
Only source-visible propositional hypotheses are simplification locations;
shadowed proof hypotheses remain selectable evidence by identity. Data-valued
local types are not rewritten by this tactic. Custom configurations, dischargers,
locations, local-rule erasure, automatic rule orientation, and general
binder-opening congruence remain unsupported. Productive simplification can
leave a genuine goal for subsequent tactics; it never admits an unfinished proof.
