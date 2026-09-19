# Native case analysis over mutual data families

The source matcher can specialize an already-admitted mutual recursor to a
single-family case split. The selected family keeps its real motive and branch
minor premises. Every sibling uses the constant motive `R -> R`, with identity
as its branch result. This inhabitant exists at the same universe as `R`, even
when that universe is `Prop` or an unresolved rigid universe parameter; no
`Inhabited` instance, fresh axiom or cumulativity rule is required.

This supports constructor matches in any family position, nested cross-family
matches, function-valued recursive fields, dependent result types, and
polymorphic results. Generated terms still go through K1 and the independent
checker. Missing/duplicate cases, malformed branch types, and false proofs do
not become successful declarations. The generated induction hypotheses are
consumed but are not source pattern fields or user-accessible assumptions.

For example, after admitting the mutual `Tree A` / `Forest A` source block:

```lean
def head (t : Tree Nat) : Nat :=
  match t with
  | .node n children => n

def first (fallback : Nat) (xs : Forest Nat) : Nat :=
  match xs with
  | .nil => fallback
  | .cons t rest => head t
```

The tests construct that block through the existing native mutual-source
candidate API and ordinary dual-checker admission before checking these source
functions. They do not claim a new `mutual ... end` parser, full upstream
eliminator compatibility, general mutual function recursion, termination
inference, or runtime-code-generator support. Ordinary pattern matching is not
permission to treat a sibling's induction hypothesis as a recursive call on the
selected family.

Focused reproduction:

```sh
cargo test --locked -p fln --test source_mutual_matching
```
