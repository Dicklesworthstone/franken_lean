# Native pattern matrices

Ordinary source `match` accepts several comma-separated discriminants and nested
constructor patterns. Rows have first-match priority. Constructor applications
inside another constructor's fields are grouped with parentheses; nullary
relative patterns need no parentheses.

```lean
def priority (a b : Bool) : Nat := match a, b with
  | true, _ => 1
  | _, true => 2
  | _, _ => 3

def flatten (m : Maybe (Maybe Nat)) : Nat := match m with
  | .none => 0
  | .some .none => 1
  | .some (.some n) => n
```

The parser retains the original commas, parentheses, comments and source positions.
Pattern grouping and matrix expansion use heap worklists, not recursive calls over
source-controlled nesting. The pattern grouping test reaches 2,000 nested groups
on a 128 KiB thread stack. That is parser evidence, not a claim that checking
arbitrarily deep generated proofs has no cost or resource bounds.

## Checked compilation

The compiler specializes a pattern matrix column by column, in source order, into
ordinary constructor eliminations. Wildcard rows are retained in each applicable
constructor branch at their original relative priority. The existing elimination
engine produces the actual recursor applications, transports dependent contexts,
and discharges impossible branches with checked equality/contradiction proofs.
No discriminant is evaluated to decide that a source body can be discarded.

Every discriminant is retained in a checked local binding, including wildcard-only
columns and global constants. Private, unspellable numeric names give source
pattern bindings simultaneous semantics: `match x, y with | y, x => x` returns the
original `y`. Exact local aliases are followed for motive abstraction, so selecting
an earlier column also refines later discriminants whose types depend on it.
Aliases do not reduce away invalid type annotations or unused value obligations.

Rows need not enumerate impossible indexed constructors. For example, extracting
the second element of `Vec Nat 2` can use one nested `cons` pattern. Matching two
vectors at the same length also refines their correlated constructor choices.
Both checking engines validate the resulting proof and computation terms.

An original row must be elaborated in at least one reachable branch. A completely
redundant row is refused rather than allowing an unchecked source expression to
vanish. Generated wildcard fallbacks may disappear only when they are unnecessary
and each original row they represent is checked elsewhere. Duplicate binders,
wrong arities, missing reachable combinations, foreign constructors and incorrect
proof-to-data elimination remain refusals. Relative and qualified constructor
spellings are merged only against explicit admitted constructor names in that
column; the qualified name remains in the generated match for type validation.

## Generic containers are not recursively typed fields

Recursive-hypothesis slots are determined from the admitted constructor's original
signature, before instantiating its parameters. A payload of type `A` does not
become a recursive child merely because `A` is instantiated with `Maybe Nat` or
`Seq Nat`. This distinction is shared by matching, tactic elimination and
constructor-equality selectors. Genuine direct recursive fields still receive
their real hypotheses; nested/higher-order inductive definitions remain outside
that frontend lane. No kernel rule or independent-checker admission rule changes.

## Resource and capability limits

This implementation bounds each source matrix to 64 discriminants and 256 rows.
Expansion, copying and branch processing also consume the existing source-work
budget. Exhaustion is a resource nonanswer, not a proof of non-exhaustiveness or
kernel rejection. Failed files publish no successor environment.

Supported patterns are variables, wildcards and constructors, including nested
constructor patterns. Numeric/string literal patterns, alternative-pattern bars,
pattern guards, inaccessible patterns, named discriminant equations and explicit
motive syntax are not added here. Existing structural-recursion definitions with
flat root patterns remain supported; recursive calls introduced through a matrix
root or a nested constructor pattern are a separate lowering task. This does not
implement general well-founded recursion, mutual/nested inductive admission,
execution-backend parity or full Reference matcher compatibility.

Run the checked example through the installed binary:

```bash
fln check-source --json examples/native_pattern_matrices.lean
```

The example contains 15 commands and eight theorems. Source and CLI regressions
check both admission engines, row priority, nested generic containers, dependent
indices, hygiene, retained discriminants, invalid unused annotations, resource
stops and failure isolation. Scoped package tests do not establish a pinned
Prelude council pass or full-workspace conformance.
