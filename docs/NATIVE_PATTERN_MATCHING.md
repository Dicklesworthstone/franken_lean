# Native constructor matching

The import-free source checker accepts single-family `inductive` declarations and
exhaustive constructor `match` expressions. These are ordinary checked inductive
blocks and recursor applications, not Reference-toolchain calls or an additional
proof-admission authority.

```lean
inductive Maybe (A : Type) where
  | none
  | some (value : A)

def get (item : Maybe Nat) : Nat := match item with
  | .none => 0
  | .some value => value

theorem payload_ok : get (Maybe.some 23) = 23 := by rfl
```

Run `fln check-source --json examples/native_pattern_matching.lean`. The installed
command checks the whole file through K1 and the independent checker and does not
compile or execute the source program. Ordinary checking still performs conversion
to verify the example's computations and proofs.

## What the implementation supports

Each match has one discriminant. Patterns are flat constructor applications with
variable or wildcard fields, qualified names such as `Maybe.some`, or expected-
family names such as `.some`. The builtin Bool patterns `true` and `false` also
work. A final `_` or single variable can cover all remaining constructors; a named
catch-all is bound to the actual constructor value in each resulting branch.
Duplicate constructors, wrong arities, duplicate variables, foreign constructors,
missing alternatives and a redundant catch-all are explicit refusals.

Branches have separate local scopes. Payload types may depend on parameters or
earlier payloads. Dependent expected results generalize a local discriminant into
the recursor motive, so a match on `package : Package` can produce a value of type
`package.carrier`. Function-valued results, proof-valued results, inferred result
types, branch-local let telescopes, nested match expressions, record values and
matches in tactic terms are supported. Nested matches are parenthesized or their
alternatives use distinct indentation; multiline alternatives at one level align.

Direct uniform recursive fields receive the recursor's real induction-hypothesis
binders, hidden from ordinary match syntax. Primitive recursive source functions
can now use those hypotheses under the rules in [Native structural recursion](NATIVE_RECURSION.md).
Cases return
ordinary core terms and **every written branch remains checked**, including a bad
branch unreachable for a literal discriminant. No branch is dropped based on
executing the scrutinee in the elaborator.

The full source seed now admits Nat as its ordinary recursive inductive family,
with `Nat.zero`, `Nat.succ` and its regenerated dependent recursor. The tiny raw
Nat elaboration fixture remains separate and unchanged. The independent checker's
Nat-literal reduction exposes one constructor layer, retaining the predecessor as
a compact arbitrary-precision literal. It does not allocate a unary chain. The
TCB audit no longer reports Nat itself as a source-seed axiom; other explicit
primitive signatures still appear in the audit and are not hidden.

## Scope and evidence boundaries

This is a bounded constructor-match compiler, not complete Lean match elaboration.
The original flat lane does not handle multiple discriminants or nested
constructor patterns; the pattern-matrix extension below supplies them. Other limits include
numeric patterns, guards, indexed/mutual/nested families, inaccessible patterns,
explicit motives, `match h : ...`, dependent generalization of other hypotheses,
general equation-compiler recursive definitions and well-founded termination
checking remain outside this increment. Numeric Nat values can be scrutinized
with `.zero` and `.succ previous`; decimal-pattern syntax is not implemented.

Resource bounds and checker nonanswers remain distinct from rejection. Parsing
nested matches uses heap worklists, and elaboration shares the existing bounded
term task machine. A failed branch, later command or later supplied file exposes
no successful prefix environment. Existing `check-source` restrictions on imports
and metaprogramming remain unchanged.

Tests are the real `fln::source_inductive`, `fln::source_matching`, parser matching
unit tests, independent-checker literal-elimination tests, and installed CLI
`source_check` tests. They include deep parser inputs, large Nat literals, both
branches of constructors, wrong branch types, invalid unused annotations, scope
isolation, resource nonanswers, multi-file failure/recovery and actual recursor
dependencies. Passing these tests is scoped evidence, not full language parity or
a whole-workspace test/release-gate claim.

## Pattern-matrix extension

Multiple discriminants and nested constructor patterns now have a shared checked
matrix-compilation path. See [Native pattern matrices](NATIVE_PATTERN_MATRICES.md)
for row priority, correlated dependent inputs, source-row reachability and current
recursion/literal-pattern limits. The original single-discriminant flat path
remains available and its structural-recursion behavior is retained.
