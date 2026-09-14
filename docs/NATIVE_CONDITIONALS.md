# Native checked conditionals

The source path accepts Boolean `if condition then yes else no` expressions.
Both arms become ordinary `Bool.rec` premises via the existing dependent match
backend, not a host-language branch selected during elaboration. Every condition,
arm, and written annotation remains an ordinary checking obligation. A false or
ill-typed unselected branch cannot disappear, and checking executes no backend.

```lean
def choose {A : Type} (b : Bool) (yes no : A) : A := if b then yes else no

theorem choose_same (A : Type) (b : Bool) (x : A) : choose b x x = x := by
  cases b with
  | false => rfl
  | true => rfl
```

Nested conditionals, ordinary constructor matches, function-valued arms, local
let telescopes, and scoped proof bodies share the existing heap-planned syntax
and elaboration worklists. Comments, CRLF positions, and branch keywords retain
their original leaves. A condition appears once in the generated recursor. The
existing root structural matcher can contain conditionals whose arms recurse on
its actual constructor children; nondecreasing calls remain refusals even inside
unused arms. Generic result types and computable Boolean-indexed types work.

The first increment is Boolean-only. Proposition-valued conditions requiring
`Decidable`, named evidence (`if h : ...`), missing-else syntax and new structural
recursion candidates at a root conditional are separate capabilities. A Boolean
comparison does not manufacture propositional equality evidence.

Run `fln check-source --json examples/native_conditionals.lean`. The example
contains 12 commands and seven theorems, including a universal generic proof.
Scoped package tests, small-stack parsing and installed CLI refusal/recovery do
not establish complete Reference conformance or execution-backend parity.
