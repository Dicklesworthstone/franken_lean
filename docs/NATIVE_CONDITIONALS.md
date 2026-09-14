# Native checked conditionals

The source path accepts Boolean and proposition-valued `if condition then yes else no`
expressions. Boolean arms become ordinary `Bool.rec` premises. Proposition arms
use a synthesized `Decidable` dictionary and the admitted `Decidable.rec` through
the same dependent match backend, not a host-language branch selected during elaboration. Every condition,
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

Named proposition conditions introduce `h : p` in the then arm and `h : Not p`
in the else arm. Both bindings are local to their branch. This supports proof
terms, method bodies, callbacks, and explicit `refine` holes. Branches are
elaborated in then/else source order even though the recursor's minors are ordered
isFalse/isTrue, so refinement holes receive the correct branch context.

```lean
def inspect (p : Prop) [Decidable p] (yes : p -> Nat) (no : Not p -> Nat) : Nat :=
  if h : p then yes h else no h

theorem recover (p : Prop) [Decidable p] (hp : p) : p := by
  refine if h : p then ?_ else ?_
  · exact h
  · exact hp
```

Computed propositions are normalized for instance selection, while their original
source values remain checked let bindings in the final term. Normalization cannot
erase a bad unselected arm of a computed condition. Unknown propositions require
an actual local or registered global decision; no classical decision is invented.
The original branch syntax is borrowed directly, not copied into alternative
source strings or recursively reparsed.

Named Boolean evidence, missing-else syntax and new structural recursion candidates
at a root conditional remain separate capabilities. A Boolean comparison does not
manufacture propositional equality evidence.

Run `fln check-source --json examples/native_proposition_conditionals.lean` for
12 commands and seven theorems exercising decisions, branch evidence, computed
types, functions and recursive definitions through both checkers.

Run `fln check-source --json examples/native_conditionals.lean`. The example
contains 12 commands and seven theorems, including a universal generic proof.
Scoped package tests, small-stack parsing and installed CLI refusal/recovery do
not establish complete Reference conformance or execution-backend parity.
