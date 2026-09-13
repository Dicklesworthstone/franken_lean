# Checked natural-literal patterns

Natural literals are patterns in ordinary matches, equation declarations, nested
constructor payloads, multiple columns, and pattern functions. Source row order
is preserved. Different spellings of the same natural, including hexadecimal,
binary and decimal underscores, denote the same pattern.

```lean
def route : Nat -> Bool -> Nat
  | 0, _ => 7
  | n, true => n + 10
  | _, false => 9

def copy : Nat -> Nat
  | 0 => 0
  | .succ k => Nat.succ (copy k)
```

Literal-only columns compile to comparisons using the existing admitted Nat.beq
and ordinary Bool recursors. A 129-bit pattern stays a compact literal, not an
astronomical unary successor tree. When a source constructor pattern or a recursive
root needs constructor fields, the compiler exposes one Nat constructor layer and
keeps the predecessor compact. Thus zero/successor recursive equations retain the
real child hypothesis and ordinary structural termination checking.

The independent checker now runs its existing, separately implemented KR-313
natural evaluator when an admitted recursor demands an arithmetic major. This
includes nested arithmetic and comparisons; it is not a new operation table or a
call into the primary kernel. The nested work, reductions, allocation bounds,
cancellation and typed nonanswers remain accounted. An unsuccessful arithmetic
attempt is distinguished from progress on the outer term, so unknown operands do
not create an endless rechecking loop. The primary kernel is unchanged.

Every original discriminant stays in a checked binding. Reachable branches and
all source annotations remain checked, including unused definitions. A completely
redundant row refuses rather than hiding a bad body. A finite list of natural
literals needs a fallback even when the source discriminant is a known constant.
The generated comparison uses the exact intrinsic identity, not a user-shadowable
operator. Wrong literal domains and foreign-family constructor patterns refuse.

## Deliberate limits

A Boolean result is not a proof of equality between the input and a literal.
This lane does not fabricate such evidence or refine arbitrary dependent results
by assuming that comparison is injective. It keeps the original dependent context;
constructor-derived equations still use the existing checked refinement engine.
There are no negative integer, character, guard or inaccessible patterns here.

String literal tokens are preserved by the parser, but String patterns currently
refuse during elaboration: the bounded source String seed is opaque, and its
executable String.decEq intrinsic is not a kernel-reducible checked definition.
This feature does not add a special String acceptance rule to either checker.
String and general decidable-pattern support require that separate foundation.

Run the installed checking path:

```bash
fln check-source --json examples/native_literal_patterns.lean
```

The example includes ordered columns, a large literal, nested payloads, a pattern
callback and a universal induction proof about an equation-defined function.
The checks concern source admission and conversion, not execution-backend parity
or a full Reference conformance claim.
