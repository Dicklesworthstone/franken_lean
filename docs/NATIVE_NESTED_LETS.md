# Transparent local bindings in nested terms

The native source parser accepts named `let` bindings with inferred or explicit
types in ordinary term positions, including lambda bodies, application
arguments, parenthesized expressions, record fields, list elements and nested
binding initializers. They use the same heap-frame parser phases as local
assertions, but produce `Lean.Parser.Term.let` syntax, not opaque `have` syntax.
The original keyword, identifier, type annotation, assignment, initializer,
separator and body remain in the syntax tree and lossless source reconstruction.

An initializer sees the outer lexical context. Its name enters scope only in the
continuation, so shadowing does not create accidental recursion. Transparent
local definitions remain reducible during ordinary kernel and independent-checker
admission, including type-valued aliases and dependent annotations. No change to
either checker, elaborator admission, or runtime reduction is needed.

`examples/native_nested_lets.lean` builds three callback stages using ordinary
lambda and local-definition syntax. Its intermediate scalar values are retained
in owned closures; the final record field also contains a local definition. Both
source entry points return 42 and the emitted FLBC replays independently of the
source parser and elaborator.

## Delimiters and bounds

Explicit semicolons and the existing indentation-sensitive line boundaries
separate initializer and continuation. Parentheses, binder annotations and
record/list boundaries retain ownership of their delimiters. Tactic initializers
follow the existing tactic parsing rules: use `(by rfl)` for a parenthesized inline
proof, or an indented tactic followed by an outdented continuation. A semicolon
inside an unparenthesized `by` block is not silently stolen from the tactic parser.

Nested definitions use heap frames for annotations, initializers and bodies, not
recursive calls to the term parser. Small-stack tests cover 600 chained bindings
with either separator. Comments, CRLF and Unicode identifiers round-trip exactly.
Malformed bindings cannot discard their type, initializer or continuation.

## Evaluation and limits

Ordinary unused initializers still execute strictly. Proof-only work is erased
only after checking; an unused malformed annotation or false proof still rejects
the source. Step-growth tests compare retained ordinary work against erased proof
work. Installed tests cover imports, rejection without output or artifact
replacement, deterministic recovery, and standalone bytecode replay.

This extension handles named simple local definitions. Nested pattern binding,
`let mut`, nested recursive-declaration syntax and nested local-function binder
sugar are not added here. Existing supported declaration-head forms remain
unchanged. The richer term grammar does not widen the older Nat-only driver.
