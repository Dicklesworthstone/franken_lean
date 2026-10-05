# Native editor goals, hover, definition and completion

Both `fln serve-lsp` and `lean --server` answer `$/lean/plainGoal`,
`textDocument/hover`, `textDocument/definition` and `textDocument/completion`
using the native source elaborator. Hover, definition and completion are
advertised in initialization, on the semantic-capable path only. Goal requests
return the Lean `rendered`/`goals` object; hover returns plaintext contents and
the selected identifier's UTF-16 range.

For example, the unfinished source

```lean
theorem pending (P : Prop) (h : P) : P := by
```

has the live goal `P : Prop`, `h : P`, `⊢ P` at the end of the `by` block.
After `intro` or `constructor`, inspection follows the actual proof driver and
reports its instantiated local context and outstanding goals. Hovering over
`h` in `exact h` reports its actual inferred type, respecting local shadowing.
The bounded renderer handles dependent binders without capturing outer locals.

The engine API is `SourceModuleSession::inspect` with `ObservationKind::Goals`
or `ObservationKind::Term`. Its result separates a checked command/import
prefix from a provisional observation. The unfinished declaration never
enters an environment or a successful module-cache entry. Even an observation
with zero goals is not an admission certificate; ordinary file checking still
checks the complete declaration with both checker seats.

Requests see the dispatcher's accepted, unsaved source and the current native
import closure. Accepted changes, incremental edits, invalidated text, saves,
and closes share the existing document/version authority. Unavailable open
text cannot fall back to disk or a previous successful query. Coordinates use
UTF-16; positions inside surrogate pairs are refused. Bad prefixes and earlier
tactic errors remain query errors, rather than invented proof states.

## Definition

`textDocument/definition` (2026-09-26, `e845bbbd`) returns one LSP `Location`:
the URI and UTF-16 range of the identifier that declares an
elaborator-resolved global, found in the exact checked source closure, which
includes unsaved open imports. The target's source text is never sent and never
re-read from disk. Locals, seed constants, generated declarations, names that
come only from `.olean` imports, and unsupported declaration shapes return
`null` rather than a same-spelled substitute. Inconclusive checking, internal
faults, stale sources and ranges with no exact UTF-16 mapping are request
errors, never a fabricated location. Engine API:
`SourceModuleSession::definition`.

## Completion

`textDocument/completion` (2026-09-27, `779beee3` and `46e05cf3`) completes
global names from the ordinary dual-checked import and command prefix. The
token under the cursor is only a filter: it is never elaborated or admitted,
and a previous successful result is never replayed after a failed check. Each
item is plaintext with a root-qualified `_root_.` replacement, so a local of
the same spelling cannot capture it, and one single-line `textEdit` that
replaces the whole identifier. Results are bounded (256 items, 64 KiB) and
`isIncomplete` marks truncation. Local, field and tactic completion are outside
this profile. Engine API: `SourceModuleSession::complete`.

## Current scope

Inspection is synchronous on the existing stack-calibrated proof worker. It
reuses the checked-prefix/module cache but re-elaborates the current declaration
to the selected boundary; this is not an O(1) goal snapshot or asynchronous
cancellation claim. Source syntax must be supported by the native parser;
empty `by` blocks are supported, arbitrary malformed partial terms are not.
Hover currently observes term identifiers, not every syntax node or binder
introduction. `plainTermGoal` still returns `null`, and Lean RPC sessions remain
separate work. Legacy callback embedders retain their null query behavior unless
they implement the new typed `WorkspaceChecker` query interface.

Installed regression tests: `cargo test --locked -p fln-cli --test lsp_goals
--test lsp_definition_navigation --test lsp_completion`.
Engine regression tests: `cargo test --locked -p fln --test source_goal_inspection`.
