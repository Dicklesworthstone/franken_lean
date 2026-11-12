# Native editor queries and document outlines

Both `fln serve-lsp` and `lean --server` answer `$/lean/plainGoal`,
`textDocument/hover`, `textDocument/definition`, `textDocument/completion` and
`textDocument/documentSymbol` using the native source elaborator. These LSP features are
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

Cursor inspection is synchronous on the existing stack-calibrated proof worker. It
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

## Document symbols

`textDocument/documentSymbol` populates the editor's outline with explicitly named,
admitted declarations in the requested document. Requests require `textDocument.uri`
and do not require a cursor position. The result is a flat `DocumentSymbol[]` in
source order, with fully qualified names such as `Outer.Inner.value`. Each entry
has the pin's declaration kind (`SymbolKind.Method`, 6), its declaration range,
and an identifier `selectionRange`, all in UTF-16 coordinates from the accepted
unsaved source. CRLF and Unicode are mapped through the original source bytes.

Definitions, theorems, abbreviations, opaque declarations, axioms, inductive and
structure/class headers, named instances, and explicit members of mutual groups
are included when supported by ordinary native checking. Imports, local binders,
anonymous instances/examples, generated helpers and macro-generated declarations
without an explicit declaration identifier are omitted. Namespace nesting is
represented in qualified names; namespace containers are not synthesized.

The complete source and its import closure are checked before an outline is
published. Extraction then replays imported and local syntax in lexical order,
including sections and temporary `open … in` scopes. A valid empty document
returns `[]`; failed or inconclusive checking, invalidated text, and resource
limits are request errors, never an empty success or a previous version's outline.
This runs on the same synchronous proof worker as the other native queries.
Engine API: `SourceModuleSession::document_symbols`, with separate source,
module, command and syntax-walk bounds in `DocumentSymbolLimits`.

The transcript correlator's `fln.lsp-method-response/5` profile validates this
flat result's names, declaration kind, nonempty nested ranges and source order.
It distinguishes `[]`, unavailable information (`null`) and typed query errors.
Regression tests are included in `source_definition_navigation`,
`lsp_definition_navigation` and `lsp_semantic_correlation`.
