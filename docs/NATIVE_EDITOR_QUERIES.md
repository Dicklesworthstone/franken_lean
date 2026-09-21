# Native editor goals and hover

Both `fln serve-lsp` and `lean --server` answer `$/lean/plainGoal` and
`textDocument/hover` using the native source elaborator. Hover is advertised in
initialization. Goal requests return the Lean `rendered`/`goals` object; hover
returns plaintext contents and the selected identifier's UTF-16 range.

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

## Current scope

Inspection is synchronous on the existing stack-calibrated proof worker. It
reuses the checked-prefix/module cache but re-elaborates the current declaration
to the selected boundary; this is not an O(1) goal snapshot or asynchronous
cancellation claim. Source syntax must be supported by the native parser;
empty `by` blocks are supported, arbitrary malformed partial terms are not.
Hover currently observes term identifiers, not every syntax node or binder
introduction. `plainTermGoal`, completion, definition lookup, and Lean RPC
sessions remain separate work. Legacy callback embedders retain their null
query behavior unless they implement the new typed `WorkspaceChecker` query
interface.

Installed regression tests: `cargo test --locked -p fln-cli --test lsp_goals`.
Engine regression tests: `cargo test --locked -p fln --test source_goal_inspection`.
