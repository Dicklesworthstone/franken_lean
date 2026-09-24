# Native multi-stage local callbacks

After admission by both logical checkers, local functions can return callbacks
that themselves perform strict work and return further callbacks. Each actual
lambda prefix retains its own argument count and return interface. This supports
mixed one- and multiargument stages, aliases, partial application, captured
functions, and owned String and record values. The complete application may also
supply all stages' arguments at once.

`examples/native_multistage_callbacks.lean` executes three stages, retains the
intermediate callbacks in local bindings, and returns an owned record containing
42. Installed tests run it through both source entry points, imports, and FLBC
replay without source elaboration.

## Metadata, not an evaluation-order transformation

A bounded heap worklist follows the result-producing path of already prepared
syntax. It derives a lambda's actual return interface from registered local
closures, lexical aliases, and applications. Unknown outer captures are not
assigned guessed runtime representations. The result's staged telescope must
retain the checked parameter representations, ownership, and terminal result.
Only then does the local closure receive the discovered exact result interface.

No source call is rewritten, no strict initializer is substituted or dropped,
and no argument is moved across a lambda boundary. Constructing a callback does
not run its body. Applying a stage runs that stage's prefix even when its returned
callback is discarded. Repeated calls share earlier completed prefixes, while
work in the called stage runs on every invocation. VM-step-growth controls test
these distinctions independently of the returned answer.

The compiler still validates every exact lambda argument count, argument type,
return type, capture, ownership transfer, and canonical callback interface. The
kernel, independent checker, logical source, global function interface, and
representation-changing-cast guard are unchanged. Malformed internal interfaces,
unknown stage identifiers, cyclic metadata, and budget exhaustion fail closed.

## Boundaries

This is not implicit adaptation between flat and staged calling conventions.
Passing a staged callback to a fixed flat callback parameter, storing it in a
field with an incompatible interface, or joining branches with incompatible
staging remains a refusal. The separate deeper nested-match result boundary in
`NATIVE_MUTUAL_INDEXED_RUNTIME.md` remains. General polymorphic runtime function
representations and Reference packed-ABI compatibility are not claimed.

Regressions cover mixed stage arities, aliases and lexical scope, owned captures,
unchanged strictness and sharing, small-host-stack discovery, resource stops,
invalid-source nonpublication, preserved artifacts, and deterministic recovery.
