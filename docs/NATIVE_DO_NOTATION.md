# Native sequential `do` notation

FrankenLean's bounded source frontend parses immutable sequential `do` blocks
and elaborates them to ordinary, checked `Bind.bind` and `Pure.pure` operations.
There is no special trusted monad evaluator and no call to the Reference.
The operations resolve from the current environment; local `[Bind M]` and
`[Pure M]` dictionaries work in generic functions.

```lean
class Pure (f : Type -> Type) where
  pure : {A : Type} -> A -> f A
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B

def map {M : Type -> Type} [Pure M] [Bind M]
    {A B : Type} (f : A -> B) (action : M A) : M B := do
  let x ← action
  return (f x)
```

The implemented syntax includes named `let x ← action` (also `<-`), optional
binding type annotations, pure `let x := value`, expression statements,
terminal `return value`, and an ordinary monadic expression in final position.
Statements may use semicolons or aligned line breaks. Nested blocks are
supported in both parenthesized expressions and indented binding values.
Comments and original UTF-8/CRLF bytes remain reconstructible from the syntax.
Sequences and nested blocks share the heap-based term parser stack.

Actions occur once in the generated term and receive a real continuation
lambda. Consequently the supplied bind implementation determines state order
and short-circuiting. The frontend does not eagerly evaluate continuation
bodies. Pure lets use ordinary local-value elaboration; bind variables are
fresh lexical locals. Discarded action results use unspellable internal names.
Expected monad constructors are preserved before aliases such as `Id` unfold;
monad specialization is a typed application, not an assumption that an unknown
higher-kinded metavariable is injective.

## Validation and boundaries

`cargo test --locked -p fln --test source_do` checks generic dictionary
parameters, identity computations, nested scopes, state sequencing, `Maybe`
short-circuiting, ordinary parenthesized conditional/match terms, and rejection
without changing the original engine. The state and `Maybe` examples include
kernel-checked equalities; these are semantic checking tests, not Golem runs.
`cargo test --locked -p fln-parse --test do_notation` additionally checks source
reconstruction and 600-element/nested sequences on a 128 KiB thread stack.

This does not yet implement mutable variables, loops, pattern bindings,
do-specific `if`/`match`, exception syntax, nested-action shorthand, or early
return. Those do elements are refused, never silently treated as plain
sequencing. Ordinary conditional/match expressions can appear inside actions;
a type ascription on the whole expression may be necessary for result
inference. `Pure`/`Bind` must be declared or imported; the parser does not
manufacture axioms or builtin instances.

## Executable specialization

Concrete calls now use a bounded, post-admission compiler specialization pass.
It instantiates ground universe parameters, leading type arguments and closed,
inert instance dictionaries, then compiles the resulting monomorphic bodies
through ordinary FIR validation, canonical FLBC encoding/decoding and Golem.
Specializations are keyed by the original declaration, universes and exact
static arguments. Their private names and transformed bodies never enter the
checked environment.

A source execution stream admits parametric definitions as checked templates
and registers instances through the ordinary source-admission path. They do not
produce phantom VM results; concrete `#eval` commands compile their reachable
specializations. For example, after the class declarations above:

```lean
def Id (A : Type) : Type := A
instance idPure : Pure Id := { pure := fun a => a }
instance idBind : Bind Id := { bind := fun a k => k a }

#eval (map (M := Id) (fun (x : Nat) => x + 1) 41 : Id Nat)
```

This executes to `42` on Golem. The runtime regressions also cover nested `do`
blocks, lexical shadowing, owned strings, different dictionaries at different
call sites, universe-polymorphic scalar functions, captured callbacks and
partial applications. Runtime lambda application introduces strict lets rather
than substituting action values: unused arguments still run, and repeated uses
share their result. Dictionary projection examines *all* fields and refuses
computed initializers rather than executing or dropping them at compile time.

`cargo test --locked -p fln --test runtime_specialization --test source_do -- --test-threads=1`
exercises these paths, deterministic bytecode, template/VM-result separation,
unchanged checked declarations, resource stops and failure-atomic recovery.
`cargo test --locked -p fln-cli --test source_do_runtime` runs the installed
`lean`, `fln run`, and FLBC replay paths with `examples/native_do.lean`, checks
alias-typed Bool/Nat/String output, and refuses late invalid code without
publishing output or artifacts.

This is not general polymorphic runtime representation. Static arguments must
form a prefix and be closed; dynamic instance dictionaries, generic data-layout
specialization, closure-returning callback interfaces and uninstantiated
polymorphic values remain outside this runtime slice. In particular the State
and Maybe proof tests above do not claim those generic data representations run
on Golem, and Reader callbacks returning closures retain an explicit refusal.
Full Reference syntax, universe, control-flow and runtime parity are not
claimed. The parent elaborator and runtime workstreams remain open.
