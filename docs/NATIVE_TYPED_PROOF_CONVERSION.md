# Typed proof conversion in the independent checker

The independent checker can discharge proof-irrelevance obligations under function
binders at declaration-body, application-domain and local-let conversion sites.
This is a sufficient typed conversion lane, not a new rule in K1, an axiom, or
function extensionality. The raw untyped `def_eq` interface retains its contract.

For example, the source checker admits this generic theorem through both engines:

```lean
theorem same (A : Type) (P : A -> Prop)
    (f : forall x : A, P x -> Nat) (p q : forall x : A, P x) :
    (fun x => f x (p x)) = (fun x => f x (q x)) := by rfl
```

When ordinary conversion defers, the typed worklist opens corresponding binders
with fresh, collision-checked local identities. Their domains are compared before
the bodies are opened. Applications are compared componentwise. The checker may
identify two proof witnesses only after checker-owned typing establishes that
both have proposition types and those proposition types are themselves convertible.
Different propositions, arbitrary data, and unknown universe levels are not
collapsed. Local definitions retain their values in the typing/reduction context.

Typing probes explicitly disable recursive entry into this new conversion lane.
Expression depth is handled by existing heap worklists plus the typed comparison
worklist; it does not determine host call depth. Every nested probe polls the
same aggregate work/cancellation counter. Exhaustion remains an inconclusive
result and unsupported obligations remain deferred, never accepted by default.
The ordinary inference pass still checks complete original terms, including
unused arguments and written annotations, before a final body conversion succeeds.
Unsafe proof sources remain subject to ordinary safety checks.

Independent wire fixtures cover final, application and let conversions, mismatched
propositions and data, domain/capture mutants, polymorphic sorts, cancellation,
recovery and a 64-binder comparison on a 128 KiB thread stack. Source regressions
exercise generic dependent proof functions and invalid unused annotations.
This does not establish full proof-irrelevance completeness, arbitrary function
extensionality, Reference heartbeat parity, or a full-workspace conformance result.
