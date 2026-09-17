# Deferred native source conversion

Ordinary typing inference first uses the existing abbreviation-only unifier.
A successful first pass is retained, including named type identities used by
later typeclass selection. If structural matching defers with
`UnsupportedEquation` or `NotAPattern`, ordinary source typing equations retry
with safe-definition transparency. This is native reduction and the existing
transactional, K1-checked assignment mechanism, not an oracle fallback.

For example, both forms now elaborate and pass both checking seats:

```lean
def wrap (n : Nat) : Nat := n
theorem termProof (n : Nat) : wrap (wrap n) = n := rfl
theorem tacticProof (n : Nat) : wrap (wrap n) = n := by rfl
```

The retry is not special treatment for the spelling `rfl`. Other implicit
applications use it too; local declarations named `rfl` keep ordinary lexical
shadowing. Polymorphic definition bodies use the unifier's existing simultaneous
universe substitution before reduction.

Instance and rewrite selection equations do not acquire this retry. Their
matches must satisfy their original selection policies. In particular,
ordinary source conversion does not make `simp only []` unfold arbitrary
unselected definitions.

Each attempt retains spent work. Resource stops, cancellation, malformed
contexts, unknown metavariables, and failed assignment checks do not trigger a
safe-definition retry. Failed solver attempts publish no assignments. Kernel
and independent-checker admission remain necessary for every declaration.

A speculative `exact` against an instantiated, metavariable-free goal also
validates its candidate through the existing typed assignment checker before
selecting that alternative. This prevents a deferred, invalid `exact rfl`
from suppressing a valid later branch:

```lean
theorem fallback (x y : Nat) (h : x = y) : wrap x = y := by
  first | exact rfl | exact h
```

This is not full upstream elaboration or its complete conversion approximation
ladder. Unresolved obligations still fail, and a resource nonanswer is not a
rejection or a proof. The regression suite covers successful implicit and
polymorphic calls, beta/delta conversion, lexical shadowing, speculative
fallback, false equations, and budget failure through the real source pipeline.

```sh
cargo test --locked -p fln --test source_delta_inference
cargo test --locked -p fln-cli --test source_delta_inference
cargo test --locked -p fln --test source_instances --test source_backtracking
```
