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

## Mixed-type operators

Operator leaves now use the existing checked coercion path to reach the type
chosen by operator elaboration. For example, an imported `Int` environment
supports both mixed addition and comparison:

```lean
import Init.Data.Int.Basic

def mixedAdd (n : Nat) (i : Int) : Int := n + i
def mixedLess (n : Nat) (i : Int) : Prop := i < n
```

The inserted conversion expands the builtin coercion projections and retains
the named `Nat.cast` application present in the pinned Lean terms. The same
path supports checked user-defined coercions on either operand, nested operator
trees, and operands whose target type is fixed by an expected result type.
Untagged conversion definitions remain explicit in the stored expression.

Coercion insertion shares ordinary expected-type inference's assignment
rollback and work accounting. It cannot create a missing operator instance or
bypass either checking seat. Failed files still publish no declarations.

`source_operator_elaboration` compares exact types and bodies against the
existing pinned Lean captures, including mixed `Nat`/`Int` operators. It also
checks user-defined conversions against their explicit forms, successful and
false proof results, failed-file atomicity, and recovery. The pin-dependent
checks require the official v4.32.0 artifacts:

```sh
FLN_REFERENCE_LIB=/path/to/lean-4.32.0-linux/lib/lean \
FLN_REQUIRE_REFERENCE=1 \
cargo test --locked -p fln --test source_operator_elaboration --test source_coercions
```
