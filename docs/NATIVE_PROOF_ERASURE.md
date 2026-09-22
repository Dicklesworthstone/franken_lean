# Native runtime proof erasure

The native execution bridge erases checked proof computations before FIR ingress.
The original declaration is still admitted by K1 and the independent checker;
proof erasure never validates a declaration, supplies evidence, or alters its
logical environment. A false proof in an unused argument or declaration remains
an error. Unsupported or resource-exhausted classification cannot authorize
an erasure.

```lean
def keep (n : Nat) (h : n = n) : Nat := n
#eval keep 42 (by rfl)
```

Proof arguments (including dependent propositions), proof-producing function
arguments, proof lets, local callbacks, partial applications, and ground
polymorphic calls are supported. Runtime interfaces are derived from the same
erased telescopes as their bodies. Original lexical types are retained during
the traversal so equal de Bruijn nodes in different scopes cannot share the
wrong classification. Type parameters and recursor motives remain original
inputs to specialization, not guessed executable values.

The current FIR profile retains an inert scalar-zero slot for each proof
parameter. It uses the existing exact-seed-checked `Bool.false` representation;
source typing prevents inspecting such a slot as a Boolean. This removes proof
*construction* and its executable dependencies, not argument/field positions.
It is not a claim of the Reference's packed ABI or a slot-removal optimization.
Without the exact scalar seed the bridge does not apply this erasure.

The traversal and nested type-domain worklists use the heap, explicit context
limits, fallible reservations, and the existing ingress work budget. Ordinary
computations, including unused let initializers and runtime arguments, remain
strict. In particular a million-step computation confined to a proof is not
run, while the same computation in a non-proof position is not discarded.

Tests: `crates/fln/tests/runtime_proof_erasure.rs`. This advances the Golem
runtime integration workstream, not full Lean runtime parity. Dependent runtime
representations and general proof-to-data eliminators remain outside this
increment. Checked proof arguments are not permission to execute arbitrary
axioms such as `Classical.choice`.
