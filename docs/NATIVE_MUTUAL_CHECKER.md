# Native mutual-inductive admission

The independent checker reconstructs bounded, safe mutual **data**-inductive
blocks instead of refusing every block containing more than one type. This
extends declaration admission and the native standalone `.olean` checking path.
It does not add a source-level `mutual` parser production, execute Reference
code, or claim that the complete pinned Prelude or mathlib council passes.

## Supported admission shape

A block may contain two to eight families sharing their universe parameters,
parameter telescope, and provably positive result sort. Parameters may depend
on earlier parameters. Each family may have its own dependent index telescope;
recursive children select the destination family's actual indices, not the
parent family's index count.

Constructors may contain ordinary fields, direct self- or cross-family recursive
fields, and strictly positive function-valued recursive fields. Function argument
telescopes remain dependent and capture-free. Multiple recursive children may be
interleaved with ordinary fields; each gets its own induction hypothesis and
recursive call, in constructor-field order.

Nested occurrences beneath unrelated type constructors, proposition-valued
mutual blocks, possibly-zero result universes, and blocks outside the supported
bounds remain explicit support nonanswers. This increment does not claim full
upstream inductive-language coverage.

## Trust boundary

Every family signature must be a type in the predecessor environment, before
any sibling type is staged. A cyclic signature cannot justify itself through a
private partially-built environment. Constructor types are subsequently checked
with all family headers available, but recursors remain unavailable until their
reconstruction succeeds.

The checker derives all motives, constructor minor premises, induction
hypotheses, and iota right-hand sides from the family and constructor telescopes.
The incoming recursor types and rules are comparison subjects, not templates.
Each recursive call retains the shared parameters, every ordered motive and
minor, the destination indices, and the actual recursive field. Strict positivity
examines function domains against **every** family in the block.

Metadata must agree with the reconstructed block: ownership, constructor indices,
universe and parameter counts, complete mutual lists, recursive/reflexive flags,
recursor arities, and rule membership. Original annotated constructor signatures
are checked before supported recursor-binder annotation erasure.

Only complete success returns all admitted member identities. Missing members,
forged rules, type errors, resource stops, or final cancellation cannot expose a
partial successor. K1 is unchanged and remains a separate required admission
seat. A K1 acceptance cannot override an independent-checker nonanswer.

## Bounds

The mutual profile allows at most eight families, 32 constructors in total,
64 constructor fields in total, eight shared universe parameters, and 64 shared
parameters plus aggregate family indices. Its absolute row ceiling is 48;
single-family admission retains its original 34-row ceiling. Input and generated
term arenas retain the existing bounded inductive-arena policy, alongside caller
supplied inference, conversion, term, environment, and cancellation controls.

## Executable coverage

```sh
cargo test --locked -p fln-checker
cargo test --locked -p fln --test mutual_inductive_admission
cargo test --locked -p fln --lib
cargo clippy --locked -p fln-checker -p fln --all-targets -- -D warnings
cargo check --locked --workspace --all-targets
```

`crates/fln-checker/tests/mutual_inductives.rs` uses independently hand-built
named-local fixtures, with no access to either checker's recursor generator.
It covers shared dependent parameters, differing index telescopes, function
children, multiple induction hypotheses, declaration-row permutation, forged
calls, negative recursion, cyclic signatures, inconsistent universes, missing
members, resource bounds, and cancellation.

`crates/fln/tests/mutual_inductive_admission.rs` sends the same candidates through
the production two-seat council. It also checks cross-family iota conversion in
an ordinary definition, native-produced `.olean` write/decode/planning/admission,
late-failure atomicity, and the independent resource veto on K1-accepted inputs.
Those generated artifacts are model fixtures, not Reference-artifact evidence.
