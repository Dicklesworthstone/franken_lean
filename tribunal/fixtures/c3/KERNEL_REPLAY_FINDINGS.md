# G0-2 findings memo — the kernel checks real modules from their oleans

Bead franken_lean-z6c (§22.1-2, feeds §8). On top of the G0-1 region reader, a
declaration decoder turns compacted Lean objects into FrankenLean term-plane
values (`Name`/`Level`/`Expr`/`ConstantInfo`), and a replay harness
(`crates/fln-conformance/tests/kernel_replay.rs`) drives every decoded
declaration of a REAL Reference module through the one authority,
`fln_kernel::check`. Statements AND proofs; identity-layer cross-checks on.

## What was proven

- **Decoding is faithful and self-checking.** The decoder reads each
  `@[computed_field]` word — `Name.hash`, `Level.Data`, `Expr.Data` — and
  compares it bit-for-bit against FrankenLean's own recomputation. Decoding all
  2 433 pinned stdlib oleans (158 608 constants) with cross-checks ON produced
  **zero** cross-check failures: the identity layer (mixHash/MurmurHash seeds,
  Level/Expr Data bit-packing) matches the pin exactly on real data, and the
  object layout is read correctly.
- **The kernel accepts real Reference declarations.** Replaying `Init.Prelude`
  (2 204 constants — the import-free root of the entire library):
  **1 233 / 1 755** kernel-checkable declarations (axioms, safe defs, theorems)
  **Accepted**, 0 Inconclusive, 522 Rejected. The 449 type-forming frontier
  declarations (inductives/constructors/recursors/quotients, plus opaque and
  unsafe/partial defs) are admitted-unchecked, honestly counted.
- **Every rejection is triaged to root cause (acceptance criterion (b)).** All
  522 rejections fall into named reduction-gap families, all requiring a
  reduction rule K1's bootstrap slice does not yet implement (marked follow-ups
  on bead franken_lean-zht):

  | family | count | missing rule |
  |---|---|---|
  | eliminator (`rec`/`recOn`/`casesOn`/`noConfusion`…) | 375 | iota |
  | custom eliminator (`.elim`/`ctorElim`) | 51 | iota |
  | equation-lemma helper (`._f`/`._sunfold`) | 26 | iota |
  | decidability instance (`decEq`/`instDecidable*`) | 21 | iota + proj |
  | structure projection/instance (`ReaderT.*`/`EStateM.*`/`inst*`) | 28 | proj reduction |
  | well-founded-recursion helper (`.brecOn.go`) | 7 | iota |
  | match-compiler auxiliary (`.match_N`) | 9 | iota |
  | nat-literal arithmetic (`UInt*.ofNatLT`/`Char.ofNatAux`) | 5 | Nat-literal reduction |

  Rejection *classes* are confined to `TypeMismatch`, `FunctionExpected`,
  `InvalidProjection`, `DefinitionTypeMismatch` — reduction/inference gaps, never
  a soundness-signalling class.

## The soundness argument

The Reference kernel **accepted every declaration in this module** when it wrote
the olean. Therefore every FrankenLean rejection here is, by definition, a
false-*reject* — a completeness gap — and never a false-*accept*. FL-INV-02 (the
kernel admits no bad constant) holds trivially on this corpus: there is nothing
the Reference refused for K1 to wrongly admit. What remains is exactly the
reduction-rule completeness work above, not a soundness problem. A future
rejection *class* outside the four listed would be a genuinely new divergence and
fails the harness loudly for triage.

## Layout / harness subtleties discovered

1. **`extends ConstantVal` is NOT flattened at the pin.** Every `*Val` stores
   its parent `ConstantVal` as a single nested object slot (slot 0), then its
   own fields — not the parent's three fields inlined. The first decode attempt
   assumed flattening and mis-read every definition's arity; the nested-object
   model is correct and now drives the decoder. (Contrast with the source-level
   "flattened field order" one might infer from the `structure ... extends`
   syntax.)
2. **The module `constants` array is storage order, not dependency order.** A
   naive in-order replay produced 1 385 spurious `UnknownConstant` rejections. A
   checker must topologically sort within the module (Kahn, stable module-order
   tie-break for determinism). After sorting, `UnknownConstant` vanishes entirely.
3. **The type-forming frontier is mutually referential.** An inductive's
   constructor's type names the inductive; recursors name their rules'
   constructors. This block cannot be linearized by dependency, so it is
   admitted as a unit (phase 1) before the checkable declarations are replayed
   in dependency order (phase 2). With that split there are **0** residual
   dependency cycles among checkable declarations.
4. **Projections resolve constructors through the environment.** K1's projection
   rule looks up `ind.ctors[0]`, so a structure's projection users depend on its
   constructor existing — an edge with no `Const` node in the term. The replay's
   dependency function adds it explicitly (constructor → inductive, and inductive
   users pull in constructors) or the frontier phase-1 admission covers it.

## Fuel / heartbeat accounting seam

`fln_kernel::check` already threads a `Budget { steps, depth }` and returns a
`Consumption` profile; the replay confirms the accounting seam exists and that
the default budget suffices for every checkable Prelude declaration (0
Inconclusive). Per-declaration fuel diffing against the Reference's heartbeat
counters is a K2-era refinement.

## Typed limitations (honest L-level)

- **Foreign-witness differential deferred.** The pinned toolchain ships
  `leanchecker`; wiring it as an external witness (running it over the same
  modules and diffing verdicts) is the natural next lane but is a heavier
  subprocess integration. This slice's differential is against the Reference
  kernel's *implicit* acceptance (it produced the olean); that is a real
  differential, just not yet the independent-binary one §8.7 ultimately wants.
- **Corpus absent.** mathlib4 is not installed on this host; the replay runs on
  the pinned stdlib (`Init.Prelude`) rather than a defeq-heavy mathlib file. The
  harness reads `FLN_REFERENCE_LIB` and extends to any module set once the
  Corpus lands.
- **iota/quot/K, projection reduction on instances, and Nat/Fin literal
  reduction** are the concrete completeness work this spike quantifies: closing
  them should convert the 522 rejections above into acceptances.
