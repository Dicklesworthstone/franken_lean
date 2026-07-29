# real-mathlib fixture selection — the review-amendment row fields (bead franken_lean-y24, G0-1)

The G0-1 review amendment requires a manifest-complete real-mathlib fixture set
whose every row binds: exact bytes/size, Reference producer binary/commit,
SUITE.lock and Corpus commits, module/import closure, platform, canonical
contract root, extension-entry census, selection rationale, clean-clone
materialization method, and expected semantic/structural facts. MANIFEST.txt
carries the per-row machine fields; this file carries the rest.

## Producer

- Corpus: `leanprover-community/mathlib4`, tag v4.32.0, commit
  `81a5d257c8e410db227a6665ed08f64fea08e997` (the `corpus` row of SUITE.lock;
  the checkout's HEAD is verified equal to it by the probe before any walk).
- Toolchain: `leanprover/lean4:v4.32.0`, commit
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35` (the `reference` row of
  SUITE.lock; the mathlib checkout's `lean-toolchain` names exactly it).
- Bytes: produced by the mathlib CI cache pipeline for that corpus commit and
  fetched verbatim with `lake exe cache get` (8639 artifacts, 7.1 GiB at
  fetch time). Never recompiled, never edited by us. Platform: linux x86_64.

## Canonical contract root

Every decoded field maps to the canonical inventory: the OLEAN domain root of
`contracts/olean_inventory.json` (schema `fln-olean-inventory/*`, pinned by the
W1 terminal join, bead franken_lean-53v). ABI_CONTRACT.md and OLEAN_CONTRACT.md
project that root; they are not competing authorities.

## Selection rationale

Six modules, one row each, spanning the cones the downstream readers actually
stress:

| module | why it is in the set |
|---|---|
| `Mathlib.Order.Basic` | Heaviest measured environment-extension payload in the surveyed candidates: 44 blocks / 1591 entries, including simp-set extensions built across the order hierarchy. This is the amendment's required heavy-extension row. |
| `Mathlib.Algebra.Group.Basic` | Deep algebraic-hierarchy module; 1445 extension entries over 509 constants — the densest extension-to-constant ratio in the set. |
| `Mathlib.Data.Real.Basic` | The README's `why-trusts` example module; analysis cone with 1005 extension entries. |
| `Mathlib.Tactic.Basic` | The tactic surface itself: 37 blocks / 649 entries of tactic-environment payload, the extension shape metaprograms install. |
| `Mathlib.Analysis.SpecialFunctions.Log.Basic` | A deep leaf in the analysis cone (the `log_pos` module of the README example). |
| `Mathlib.Algebra.Ring.Basic` | Ring hierarchy; the smallest payload in the set (21 blocks / 222 entries), kept as the low-end control so the manifest is not all maxima. |

Expected semantic/structural facts per row (objects, import count, constants,
extension blocks/entries) are the MANIFEST.txt columns; the probe re-walks
every row and refuses on any mismatch. The ordered import closure per row,
including `import_all` / `is_exported` / `is_meta` flags and duplicate
preservation, is IMPORTS.tsv — the same oracle shape the C3 family uses.

## Clean-clone materialization method

The six fixture byte files are TRACKED in this directory (2,393,304 bytes
total, under the narrow `!/tribunal/fixtures/mathlib/*.olean` ignore exception,
exactly the ci0/C3 law: manifest-bound bytes must exist in a clean clone).
Regeneration instead of tracking is a deliberate act against the pin: fetch
the corpus commit, `lake exe cache get`, copy the same six paths, and require
MANIFEST.txt to match byte-for-byte — which is what
`scripts/tribunal/g01_resurrection_probe.sh --regenerate-mathlib-fixtures`
does and verifies.

## What this set does not claim

Six of 8639 published mathlib modules, chosen by the rationale above — a
manifest-complete set per the amendment, not the whole corpus. A whole-corpus
walk is an on-demand sweep, not a fixture obligation; the probe's typed skip
covers hosts without the corpus checkout, exactly as the stdlib lane covers
hosts without the pinned toolchain.
