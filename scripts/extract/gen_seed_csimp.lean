/-
gen_seed_csimp.lean — the recursors the pin's code generator replaces through a
`@[csimp]` lemma (bead franken_lean-z8j.1.6.6).

Run BY THE PINNED REFERENCE BINARY ONLY (D8-2: the Reference as fixture mine), via
scripts/extract/gen_seed_csimp.sh, which verifies the binary's commit against
SUITE.lock before trusting a byte of this output.

Usage: lean --run gen_seed_csimp.lean

The pin compiles a definition by first rewriting every constant through its
`@[csimp]` replacement (`CSimp.replaceConstant`, vendored
src/Lean/Compiler/LCNF/ToLCNF.lean:818); a recursor that survives is refused
("code generator does not support recursor", ToImpure.lean:184). So a recursor
is compilable exactly when the csimp set, as `import Init` sees it, replaces it.
One record per such recursor, tab-separated, sorted:

  recursor <TAB> replacement
-/
import Lean
open Lean

unsafe def main (_ : List String) : IO Unit := do
  -- The running binary's own library: `findSysroot` would ask whichever `lean` is first
  -- on PATH, which need not be the pin.
  let some sysroot := (← IO.appDir).parent
    | throw <| IO.userError "cannot locate the running binary's toolchain"
  initSearchPath sysroot
  enableInitializersExecution
  let env ← importModules #[{ module := `Init }] {} (loadExts := true)
  let mut rows : Array String := #[]
  for (source, entry) in (Compiler.CSimp.ext.getState env).map.toList do
    if let some (.recInfo _) := env.find? source then
      rows := rows.push s!"{source}\t{entry.toDeclName}"
  for row in rows.qsort (· < ·) do
    IO.println row
