/-
gen_seed_protected.lean — the pin's `protected` status for every constant of
FrankenLean's source seed (bead fln-8xz8).

Run BY THE PINNED REFERENCE BINARY ONLY (D8-2: the Reference as fixture mine), via
scripts/extract/gen_seed_protected.sh, which verifies the binary's commit against
SUITE.lock before trusting a byte of this output.

Usage: lean --run gen_seed_protected.lean <names-file>

`<names-file>` holds one seed constant name per line, as FrankenLean's own seed
admits them (the shell script obtains them from the seed itself). Each is looked up
in the environment a headerless file sees at the pin, `import Init`, and one record
is printed per name, tab-separated, in the input's order:

  name <TAB> status

- `protected`: the pin has the constant and `isProtected` (vendored
  src/Lean/Modifiers.lean) holds for it;
- `unprotected`: the pin has the constant and it is not protected;
- `absent`: the pin has no constant of that name (a seed constant with no
  counterpart), which therefore cannot be protected there.

A name containing a tab or a newline is refused rather than escaped.
-/
import Lean
open Lean

unsafe def main (args : List String) : IO Unit := do
  let [namesPath] := args | throw <| IO.userError "usage: gen_seed_protected.lean <names-file>"
  -- The running binary's own library: `findSysroot` would ask whichever `lean` is first
  -- on PATH, which need not be the pin.
  let some sysroot := (← IO.appDir).parent
    | throw <| IO.userError "cannot locate the running binary's toolchain"
  initSearchPath sysroot
  enableInitializersExecution
  let env ← importModules #[{ module := `Init }] {} (loadExts := true)
  for line in ← IO.FS.lines namesPath do
    if line.isEmpty then
      continue
    if line.any (fun c => c == '\t' || c == '\n') then
      throw <| IO.userError s!"unrepresentable seed name {line}"
    let name := line.toName
    if name.toString (escape := false) != line then
      throw <| IO.userError s!"seed name {line} does not round-trip as a Name"
    let status :=
      if !env.contains name then "absent"
      else if isProtected env name then "protected"
      else "unprotected"
    IO.println s!"{line}\t{status}"
