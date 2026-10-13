/-
upstream_suite_headers.lean: print the pinned frontend's parsed header for each file
(bead fln-upstream-suite-scoreboard-n04o). The upstream-suite scoreboard derives each
file's stratum from these rows, never from a regular expression over the source.

    T=~/.elan/toolchains/leanprover--lean4---v4.32.0
    $T/bin/lean --run scripts/extract/upstream_suite_headers.lean FILE.lean...

Each file prints one row, `HEADER <file>\t<kind>\t<imports, comma-separated>`. `kind` is
`prelude` when the header says `prelude` and `implicit` when `Init` is implied, prefixed
with `module-` when the header opens with the `module` keyword. The imports are the
header's EXPLICIT `import` commands, in order. A header the pin cannot parse prints
`HEADER <file>\tunparsed\t`; a file that is not UTF-8 prints `HEADER <file>\tunreadable\t`. Nothing is elaborated and nothing is written anywhere.
-/
import Lean
open Lean

def main (args : List String) : IO UInt32 := do
  for path in args do
    -- A file that is not UTF-8 (the suite has one on purpose) has no parsed header.
    let bytes ← IO.FS.readBinFile path
    let some input := String.fromUTF8? bytes | do
      IO.println s!"HEADER {path}\tunreadable\t"
      continue
    let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext input path)
    if messages.hasErrors then
      IO.println s!"HEADER {path}\tunparsed\t"
    else
      -- `Module.header`: [module keyword?] [prelude?] [import*]; an import is
      -- [public?] [meta?] "import" [all?] ident.
      let stx := header.raw
      let isModule := !stx[0].isNone
      let isPrelude := !stx[1].isNone
      let imports := stx[2].getArgs.map (·[4].getId.toString)
      let kind := (if isModule then "module-" else "") ++ (if isPrelude then "prelude" else "implicit")
      IO.println s!"HEADER {path}\t{kind}\t{",".intercalate imports.toList}"
  return 0
