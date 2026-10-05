/-
dump_command_syntax.lean: print the pinned frontend's `Syntax` for every command of a file
(bead franken_lean-z8j.1.10). This is the capture tool behind the frozen rows of
`crates/fln-parse/tests/reference_command_trees.rs`.

    T=~/.elan/toolchains/leanprover--lean4---v4.32.0
    $T/bin/lean --run scripts/extract/dump_command_syntax.lean FILE.lean "$T"

The file is processed exactly as `lean FILE.lean` would: the header's imports are loaded from
the given toolchain, and every command is parsed AND elaborated in order, so grammar the file
or its imports declare is in effect where `lean` would see it. Each command's tree is printed
as `COMMAND <Syntax.toString>`, then every message as `MESSAGE`. Nothing is written anywhere.
-/
import Lean
open Lean Elab Frontend

unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let path := args.head!
  let input ← IO.FS.readFile path
  initSearchPath (System.FilePath.mk args[1]!)
  let inputCtx := Parser.mkInputContext input path
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  IO.println s!"HEADER {header}"
  let (env, messages) ← processHeader header {} messages inputCtx
  IO.println s!"IMPORTED {env.header.moduleNames.size} modules"
  for msg in messages.toList do
    IO.println s!"HEADER-MESSAGE {← msg.toString}"
  let commandState := Command.mkState env messages {}
  let s ← IO.processCommands inputCtx parserState commandState
  for tree in s.commands do
    IO.println s!"COMMAND {tree}"
  for msg in s.commandState.messages.toList do
    IO.println s!"MESSAGE {← msg.toString}"
  return 0
