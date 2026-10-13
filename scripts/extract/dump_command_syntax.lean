/-
dump_command_syntax.lean: print the pinned frontend's `Syntax` for every command of a file
(beads franken_lean-z8j.1.10, fln-pin-syntax-corpus-7b5b). This is the capture tool behind the
frozen rows of `crates/fln-parse/tests/reference_command_trees.rs`, and with `--lossless` the
producer of the pin syntax corpus.

    T=~/.elan/toolchains/leanprover--lean4---v4.32.0
    $T/bin/lean --run scripts/extract/dump_command_syntax.lean FILE.lean "$T" [--lossless]

The file is processed exactly as `lean FILE.lean` would: the header's imports are loaded from
the given toolchain, and every command is parsed AND elaborated in order, so grammar the file
or its imports declare is in effect where `lean` would see it. Nothing is written anywhere.

Without `--lossless`, each command's tree is printed as `COMMAND <Syntax.toString>`, then every
message as `MESSAGE`. `Syntax.toString` drops source positions and prints macro scopes
ambiguously, so `--lossless` prints the schema `fln.pin-syntax/1` instead, one record per line:

    fln.pin-syntax/1
    HEADER                       then the header's tree, as below
    COMMAND <index>              then that command's tree, one node per line in pre-order:
      <depth> N <info> <kind> <arity>
                                   a node; <kind> is a name (below)
      <depth> A <info> <value>     an atom; <value> a JSON string
      <depth> I <info> <raw start> <raw stop> <raw> <name> <preresolved>
                                   an identifier: the raw substring's byte range and text
                                   (JSON string), the structural name, and the pre-resolved
                                   list (JSON)
      <depth> M                    `Syntax.missing`
    MESSAGE <severity> <line> <column> <text>      text a JSON string
    END <commands> <messages>

  <info> is `o <leading start> <leading stop> <pos> <end> <trailing start> <trailing stop>` for
  original syntax, byte offsets into the file; `s <pos> <end> <canonical>` for synthetic (canonical 0 or 1); `n` for none.
  A name is a JSON array of its components from the root: strings, and numbers for numeric
  components (macro scopes are numeric components), so `x._@.M._hyg.3` is unambiguous.
-/
import Lean
open Lean Elab Frontend

/-- A name's components from the root, as JSON. -/
def nameJson : Name → Array Json
  | .anonymous => #[]
  | .str p s => (nameJson p).push (Json.str s)
  | .num p n => (nameJson p).push (Json.num n)

def nameField (n : Name) : String := (Json.arr (nameJson n)).compress

def infoField : SourceInfo → String
  | .original leading pos trailing endPos =>
    s!"o {leading.startPos.byteIdx} {leading.stopPos.byteIdx} {pos.byteIdx} {endPos.byteIdx} \
      {trailing.startPos.byteIdx} {trailing.stopPos.byteIdx}"
  | .synthetic pos endPos canonical =>
    s!"s {pos.byteIdx} {endPos.byteIdx} {if canonical then 1 else 0}"
  | .none => "n"

def preresolvedJson : Syntax.Preresolved → Json
  | .namespace ns => Json.mkObj [("namespace", Json.arr (nameJson ns))]
  | .decl n fields =>
    Json.mkObj [("decl", Json.arr (nameJson n)), ("fields", Json.arr (fields.toArray.map Json.str))]

partial def emit (depth : Nat) : Syntax → IO Unit
  | .missing => IO.println s!"{depth} M"
  | .node info kind args => do
    IO.println s!"{depth} N {infoField info} {nameField kind} {args.size}"
    for arg in args do emit (depth + 1) arg
  | .atom info val => IO.println s!"{depth} A {infoField info} {(Json.str val).compress}"
  | .ident info rawVal val pre =>
    let raw := (Json.str rawVal.toString).compress
    let pre := (Json.arr (pre.toArray.map preresolvedJson)).compress
    let range := s!"{rawVal.startPos.byteIdx} {rawVal.stopPos.byteIdx}"
    IO.println s!"{depth} I {infoField info} {range} {raw} {nameField val} {pre}"

def severityName : MessageSeverity → String
  | .information => "info"
  | .warning => "warning"
  | .error => "error"

unsafe def main (args : List String) : IO UInt32 := do
  enableInitializersExecution
  let path := args.head!
  let lossless := args.contains "--lossless"
  let input ← IO.FS.readFile path
  initSearchPath (System.FilePath.mk args[1]!)
  let inputCtx := Parser.mkInputContext input path
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  if lossless then
    IO.println "fln.pin-syntax/1"
    IO.println "HEADER"
    emit 0 header.raw
  else
    IO.println s!"HEADER {header}"
  let (env, messages) ← processHeader header {} messages inputCtx
  unless lossless do
    IO.println s!"IMPORTED {env.header.moduleNames.size} modules"
    for msg in messages.toList do
      IO.println s!"HEADER-MESSAGE {← msg.toString}"
  let commandState := Command.mkState env messages {}
  let s ← IO.processCommands inputCtx parserState commandState
  let msgs := s.commandState.messages.toList
  if lossless then
    let mut index := 0
    for tree in s.commands do
      IO.println s!"COMMAND {index}"
      emit 0 tree
      index := index + 1
    for msg in msgs do
      let text := (Json.str (← msg.data.toString)).compress
      IO.println s!"MESSAGE {severityName msg.severity} {msg.pos.line} {msg.pos.column} {text}"
    IO.println s!"END {s.commands.size} {msgs.length}"
  else
    for tree in s.commands do
      IO.println s!"COMMAND {tree}"
    for msg in msgs do
      IO.println s!"MESSAGE {← msg.toString}"
  return 0
