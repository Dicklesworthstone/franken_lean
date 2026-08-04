import Lean

open Lean Elab Command

namespace FlnG04

private def hexByte (byte : UInt8) : String :=
  hexDigitRepr (byte.toNat / 16) ++ hexDigitRepr (byte.toNat % 16)

private def hex (text : String) : String :=
  text.toUTF8.foldl (fun out byte => out ++ hexByte byte) ""

private def field (text : String) : String :=
  s!"{text.utf8ByteSize}:{hex text}"

private def encodeSubstring (text : Substring.Raw) : String :=
  s!"{text.startPos.byteIdx},{text.stopPos.byteIdx},{field text.toString}"

private def encodeSourceInfo : SourceInfo → String
  | .original leading pos trailing endPos =>
      s!"O({encodeSubstring leading};{pos.byteIdx};{encodeSubstring trailing};{endPos.byteIdx})"
  | .synthetic pos endPos canonical =>
      s!"S({pos.byteIdx};{endPos.byteIdx};{if canonical then 1 else 0})"
  | .none => "Z"

private def encodePreresolved : Syntax.Preresolved → String
  | .namespace ns => s!"PNS({field ns.toString})"
  | .decl name fields =>
      s!"PDECL({field name.toString};{fields.length};{String.join (fields.map field)})"

private partial def encodeSyntax : Syntax → String
  | .missing => "M"
  | .atom info value => s!"A({encodeSourceInfo info};{field value})"
  | .ident info raw value preresolved =>
      s!"I({encodeSourceInfo info};{field raw.toString};{field value.toString};\
        {preresolved.length};{String.join (preresolved.map encodePreresolved)})"
  | .node info kind args =>
      s!"N({encodeSourceInfo info};{field kind.toString};{args.size};\
        {String.join (args.toList.map encodeSyntax)})"

private def emit (fixture phase disposition payload : String) : IO Unit :=
  IO.println s!"fln-g04-reference/1\t{fixture}\t{phase}\t{disposition}\t{hex payload}"

private def observeParse (fixture : String) (category : Name) (source : String) :
    CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) category source s!"<{fixture}>" with
  | .ok stx => emit fixture "parse" "accepted" (encodeSyntax stx)
  | .error message => emit fixture "parse" "parse-error" message

private def observeExpansion (fixture : String) (category : Name) (source : String) :
    CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) category source s!"<{fixture}>" with
  | .error message => emit fixture "expand" "parse-error" message
  | .ok stx =>
      try
        let expanded ← liftMacroM <| expandMacros stx
        emit fixture "expand" "accepted" (encodeSyntax expanded)
      catch exception =>
        emit fixture "expand" "expansion-error" (← exception.toMessageData.toString)

run_cmd observeParse "c0_pratt_trivia" `term "1 + /- nested /- block -/ trivia -/ 2 * 3"
run_cmd observeParse "c0_unicode_positions" `term "α + β -- trailing\n"
run_cmd observeParse "c0_missing_rhs" `term "1 +"

run_cmd observeParse "c1_call_before_registration" `term "call Nat.add (1 + 2, 3)"

/- Exact successful source row from the pinned Lean test
   `tests/elab/macro2.lean`, with only the surrounding test declaration omitted. -/
syntax "call" term:max "(" sepBy1(term, ",") ")" : term

macro_rules
  | `(call $f ($args,*)) => `($f $args*)

run_cmd observeParse "c1_call_parse" `term "call Nat.add (1 + 2, 3)"
run_cmd observeExpansion "c1_call_expand" `term "call Nat.add (1 + 2, 3)"
run_cmd observeParse "c1_call_malformed" `term "call Nat.add (1 + 2,)"

/- Exact parser and successful macro arm from mathlib4
   `Mathlib/LinearAlgebra/Matrix/Notation.lean:91-108` at the SUITE.lock
   Corpus commit. The fixture needs only syntax expansion, so the downstream
   `Matrix.of` declaration is intentionally not imported or executed. -/
syntax (name := matrixNotation)
  "!![" ppRealGroup(sepBy1(ppGroup(term,+,?), ";", "; ", allowTrailingSep)) "]" : term

macro_rules
  | `(!![$[$[$rows],*];*]) => do
    let m := rows.size
    let n := if h : 0 < m then rows[0].size else 0
    let rowVecs ← rows.mapM fun row : Array Term => do
      unless row.size = n do
        Macro.throwErrorAt (mkNullNode row) s!"\
          Rows must be of equal length; this row has {row.size} items, \
          the previous rows have {n}"
      `(![$row,*])
    `(@Matrix.of (Fin $(quote m)) (Fin $(quote n)) _ ![$rowVecs,*])

run_cmd observeParse "c2_matrix_parse" `term "!![1, 2; 3, 4]"
run_cmd observeExpansion "c2_matrix_expand" `term "!![1, 2; 3, 4]"
run_cmd observeExpansion "c2_matrix_uneven" `term "!![1, 2; 3]"

end FlnG04
