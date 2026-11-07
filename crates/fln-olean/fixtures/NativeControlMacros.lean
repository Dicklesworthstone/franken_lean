module

import Lean
import all Init.Prelude -- inspect the complete Macro.State, including private fields

open Lean

-- A lossless comparison wire for this oracle fixture, including original
-- trivia, raw identifier backing, structural names and pre-resolved targets.
-- Length-prefixed UTF-8 text keeps punctuation and non-ASCII names unambiguous.
meta def controlText (s : String) : String := s!"{s.utf8ByteSize}:{s}"

meta def controlName : Name → String
  | .anonymous => "a"
  | .str parent component => "s" ++ controlName parent ++ controlText component
  | .num parent component => "u" ++ controlName parent ++ s!"{component};"

meta def controlRaw (raw : Substring.Raw) : String :=
  controlText raw.str ++ s!"{raw.startPos.byteIdx},{raw.stopPos.byteIdx};"

meta def controlInfo : SourceInfo → String
  | .none => "-"
  | .synthetic start stop canonical =>
    s!"s{start.byteIdx},{stop.byteIdx},{if canonical then 1 else 0};"
  | .original leading pos trailing endPos =>
    "o" ++ controlRaw leading ++ s!"{pos.byteIdx};" ++
      controlRaw trailing ++ s!"{endPos.byteIdx};"

meta def controlPreresolved : Syntax.Preresolved → String
  | .namespace n => "n" ++ controlName n
  | .decl n fields => "d" ++ controlName n ++ "[" ++
    String.join (fields.map controlText) ++ "]"

meta partial def controlSyntax : Syntax → String
  | .missing => "m"
  | .node info kind args => "N" ++ controlInfo info ++ controlName kind ++ "[" ++
    String.join (args.toList.map controlSyntax) ++ "]"
  | .atom info text => "A" ++ controlInfo info ++ controlText text
  | .ident info raw val pre => "I" ++ controlInfo info ++ controlRaw raw ++
    controlName val ++ "[" ++ String.join (pre.map controlPreresolved) ++ "]"

meta def controlStateExact : Macro.State → Bool
  | ⟨scope, traces, declarations⟩ =>
    scope == 9 && traces == [(`Trace, "keep")] && declarations == [`Prior]

meta def controlCandidates : List (Macro × Name) :=
  [(Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticExfalso_1,
    `Lean.Parser.Tactic.tacticExfalso),
   (Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticInfer_instance_1,
    `Lean.Parser.Tactic.tacticInfer_instance),
   (Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTry__1,
    `Lean.Parser.Tactic.tacticTry_),
   (Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticNofun_1,
    `Lean.Parser.Tactic.tacticNofun)]

meta def controlContexts : List Macro.Context :=
  [⟨default, `Client.Scope, 17, 3, 512, .missing⟩,
   ⟨default, `Other, 18446744073709551615, 0, 512, .missing⟩]

meta def controlReferences : List Syntax :=
  let positioned := SourceInfo.synthetic ⟨2⟩ ⟨5⟩ true
  [.missing,
   .atom positioned "rfl",
   .node .none `container #[.missing, .atom positioned "first", .atom .none "last"],
   .node .none `container #[.atom .none "first", .atom positioned "last"]]

meta def controlBody : Syntax :=
  let source := "  rfl    "
  let original := SourceInfo.original ⟨source, ⟨0⟩, ⟨2⟩⟩ ⟨2⟩
    ⟨source, ⟨5⟩, ⟨9⟩⟩ ⟨5⟩
  .node .none `Client.body #[
    .ident original ⟨"prefix::local::suffix", ⟨8⟩, ⟨13⟩⟩
      (.num `Captured._hyg 23) [.namespace `Imported, .decl `Target ["field"]],
    .missing,
    .atom (.synthetic ⟨2⟩ ⟨5⟩ false) "λ"]

meta def controlInputs (kind : Name) : List Syntax :=
  [.node .none kind #[],
   .node .none kind #[.atom .none "wrong"],
   .node .none kind #[.atom .none "wrong", controlBody],
   .node .none kind #[.atom .none "wrong", .missing, .atom .none "extra"]]

meta def runControlMacros : IO Unit := do
  let state : Macro.State := ⟨9, [(`Trace, "keep")], [`Prior]⟩
  for (macroFn, kind) in controlCandidates do
    for context in controlContexts do
      for reference in controlReferences do
        for input in controlInputs kind do
          match macroFn input { context with ref := reference } state with
          | .ok syntax next =>
            IO.println ("ok:" ++ controlSyntax syntax ++ s!":{controlStateExact next}")
          | .error _ _ => IO.println "unexpected-error"
    for input in [Syntax.missing, .atom .none "wrong", .node .none `User.tactic #[]] do
      match macroFn input ⟨default, `Client.Scope, 17, 3, 512, .missing⟩ state with
      | .error .unsupportedSyntax next =>
        IO.println s!"unsupported:{controlStateExact next}"
      | _ => IO.println "unexpected-result"

#eval runControlMacros
