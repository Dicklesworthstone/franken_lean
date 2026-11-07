module

import Init
import all Init.Prelude -- inspect all of Macro.State, including private fields

open Lean

-- The same lossless wire as NativeControlMacros.lean: syntax kinds, structural
-- names, owned raw identifier backing, every source-info field and preresolved
-- targets are observable. The callable is the actual pinned registration.
meta def compositeText (s : String) : String := s!"{s.utf8ByteSize}:{s}"

meta def compositeName : Name → String
  | .anonymous => "a"
  | .str parent component => "s" ++ compositeName parent ++ compositeText component
  | .num parent component => "u" ++ compositeName parent ++ s!"{component};"

meta def compositeRaw (raw : Substring.Raw) : String :=
  compositeText raw.str ++ s!"{raw.startPos.byteIdx},{raw.stopPos.byteIdx};"

meta def compositeInfo : SourceInfo → String
  | .none => "-"
  | .synthetic start stop canonical =>
    s!"s{start.byteIdx},{stop.byteIdx},{if canonical then 1 else 0};"
  | .original leading pos trailing endPos =>
    "o" ++ compositeRaw leading ++ s!"{pos.byteIdx};" ++
      compositeRaw trailing ++ s!"{endPos.byteIdx};"

meta def compositePreresolved : Syntax.Preresolved → String
  | .namespace n => "n" ++ compositeName n
  | .decl n fields => "d" ++ compositeName n ++ "[" ++
    String.join (fields.map compositeText) ++ "]"

meta partial def compositeSyntax : Syntax → String
  | .missing => "m"
  | .node info kind args => "N" ++ compositeInfo info ++ compositeName kind ++ "[" ++
    String.join (args.toList.map compositeSyntax) ++ "]"
  | .atom info text => "A" ++ compositeInfo info ++ compositeText text
  | .ident info raw val pre => "I" ++ compositeInfo info ++ compositeRaw raw ++
    compositeName val ++ "[" ++ String.join (pre.map compositePreresolved) ++ "]"

meta def compositeStateExact : Macro.State → Bool
  | ⟨scope, traces, declarations⟩ =>
    scope == 9 && traces == [(`Trace, "keep")] && declarations == [`Prior]

meta def compositeCandidates : List (Macro × Name) :=
  [(Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticRwa___1,
    `Lean.Parser.Tactic.tacticRwa__),
   (Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_rwSeq_1,
    `Lean.Parser.Tactic.rwSeq),
   (Lean.Parser.Tactic.«_aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tactic_<;>__1»,
    `Lean.Parser.Tactic.«tactic_<;>_»),
   (Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTrivial_1,
    `Lean.Parser.Tactic.tacticTrivial),
   (Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTrivial_2,
    `Lean.Parser.Tactic.tacticTrivial),
   (Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTrivial_3,
    `Lean.Parser.Tactic.tacticTrivial),
   (Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTrivial_4,
    `Lean.Parser.Tactic.tacticTrivial),
   (Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTrivial_5,
    `Lean.Parser.Tactic.tacticTrivial),
   (Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTrivial_6,
    `Lean.Parser.Tactic.tacticTrivial)]

meta def compositeContexts : List Macro.Context :=
  [⟨default, `Client.Scope, 17, 3, 512, .missing⟩,
   ⟨default, `Other, 18446744073709551615, 0, 512, .missing⟩]

meta def compositeReferences : List Syntax :=
  let positioned := SourceInfo.synthetic ⟨2⟩ ⟨5⟩ true
  [.missing,
   .atom positioned "rfl",
   .node .none `container #[.missing, .atom positioned "first", .atom .none "last"],
   .node .none `container #[.atom .none "first", .atom positioned "last"]]

meta def compositeBody : Syntax :=
  let source := "  rfl    "
  let original := SourceInfo.original ⟨source, ⟨0⟩, ⟨2⟩⟩ ⟨2⟩
    ⟨source, ⟨5⟩, ⟨9⟩⟩ ⟨5⟩
  .node .none `Client.body #[
    .ident original ⟨"prefix::local::suffix", ⟨8⟩, ⟨13⟩⟩
      (.num `Captured._hyg 23) [.namespace `Imported, .decl `Target ["field"]],
    .missing,
    .atom (.synthetic ⟨2⟩ ⟨5⟩ false) "λ"]

-- Wrong token spellings and excess/missing children establish the generated
-- matcher's real boundary. In particular optional captures and rw's nested
-- rule-sequence pattern cannot be inferred from a valid parsed example alone.
meta def compositeInputs (kind : Name) : List Syntax :=
  let wrong := Syntax.atom .none "wrong"
  let extra := Syntax.atom .none "extra"
  let body := compositeBody
  [.node .none kind #[],
   .node .none kind #[wrong],
   .node .none kind #[wrong, body],
   .node .none kind #[wrong, .missing, extra],
   .node .none kind #[wrong, body, .node .none `null #[]],
   .node .none kind #[wrong, body, .node .none `null #[body]],
   .node .none kind #[wrong, body, .node .none `null #[body, .missing]],
   .node .none kind #[wrong, body, .node .none `Other.optional #[body]],
   .node .none kind #[wrong, body, .node .none `Lean.Parser.Tactic.rwRuleSeq #[],
     .node .none `null #[body]],
   .node .none kind #[wrong, body,
     .node .none `Lean.Parser.Tactic.rwRuleSeq #[wrong,
       .node .none `Other.separated #[body, .atom .none ",", .missing], body, extra],
     .node .none `null #[body], extra]]

meta def runCompositeMacros : IO Unit := do
  let state : Macro.State := ⟨9, [(`Trace, "keep")], [`Prior]⟩
  for (macroFn, kind) in compositeCandidates do
    for context in compositeContexts do
      for reference in compositeReferences do
        for input in compositeInputs kind do
          match macroFn input { context with ref := reference } state with
          | .ok stx next =>
            IO.println ("ok:" ++ compositeSyntax stx ++ s!":{compositeStateExact next}")
          | .error .unsupportedSyntax next =>
            IO.println s!"unsupported:{compositeStateExact next}"
          | .error _ _ => IO.println "unexpected-error"
    for input in [Syntax.missing, .atom .none "wrong", .node .none `User.tactic #[]] do
      match macroFn input ⟨default, `Client.Scope, 17, 3, 512, .missing⟩ state with
      | .error .unsupportedSyntax next =>
        IO.println s!"unsupported:{compositeStateExact next}"
      | _ => IO.println "unexpected-result"

#eval runCompositeMacros
