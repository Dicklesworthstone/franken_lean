module

import Lean
import all Init.Prelude -- observe the complete Macro.State ABI, including its private field

open Lean

meta def nativeRflInputs : List Syntax :=
  [.node .none `Lean.Parser.Tactic.tacticRfl #[],
   .node .none `Lean.Parser.Tactic.tacticRfl #[.atom .none "wrong"],
   .node .none `Lean.Parser.Tactic.tacticRfl #[.atom .none "rfl"]]

meta def nativeRflReferences : List (Syntax × SourceInfo) :=
  let positioned := SourceInfo.synthetic ⟨2⟩ ⟨5⟩ true
  let expected := SourceInfo.synthetic ⟨2⟩ ⟨5⟩ false
  [(.missing, .none),
   (.atom positioned "rfl", expected),
   (.node .none `container #[.missing, .atom positioned "first", .atom .none "last"], expected),
   (.node .none `container #[.atom .none "first", .atom positioned "last"], .none)]

meta def nativeRflContexts : List Macro.Context :=
  [⟨default, `Client.Scope, 17, 3, 512, .missing⟩,
   ⟨default, `Other, 18446744073709551615, 0, 512, .missing⟩]

meta def nativeRflState : Macro.State := ⟨9, [(`Trace, "keep")], [`Prior]⟩

meta def nativeRflStateExact : Macro.State → Bool
  | ⟨scope, traces, declarations⟩ =>
    scope == 9 && traces == [(`Trace, "keep")] && declarations == [`Prior]

meta def nativeRflInfoExact : SourceInfo → SourceInfo → Bool
  | .none, .none => true
  | .synthetic p q c, .synthetic r s d =>
    p.byteIdx == r.byteIdx && q.byteIdx == s.byteIdx && c == d
  | _, _ => false

meta def nativeRflAtomExact (expected : SourceInfo) (keyword : String) : Syntax → Bool
  | .atom info value => nativeRflInfoExact info expected && value == keyword
  | _ => false

meta def nativeRflOutputExact (context : Macro.Context) (expected : SourceInfo)
    (kind : Name) (keyword : String) (constant : Option Name) : Syntax → Bool
  | .node info actual args =>
    nativeRflInfoExact info expected && actual == kind &&
    nativeRflAtomExact expected keyword args[0]! &&
    match constant with
    | none => args.size == 1
    | some declaration => args.size == 2 &&
      match args[1]! with
      | .ident info raw value [.decl target fields] =>
        nativeRflInfoExact info expected && raw.str == declaration.toString &&
        raw.startPos.byteIdx == 0 && raw.stopPos.byteIdx == 7 &&
        value == addMacroScope context.quotContext declaration context.currMacroScope &&
        target == declaration && fields.isEmpty
      | _ => false
  | _ => false

meta def nativeRflCandidates : List (Macro × Name × String × Option Name) :=
  [(Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticRfl_1,
    `Lean.Parser.Tactic.applyRfl, "apply_rfl", none),
   (Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticRfl_2,
    `Lean.Parser.Tactic.eqRefl, "eq_refl", none),
   (Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticRfl_3,
    `Lean.Parser.Tactic.exact, "exact", some `HEq.rfl),
   (_aux_Init_Core___macroRules_Lean_Parser_Tactic_tacticRfl_1,
    `Lean.Parser.Tactic.exact, "exact", some `Iff.rfl)]

meta def nativeRflPrint (checks : List Bool) : IO Unit :=
  IO.println ("[" ++ String.intercalate ", " (checks.map fun b => if b then "true" else "false") ++ "]")

#eval nativeRflPrint <| nativeRflCandidates.flatMap fun (macroFn, kind, keyword, constant) =>
  nativeRflContexts.flatMap fun context =>
    nativeRflReferences.flatMap fun (reference, expected) =>
      nativeRflInputs.map fun input =>
        match macroFn input { context with ref := reference } nativeRflState with
        | .ok output state =>
          nativeRflOutputExact context expected kind keyword constant output &&
          nativeRflStateExact state
        | _ => false

#eval nativeRflPrint <| nativeRflCandidates.flatMap fun (macroFn, _, _, _) =>
  [Syntax.missing, .atom .none "rfl", .node .none `User.tacticRfl #[]].map fun input =>
    match macroFn input ⟨default, `Client.Scope, 17, 3, 512, .missing⟩ nativeRflState with
    | .error .unsupportedSyntax state => nativeRflStateExact state
    | _ => false
