module
prelude
public import Init
public import Lean.Syntax
public section

-- Real user MacroM IR combining the native quotation-pattern services. The
-- result retains the optional child's exact syntax and the erased Name.
@[noinline] def patternServicesMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax := do
  let id := stx[0].getId
  let target := stx[1].getId
  let kind := stx[2].getId
  let size := (⟨stx[3]⟩ : Lean.NumLit).getNat
  let lit := stx[4]
  let text := stx[5].getAtomVal
  let optional := stx[6]
  let candidate := stx[7]
  pure (.node .none `patternResult #[
    Lean.mkAtom (if id.hasMacroScopes then "true" else "false"),
    .ident .none ⟨"", ⟨0⟩, ⟨0⟩⟩ id.eraseMacroScopes [],
    Lean.mkAtom (if stx[0].matchesIdent target then "true" else "false"),
    Lean.mkAtom (if lit.matchesLit kind text then "true" else "false"),
    Lean.mkAtom (if optional.matchesNull size then "true" else "false"),
    Lean.mkAtom (if candidate.isNodeOf kind size then "true" else "false"),
    match optional.getOptional? with
      | some value => value
      | none => .missing])

-- Repetition antiquotations use the same erased array carriers as these
-- separated-syntax helpers. Keep the calls visible in real imported user IR.
@[noinline] def separatedServicesMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax := do
  let values := stx[0].getArgs
  let separator := stx[1]
  let candidate := stx[2]
  pure (.node .none `separatedResult #[
    Lean.mkNullNode (Lean.mkSepArray values separator),
    Lean.Syntax.mkSep values separator,
    Lean.mkNullNode candidate.getSepArgs,
    Lean.mkNullNode (⟨candidate.getArgs⟩ : Lean.Syntax.SepArray ",").getElems,
    Lean.mkNullNode (⟨candidate.getArgs⟩ : Lean.Syntax.TSepArray `term ",").getElems.raw])
