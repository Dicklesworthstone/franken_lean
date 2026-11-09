module
prelude
public import Init
public import Lean.Syntax
public section

-- Ordinary user code: these helpers must resolve through native Mirror rows,
-- including the typed getter emitted by `s:str` macro patterns.
@[noinline] def genericLiteralMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure (Lean.Syntax.mkLit `custom stx.getAtomVal stx.getHeadInfo).raw

@[noinline] def stringLiteralMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure (Lean.Syntax.mkStrLit stx.getAtomVal stx.getHeadInfo).raw

@[noinline] def quotedStringMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure (Lean.quote stx.getAtomVal : Lean.StrLit).raw

@[noinline] def inspectLiteralMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  match Lean.Syntax.isLit? `custom stx with
  | some value => pure (Lean.mkAtom value)
  | none => pure .missing

@[noinline] def inspectStringMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  match stx.isStrLit? with
  | some value => pure (Lean.mkAtom value)
  | none => pure .missing

@[noinline] def typedStringMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure (Lean.mkAtom (Lean.TSyntax.getString ⟨stx⟩))

syntax (name := stringEcho) "stringEcho% " str : term
@[macro stringEcho] meta def expandStringEcho : Lean.Macro
  | `(stringEcho% $s:str) => pure (Lean.Syntax.mkStrLit s.getString).raw
  | _ => Lean.Macro.throwUnsupported
