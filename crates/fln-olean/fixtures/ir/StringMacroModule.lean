module
prelude
public import Init
public import Lean.Syntax
public section

-- Ordinary user code: these helpers must resolve through native Mirror rows,
-- including the typed getters emitted by `s:str` and `c:char` macro patterns.
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

@[noinline] def characterLiteralMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure (Lean.Syntax.mkCharLit (Lean.TSyntax.getChar ⟨stx⟩) stx.getHeadInfo).raw

@[noinline] def quotedCharacterMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure (Lean.quote (Lean.TSyntax.getChar ⟨stx⟩) : Lean.CharLit).raw

@[noinline] def inspectCharacterMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  match stx.isCharLit? with
  | some value => pure (Lean.Syntax.mkCharLit value).raw
  | none => pure .missing

syntax (name := stringEcho) "stringEcho% " str : term
@[macro stringEcho] meta def expandStringEcho : Lean.Macro
  | `(stringEcho% $s:str) => pure (Lean.Syntax.mkStrLit s.getString).raw
  | _ => Lean.Macro.throwUnsupported

syntax (name := characterEcho) "charEcho% " char : term
@[macro characterEcho] meta def expandCharacterEcho : Lean.Macro
  | `(charEcho% $c:char) => pure (Lean.Syntax.mkCharLit c.getChar).raw
  | _ => Lean.Macro.throwUnsupported

@[expose] def nativeCharacterEcho : Char := charEcho% 'λ'
example : nativeCharacterEcho = 'λ' := rfl
