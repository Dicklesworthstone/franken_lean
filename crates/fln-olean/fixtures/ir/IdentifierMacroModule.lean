module
prelude
public import Init
public section

-- These public helpers must resolve to native Mirror rows when this user IR is
-- run by Golem. The caller's Name, SourceInfo and MacroM state are observable.
@[noinline] def identifierMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure (Lean.mkIdent stx.getId)

@[noinline] def identifierFromMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure (Lean.mkIdentFrom stx stx.getId false)

@[noinline] def canonicalIdentifierFromMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure (Lean.mkIdentFrom stx stx.getId true)

@[noinline] def constantIdentifierMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure (Lean.mkCIdent stx.getId)

@[noinline] def constantIdentifierFromMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure (Lean.mkCIdentFrom stx stx.getId false)

@[noinline] def canonicalConstantIdentifierFromMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure (Lean.mkCIdentFrom stx stx.getId true)
