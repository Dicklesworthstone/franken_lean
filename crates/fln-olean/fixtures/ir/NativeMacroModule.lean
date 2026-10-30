module
prelude
public import Init
public section

-- A real registered macro with executable control flow, not a quoted template.
macro (name := userChoose) "chooseTerm%" a:term "," b:term : term => do
  if a.raw.getNumArgs == 0 then pure b else pure a

@[noinline] def scopedMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  Lean.Macro.withFreshMacroScope (pure stx)

@[noinline] def errorMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  throw (Lean.Macro.Exception.error stx "λ\x00error")

-- Demanding an environment method stays outside the first native slice.
@[noinline] def namespaceMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax := do
  let _ ← Lean.Macro.getCurrNamespace
  pure stx

-- These read the caller's actual native context. No environment method runs.
macro (name := contextChoose) "contextTerm%" a:term "," b:term : term => do
  let ctx ← read
  if ctx.currMacroScope == 17 then pure a else pure b

@[noinline] def contextFields (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax := do
  let ctx ← read
  if ctx.currRecDepth == ctx.maxRecDepth then
    pure ctx.ref
  else
    pure (.node .none ctx.quotContext #[ctx.ref, stx])


-- Structural inspection must use the native Mirror, including pseudo-kinds and
-- hygienic identifier names. These functions deliberately need no environment.
@[noinline] def inspectSyntaxMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax := do
  if stx.isMissing then
    pure (.node .none stx.getKind stx.getArgs)
  else if stx.isIdent then
    pure (.node .none stx.getId #[stx])
  else
    pure (.node .none stx.getKind stx.getArgs)

@[noinline] def idSyntaxMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure (.node .none stx.getId stx.getArgs)

@[noinline] def replaceSyntaxKindMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure (stx.setKind (Lean.Name.mkStr1 "renamed"))
