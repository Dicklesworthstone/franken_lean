module
prelude
public import Init
public section

@[noinline] def helperContextRef : Lean.MacroM Lean.Syntax := do
  let ctx ← read
  pure ctx.ref

@[noinline] def forwardedContextMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax := do
  let chosen ← helperContextRef
  pure (.node .none (Lean.Name.mkStr1 "forwarded") #[chosen, stx])

