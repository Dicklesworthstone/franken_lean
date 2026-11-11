module
prelude
public import Init
public import Lean.Syntax
public section

-- These are ordinary user MacroM declarations. Imported Syntax services are
-- linked to native implementations; no toolchain IR is supplied by the test.
@[noinline] def immediateInfoMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure <| match stx.getInfo? with
    | some info => .atom info "info"
    | none => .missing

@[noinline] def headInfoMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure <| match stx.getHeadInfo? with
    | some info => .atom info "info"
    | none => .missing

@[noinline] def rangeMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure <| match stx.getRange? with
    | some range => .atom (.synthetic range.start range.stop true) "range"
    | none => .missing

@[noinline] def canonicalRangeMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure <| match stx.getRange? (canonicalOnly := true) with
    | some range => .atom (.synthetic range.start range.stop true) "range"
    | none => .missing

@[noinline] def hasMissingMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure (Lean.mkAtom (if stx.hasMissing then "true" else "false"))

@[noinline] def reprintMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure <| match stx.reprint with
    | some text => Lean.mkAtom text
    | none => .missing
