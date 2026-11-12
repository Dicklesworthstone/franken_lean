module
prelude
public import Init
public import Lean.Syntax
public section

-- Ordinary user MacroM code calls the native sequence builders. The typed
-- ofElems API erases to SepArray.ofElems; push also preserves arbitrary
-- caller-constructed even and odd separated arrays.
@[noinline] def untypedSequenceMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  let parts : Lean.Syntax.SepArray "," := .ofElems stx.getArgs
  pure (Lean.mkNullNode parts.elemsAndSeps)

@[noinline] def emptySeparatorMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  let parts : Lean.Syntax.SepArray "" := .ofElems stx.getArgs
  pure (Lean.mkNullNode parts.elemsAndSeps)

@[noinline] def typedSequenceMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  let parts : Lean.Syntax.TSepArray `term "," := .ofElems (Lean.TSyntaxArray.mk stx.getArgs)
  pure (Lean.mkNullNode parts.elemsAndSeps)

@[noinline] def appendSequenceMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  let parts : Lean.Syntax.TSepArray `term "," := ⟨stx.getArgs⟩
  pure (Lean.mkNullNode (parts.push ⟨Lean.mkAtom "tail"⟩).elemsAndSeps)

@[noinline] def appendEmptySeparatorMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  let parts : Lean.Syntax.TSepArray `term "" := ⟨stx.getArgs⟩
  pure (Lean.mkNullNode (parts.push ⟨Lean.mkAtom "tail"⟩).elemsAndSeps)

syntax (name := firstSequence) "firstSequence%[" term,* "]" : term
@[macro firstSequence] meta def expandFirstSequence : Lean.Macro
  | `(firstSequence%[$items:term,*]) =>
    let completed := items.push ⟨(Lean.Syntax.mkNumLit "42").raw⟩
    pure (Lean.mkNullNode completed.getElems.raw)[0]
  | _ => Lean.Macro.throwUnsupported

-- Real registered quotation expansion is also exercised while the pin emits
-- the user module, independently of the native invocation test.
@[expose] def nativeSequenceEmpty : Nat := firstSequence%[]
@[expose] def nativeSequenceFirst : Nat := firstSequence%[7, 11, 13]
example : nativeSequenceEmpty = 42 := rfl
example : nativeSequenceFirst = 7 := rfl
