module
prelude
public import Init.Prelude
public import Init.Data.Repr
public meta import Init.Syntax
public meta import Init.Meta.Defs
public meta import Lean.Syntax

open Lean
public section

def syntaxMethodRootValue : Nat := 17

-- The observations are compiled user code. The Syntax operations themselves
-- must resolve to the native Mirror, with the pin's actual runtime telescopes.
@[noinline] meta def syntaxHasSynthetic (stx : Syntax) (start stop : Nat)
    (canonical : Bool) : Bool :=
  match stx.getHeadInfo with
  | .synthetic ⟨first⟩ ⟨last⟩ actual =>
    first == start && last == stop && actual == canonical
  | _ => false

@[noinline] meta def syntaxHasNoInfo (stx : Syntax) : Bool :=
  match stx.getHeadInfo with
  | .none => true
  | _ => false

@[noinline] meta def syntaxSameSubstring : Substring.Raw → Substring.Raw → Bool
  | ⟨text, ⟨start⟩, ⟨stop⟩⟩, ⟨other, ⟨otherStart⟩, ⟨otherStop⟩⟩ =>
    text == other && start == otherStart && stop == otherStop

@[noinline] meta def syntaxSameOriginal (left right : SourceInfo) : Bool :=
  match left, right with
  | .original leading ⟨start⟩ trailing ⟨stop⟩,
      .original otherLeading ⟨otherStart⟩ otherTrailing ⟨otherStop⟩ =>
    syntaxSameSubstring leading otherLeading && start == otherStart &&
      syntaxSameSubstring trailing otherTrailing && stop == otherStop
  | _, _ => false

syntax (name := syntaxAtomsKind) "syntaxAtoms!" term:max : term

@[macro syntaxAtomsKind]
meta def syntaxAtoms : Macro := fun stx => do
  let atom := Syntax.atom (.synthetic ⟨5⟩ ⟨12⟩ true) "before"
  let updated := atom.setAtomVal "after"
  let identifier ← `(Nat)
  let sameIdentifier := identifier.raw.setAtomVal "discarded"
  let sameNode := stx.setAtomVal "discarded"
  let sameMissing := Syntax.missing.setAtomVal "discarded"
  if atom.isAtom && atom.getAtomVal == "before" &&
      updated.isAtom && updated.getAtomVal == "after" &&
      syntaxHasSynthetic updated 5 12 true &&
      !(identifier.raw.isAtom) && identifier.raw.getAtomVal == "" &&
      sameIdentifier.isIdent && sameIdentifier.getId == identifier.raw.getId &&
      !(stx.isAtom) && stx.getAtomVal == "" &&
      sameNode.isOfKind ``syntaxAtomsKind && sameNode.getNumArgs == 2 &&
      !(Syntax.missing.isAtom) && Syntax.missing.getAtomVal == "" &&
      sameMissing.isMissing then
    return sameNode.getArg 1
  else
    fun _ state => .error (.error stx "Syntax atom methods changed a token, alias, or non-atom") state

syntax (name := syntaxArgKind) "syntaxArg!" term:max term:max : term

@[macro syntaxArgKind]
meta def syntaxArg : Macro := fun stx => do
  let original := Syntax.setInfo (.synthetic ⟨8⟩ ⟨21⟩ false) stx
  let updated := original.setArg 1 (stx.getArg 2)
  -- Read both aliases after the update; in-place mutation of the shared
  -- child array would change the source program's mathematical result.
  let left : TSyntax `term := ⟨original.getArg 1⟩
  let right : TSyntax `term := ⟨updated.getArg 1⟩
  if updated.isOfKind ``syntaxArgKind && updated.getNumArgs == 3 &&
      syntaxHasSynthetic updated 8 21 false then
    return (← `(Nat.add $left $right)).raw
  else
    fun _ state => .error (.error stx "Syntax.setArg changed node kind or source info") state

syntax (name := syntaxArgsKind) "syntaxArgs!" term:max term:max : term

@[macro syntaxArgsKind]
meta def syntaxArgs : Macro := fun stx => do
  let original := Syntax.setInfo (.synthetic ⟨13⟩ ⟨34⟩ true) stx
  let updated := original.setArgs #[stx.getArg 0, stx.getArg 2]
  let left : TSyntax `term := ⟨original.getArg 1⟩
  let right : TSyntax `term := ⟨updated.getArg 1⟩
  if original.getNumArgs == 3 && updated.getNumArgs == 2 &&
      updated.isOfKind ``syntaxArgsKind && syntaxHasSynthetic updated 13 34 true then
    return (← `(Nat.add $left $right)).raw
  else
    fun _ state => .error (.error stx "Syntax.setArgs changed an alias, node kind, or source info") state

syntax (name := syntaxBoundsKind) "syntaxBounds!" term:max : term

@[macro syntaxBoundsKind]
meta def syntaxBounds : Macro := fun stx => do
  let unchanged := (stx.setArg 2 Syntax.missing).setArg 18446744073709551616 Syntax.missing
  let atom := Syntax.atom .none "retained"
  let sameAtom := (atom.setArgs #[Syntax.missing]).setArg 0 Syntax.missing
  let sameMissing := (Syntax.missing.setArgs #[atom]).setArg 0 atom
  let identifier ← `(Nat)
  let sameIdentifier := (identifier.raw.setArgs #[atom]).setArg 0 atom
  if unchanged.getNumArgs == 2 && unchanged.isOfKind ``syntaxBoundsKind &&
      sameAtom.isAtom && sameAtom.getAtomVal == "retained" && sameMissing.isMissing &&
      sameIdentifier.isIdent && sameIdentifier.getId == identifier.raw.getId then
    return unchanged.getArg 1
  else
    fun _ state => .error (.error stx "Syntax argument updates changed a non-node or out-of-bounds argument") state

syntax (name := syntaxInfoKind) "syntaxInfo!" term:max : term

@[macro syntaxInfoKind]
meta def syntaxInfo : Macro := fun stx => do
  let last := Syntax.atom (.synthetic ⟨3⟩ ⟨9⟩ true) "last"
  let empty := Syntax.node .none `empty #[]
  let skipped := Syntax.node .none `nested #[Syntax.missing, empty]
  let search := Syntax.node .none `outer #[Syntax.missing, skipped, last]
  -- An info-less leaf is a successful head: its .none must stop the walk.
  let stopsAtNone := Syntax.node .none `outer #[Syntax.atom .none "first", last]
  let stopsAtNode := Syntax.node (.synthetic ⟨4⟩ ⟨10⟩ false) `outer #[last]
  let unchangedMissing := Syntax.setInfo (.synthetic ⟨1⟩ ⟨2⟩ true) Syntax.missing
  let originalInfo := stx.getHeadInfo
  let movedOriginal := Syntax.setInfo originalInfo (stx.getArg 1)
  let updated := Syntax.setInfo (.synthetic ⟨20⟩ ⟨30⟩ true) (stx.getArg 1)
  if syntaxHasSynthetic search 3 9 true && syntaxHasNoInfo stopsAtNone &&
      syntaxHasSynthetic stopsAtNode 4 10 false && syntaxHasNoInfo empty &&
      syntaxHasNoInfo skipped && syntaxHasNoInfo Syntax.missing && unchangedMissing.isMissing &&
      syntaxSameOriginal movedOriginal.getHeadInfo originalInfo &&
      syntaxHasSynthetic updated 20 30 true then
    return updated
  else
    fun _ state => .error (.error stx "Syntax source information was changed or searched in the wrong order") state

syntax (name := syntaxRootKind) "syntaxRoot!" : term

@[macro syntaxRootKind]
meta def syntaxRoot : Macro := fun _ => do
  let quoted ← `(syntaxMethodRootValue)
  -- Replacing source information must retain the identifier's quotation
  -- hygiene and pre-resolved declaration even under a same-named local.
  return Syntax.setInfo .none quoted.raw
