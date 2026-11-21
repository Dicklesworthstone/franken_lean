/-
Reference-only Tribunal driver for kernel unfold-count differentials
(bead `fln-kernel-unfold-differential-tfvw`).

Given a module name and a declaration name, loads the module's `.olean`
parts from `LEAN_PATH`, imports its dependencies, replays every prerequisite
declaration in the module with diagnostics off, then enables
`Kernel.Diagnostics` (`enableDiag true`, `resetDiag`) immediately before
calling `addDeclCore` on the target declaration (or its mutual/inductive
block). Prints header metadata (`# key\tvalue`) followed by lexicographically
sorted `name\tcount` rows from `Kernel.Diagnostics.unfoldCounter`.

Never a FrankenLean runtime component: invoked only through the pinned
Reference `lean` binary inside the Tribunal (D8).
-/
import Lean.CoreM
import Lean.Replay

open Lean

namespace UnfoldCounts

structure Context where
  newConstants : Std.HashMap Name ConstantInfo

structure State where
  env : Kernel.Environment
  remaining : NameSet := {}
  pending : NameSet := {}

abbrev M := ReaderT Context <| StateRefT State IO

def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

def throwKernelException (ex : Kernel.Exception) : M Unit := do
  throw <| .userError <| (← ex.toMessageData {} |>.toString)

def addDeclRaw (d : Declaration) : M Unit := do
  match (← get).env.addDeclCore 0 d (cancelTk? := none) with
  | .ok env => modify fun s => { s with env := env }
  | .error ex => throwKernelException ex

partial def buildDeclaration (name : Name) : M (Declaration × List Name) := do
  let some ci := (← read).newConstants[name]?
    | throw <| .userError s!"declaration '{name}' not found in module"
  match ci with
  | .defnInfo info =>
    if info.all.length > 1 then
      let mut defs : List DefinitionVal := []
      for n in info.all do
        let some (.defnInfo d) := (← read).newConstants[n]?
          | throw <| .userError s!"mutual definition member '{n}' missing"
        defs := defs ++ [d]
      return (Declaration.mutualDefnDecl defs, info.all)
    else
      return (Declaration.defnDecl info, [name])
  | .thmInfo info =>
    return (Declaration.thmDecl info, [name])
  | .axiomInfo info =>
    return (Declaration.axiomDecl info, [name])
  | .opaqueInfo info =>
    return (Declaration.opaqueDecl info, [name])
  | .inductInfo info =>
    let lparams := info.levelParams
    let nparams := info.numParams
    let all ← info.all.mapM fun n => do
      let some c := (← read).newConstants[n]?
        | throw <| .userError s!"inductive member '{n}' missing"
      pure c
    let ctorInfo ← all.mapM fun c => do
      let ctors ← c.inductiveVal!.ctors.mapM fun cn => do
        let some cc := (← read).newConstants[cn]?
          | throw <| .userError s!"constructor '{cn}' missing"
        pure cc
      pure (c, ctors)
    let types : List InductiveType := ctorInfo.map fun ⟨c, ctors⟩ =>
      { name := c.name
        type := c.type
        ctors := ctors.map fun cc => { name := cc.name, type := cc.type } }
    return (Declaration.inductDecl lparams nparams types info.isUnsafe, info.all)
  | .quotInfo _ =>
    return (Declaration.quotDecl, [name])
  | .ctorInfo info =>
    buildDeclaration info.induct
  | .recInfo info =>
    match info.all with
    | ind :: _ => buildDeclaration ind
    | [] => throw <| .userError s!"recursor '{name}' has no inductive family"

partial def usedConstantsOfUnit (name : Name) : M NameSet := do
  let some ci := (← read).newConstants[name]?
    | throw <| .userError s!"declaration '{name}' not found in module"
  match ci with
  | .defnInfo info =>
    if info.all.length > 1 then
      let mut acc : NameSet := {}
      for n in info.all do
        if let some c := (← read).newConstants[n]? then
          for u in c.getUsedConstantsAsSet do
            if !info.all.contains u then
              acc := acc.insert u
      return acc
    else
      return ci.getUsedConstantsAsSet.erase name
  | .inductInfo info =>
    let mut acc : NameSet := {}
    let mut selfNames : NameSet := {}
    for n in info.all do
      selfNames := selfNames.insert n
      if let some (.inductInfo ind) := (← read).newConstants[n]? then
        for cn in ind.ctors do
          selfNames := selfNames.insert cn
    for n in info.all do
      if let some (.inductInfo ind) := (← read).newConstants[n]? then
        for u in ind.toConstantVal.type.getUsedConstants do
          if !selfNames.contains u then
            acc := acc.insert u
        for cn in ind.ctors do
          if let some cc := (← read).newConstants[cn]? then
            for u in cc.getUsedConstantsAsSet do
              if !selfNames.contains u then
                acc := acc.insert u
    return acc
  | .ctorInfo info => usedConstantsOfUnit info.induct
  | .recInfo info =>
    match info.all with
    | ind :: _ => usedConstantsOfUnit ind
    | [] => return {}
  | .quotInfo _ => return ({} : NameSet).insert `Eq
  | _ => return ci.getUsedConstantsAsSet.erase name

mutual
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants[name]? | return
    match ci with
    | .ctorInfo info =>
      modify fun s => { s with pending := s.pending.erase name }
      replayConstant info.induct
      return
    | .recInfo info =>
      modify fun s => { s with pending := s.pending.erase name }
      if let ind :: _ := info.all then
        replayConstant ind
      return
    | _ => pure ()
    let deps ← usedConstantsOfUnit name
    replayConstants deps
    if (← get).pending.contains name then
      match ci with
      | .thmInfo info =>
        if let some (.thmInfo info') := (← get).env.find? ci.name then
          if info.name == info'.name &&
             info.type == info'.type &&
             info.levelParams == info'.levelParams &&
             info.all == info'.all then
            modify fun s => { s with pending := s.pending.erase name }
            return
      | _ => pure ()
      let (decl, members) ← buildDeclaration name
      for m in members do
        modify fun s =>
          { s with remaining := s.remaining.erase m, pending := s.pending.erase m }
      addDeclRaw decl

partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do
    replayConstant n
end

unsafe def runForDeclaration (module : Name) (declName : Name) : IO Unit := do
  let moduleFile ← findOLean module
  unless (← moduleFile.pathExists) do
    throw <| IO.userError s!"object file '{moduleFile}' of module {module} does not exist"

  let mut partFiles := #[moduleFile]
  let serverFile := OLeanLevel.server.adjustFileName moduleFile
  if (← serverFile.pathExists) then
    partFiles := partFiles.push serverFile
    let privateFile := OLeanLevel.private.adjustFileName moduleFile
    if (← privateFile.pathExists) then
      partFiles := partFiles.push privateFile

  let parts ← readModuleDataParts partFiles
  if h : parts.size = 0 then
    throw <| IO.userError "failed to read module data"
  else
    let (moduleData, _) := parts[0]
    let (_, importState) ← importModulesCore moduleData.imports |>.run
    let environment ←
      finalizeImport importState moduleData.imports {} 0 false false (isModule := true)
    let mut newConstants : Std.HashMap Name ConstantInfo := {}
    let mut remaining : NameSet := {}
    for name in parts[parts.size - 1].1.constNames,
        constantInfo in parts[parts.size - 1].1.constants do
      newConstants := newConstants.insert name constantInfo
      remaining := remaining.insert name

    unless newConstants.contains declName do
      throw <| IO.userError s!"declaration '{declName}' not found in module '{module}'"

    let ctx : Context := { newConstants }
    let initState : State := { env := environment.toKernelEnv, remaining }
    let ((decl, _members), st) ← (do
      let deps ← usedConstantsOfUnit declName
      replayConstants deps
      buildDeclaration declName
    ).run ctx |>.run initState

    let envBefore := st.env.enableDiag true |>.resetDiag
    let t0 ← IO.monoNanosNow
    match envBefore.addDeclCore 0 decl (cancelTk? := none) with
    | .ok envAfter =>
      let elapsedNs := (← IO.monoNanosNow) - t0
      let diag := Kernel.Environment.getDiagnostics envAfter
      let rows := diag.unfoldCounter.foldl (init := #[]) fun acc n c =>
        acc.push (n.toString, c)
      let sorted := rows.qsort fun a b => a.1 < b.1
      IO.println s!"# module\t{module}"
      IO.println s!"# declaration\t{declName}"
      IO.println "# verdict\taccepted"
      IO.println s!"# wall_ns\t{elapsedNs}"
      IO.println s!"# entries\t{sorted.size}"
      for (n, c) in sorted do
        IO.println s!"{n}\t{c}"
    | .error ex =>
      let msg ← ex.toMessageData {} |>.toString
      throw <| IO.userError s!"kernel rejected '{declName}' in '{module}': {msg}"

end UnfoldCounts

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  match args with
  | [moduleArg, declArg] =>
    let module := moduleArg.toName
    let declName := declArg.toName
    if module.isAnonymous then
      throw <| IO.userError s!"invalid module name: {moduleArg}"
    if declName.isAnonymous then
      throw <| IO.userError s!"invalid declaration name: {declArg}"
    UnfoldCounts.runForDeclaration module declName
    return 0
  | _ =>
    throw <| IO.userError "usage: lean --run scripts/tribunal/unfold_counts.lean <Module> <Declaration>"
