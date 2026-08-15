/-
Copyright (c) 2023 Kim Morrison, Sebastian Ullrich.
Released under Apache 2.0 license as described in the Lean 4 repository.

Reference-only Tribunal driver for checking an exact list of modules.  The
pinned `leanchecker` executable treats every positional argument as a namespace
prefix and eagerly starts one task for every matching module.  That interface
cannot check a declaration-bearing namespace module independently of all of its
descendants.  This driver deliberately calls the same `Lean.Replay` operation
for exact module names in bounded windows.

It is never a FrankenLean runtime component.  `kernel_replay.rs` invokes it only
through the pinned Reference binary, as a differential oracle under D8.
-/
import Lean.CoreM
import Lean.Replay

open Lean

unsafe def replayExactModule (module : Name) : IO Unit := do
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
    let (_, state) ← importModulesCore moduleData.imports |>.run
    let environment ←
      finalizeImport state moduleData.imports {} 0 false false (isModule := true)
    let mut newConstants := {}
    for name in parts[parts.size - 1].1.constNames,
        constantInfo in parts[parts.size - 1].1.constants do
      newConstants := newConstants.insert name constantInfo
    let checked ← environment.replay newConstants
    checked.freeRegions

def exactWindowSize : Nat := 8

unsafe def replayExactWindow (args : List String) : IO Unit := do
  let mut tasks := #[]
  for arg in args do
    let module := arg.toName
    if module.isAnonymous then
      throw <| IO.userError s!"Could not resolve module: {arg}"
    tasks := tasks.push (module, ← IO.asTask (replayExactModule module))
  for (module, task) in tasks do
    if let .error error := task.get then
      IO.eprintln s!"exact_leanchecker found a problem in {module}"
      throw error
    IO.println s!"replayed exact module {module}"

unsafe def replayExactWindows (args : List String) : IO Unit := do
  if args.isEmpty then
    return
  replayExactWindow (args.take exactWindowSize)
  replayExactWindows (args.drop exactWindowSize)

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  if args.isEmpty then
    throw <| IO.userError "exact_leanchecker requires at least one module"
  replayExactWindows args
  return 0
