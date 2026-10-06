/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Batteries.Lean.HashSet
import Lean
/-!

# Check file imports

This file checks that the imports in each library root file (`Physlib.lean` and
`QuantumInfo.lean`) are sorted and complete. `PhyslibAlpha.lean` has its own check,
`alphaFileImports`.

It can be run from the terminal using
`lake exe check_file_imports`.

## Note on adaptation

The functions

`addModulesIn`, `expectedPhyslibImports`, and `checkMissingImports`

are adapted from `batteries.scripts.check_imports.lean` authored by Joe Hendrix.

-/
open Lean System Meta

/--  Recursively finds files in directory. -/
partial def addModulesIn (recurse : Bool) (prev : Array Name) (root : Name := .anonymous)
    (path : FilePath) : IO (Array Name) := do
  let mut r := prev
  for entry in ← path.readDir do
    if ← entry.path.isDir then
      if recurse then
        r ← addModulesIn recurse r (root.mkStr entry.fileName) entry.path
    else
      -- Only `.lean` files correspond to modules; skip any other files (e.g. an
      -- `API-map.yaml` sitting at the top of an API directory).
      if entry.path.extension == some "lean" then
        let .some mod := FilePath.fileStem entry.fileName
          | continue
        r := r.push (root.mkStr mod)
  pure r

/-- Compute imports expected by `<lib>.lean` by looking at the file structure under `<lib>/`. -/
def expectedImports (lib : Name) : IO (Array Name) := do
  let mut needed := #[]
  for top in ← FilePath.readDir lib.toString do
      let rootname := FilePath.withExtension top.fileName ""
      let root :=  lib.mkStr rootname.toString
      if ← top.path.isDir then
        needed ← addModulesIn (recurse := true) needed (root := root) top.path
      else if top.path.extension == some "lean" then
        needed := needed.push root
  pure needed

def listDif : (a: List String) → (b : List String) → (List String × List String)
  | [], [] => ([], [])
  | a :: as, [] => (a :: as, [])
  | [], b :: bs => ([], b :: bs)
  | a :: as, b :: bs =>
    if a = b then listDif as bs
    else (a :: (listDif as bs).1, b :: (listDif as bs).2)

/-- Checks whether an array `imports` is sorted after `Init` is removed.  -/
def arrayImportSorted (imports : Array Import) : IO Bool :=  do
  let X := (imports.map (fun x => x.module.toString)).filter (fun x => x != "Init")
  let mut warned := false
  if ! X = X.qsort (· < ·) then
    IO.print s!"Import file is not sorted. \n"
    let ldif := listDif X.toList (X.qsort (· < ·)).toList
    let lzip := List.zip ldif.1 ldif.2
    let lstring := String.intercalate "\n" (lzip.map (fun x => s!"{x.1} > {x.2}"))
    println! lstring
    warned := true
  pure warned

/-- Checks every file in `reqImports` is imported into `modData`
  return true if this is NOT the case. -/
def checkMissingImports (lib : Name) (modData : ModuleData) (reqImports : Array Name) :
    IO Bool := do
  let names : Std.HashSet Name := Std.HashSet.ofArray (modData.imports.map (·.module))
  let mut warned := false
  let nameArray := reqImports.filterMap (
    fun req => if !names.contains req then
      some req
    else
      none)
  if nameArray.size ≠ 0  then
    let nameArraySort := nameArray.qsort (·.toString < ·.toString)
    IO.print s!"Files are not imported add the following to the `{lib}` file: \n"
    for name in nameArraySort do
      IO.print s!"import {name}\n"
    warned := true
  pure warned

/-- Check one library root `<lib>.lean` against the files under `<lib>/`.
  Returns `true` if the root is unsorted or has missing imports. -/
def checkLib (lib : Name) : IO Bool := do
  let imp : Import := {module := lib}
  let mFile ← findOLean imp.module
  unless (← mFile.pathExists) do
        throw <| IO.userError s!"object file '{mFile}' of module {imp.module} does not exist"
  let (libMod, _) ← readModuleData mFile
  let eImports ← expectedImports lib
  let sortedWarned ← arrayImportSorted libMod.imports
  let warned ← checkMissingImports lib libMod eImports
  if (warned ∨ sortedWarned) then
    IO.println s!"\x1b[31mThe {lib}.lean file is not sorted, or has missing imports.\x1b[0m"
  else
    IO.println s!"\x1b[32mAll files are imported correctly into {lib}.lean.\x1b[0m"
  pure (warned ∨ sortedWarned)

/-- The library roots this check covers. `PhyslibAlpha` has its own check,
  `alphaFileImports`. -/
def libraries : List Name := [`Physlib, `QuantumInfo]

def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut failed := false
  for lib in libraries do
    failed := (← checkLib lib) || failed
  if failed then
    throw <| IO.userError s!"\x1b[31mA library root file is not sorted, or has missing imports.\x1b[0m"
  pure 0
