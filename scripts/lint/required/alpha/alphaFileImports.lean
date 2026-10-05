import Lean
import Physlib.Meta.AllFilePaths
import Std.Data.HashSet


/-!
Copyright (c) 2026 Fergus Munro. All rights reserved.
Released under Apache 2.0 license.
Authors: Fergus Munro
-/

open Lean
open Std
open System

def extractModuleNameFromFilePath (path : FilePath) : String := 
  ".".intercalate ((path.withExtension "").components.drop 1)

def extractModuleNameFromImport (importString : String) : String := 
  let rec findAfterImport : List String → String
  | "import" :: x :: _ => x
  | _ :: xs            => findAfterImport xs
  | []                 => ""

  findAfterImport ((importString.split Char.isWhitespace).toList.map toString)

def checkAllFilesImported (directory : String) (mainFilePath : String) : (IO Bool) := do
  let modules : HashSet String := HashSet.ofArray $ (← getFilePaths directory).map extractModuleNameFromFilePath 
  let importedModules := HashSet.ofArray $ ((← IO.FS.lines mainFilePath).filter 
    (·.contains "import")).map extractModuleNameFromImport 
  let diff := modules \ importedModules
  if diff.size > 0 
    then do 
      IO.println s!"Error: The following .lean files are not imported in {mainFilePath}:"
      for module_name in diff do
        IO.println s!"  - public import {module_name}"
      return False 
    else do
      IO.println s!"✓ All {modules.size} .lean files in {directory} are imported in {mainFilePath}"
      return True

unsafe def main (args : List String) : IO Unit := do
  let (dir, file) := match args with
    | d :: f :: [] => (d, f)
    | _ => ("./PhyslibAlpha", "./PhyslibAlpha.lean")
  let success ← checkAllFilesImported dir file
  if !success then
    IO.Process.exit 1

