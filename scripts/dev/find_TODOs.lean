/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Lean
import Batteries.Data.String.Matcher
import Mathlib.Data.Nat.Notation
/-!

# TODO finder

This program finds all instances of `/<!> TODO: ...` (without the `<>`) in Physlib files.

## Note

Parts of this file are adapted from `Mathlib.Tactic.Linter.TextBased`,
  authored by Michael Rothgang.

-/
open Lean System Meta

/-- Given a list of lines, outputs an error message and a line number. -/
def PhyslibTODOItem : Type := Array String → Array (String × ℕ)

/-- Checks if a . -/
def TODOFinder : PhyslibTODOItem := fun lines ↦ Id.run do
  let enumLines := (lines.toList.enumFrom 1)
  let todos := enumLines.filterMap (fun (lno1, l1) ↦
    if l1.startsWith "/-! TODO:"   then
      some ((l1.replace "/-! TODO: " "").replace "-/" "", lno1)
    else none)
  todos.toArray

structure TODOContext where
  /-- The underlying `message`. -/
  statement : String
  /-- The line number -/
  lineNumber : ℕ
  /-- The file path -/
  path : FilePath

def printTODO (todos : Array TODOContext) : IO Unit := do
  for e in todos do
    IO.println (s!"{e.path}:{e.lineNumber}: {e.statement}")

def filePathToGitPath (S : FilePath) (n : ℕ) : String :=
  "https://github.com/leanprover-community/physlib/blob/master/"++
  (S.toString.replace "." "/").replace "/lean" ".lean"
  ++ "#L" ++ toString n

def docTODO  (todos : Array TODOContext) : IO String := do
  let mut out := ""
  for e in todos do
    out := out ++ (s!" - [{e.statement}]("++ filePathToGitPath e.path e.lineNumber ++ ")\n")
  return out

def physlibLintFile (path : FilePath) : IO String := do
  let lines ← IO.FS.lines path
  let allOutput := (Array.map (fun lint ↦
    (Array.map (fun (e, n) ↦ TODOContext.mk e n path)) (lint lines)))
    #[TODOFinder]
  let errors := allOutput.flatten
  printTODO errors
  docTODO errors

def todoFileHeader : String := s!"
# TODO List

This is an automatically generated list of TODOs appearing as `/-! TODO:...` in Physlib.

Please feel free to contribute to the completion of these tasks.


"

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mods : Name :=  `Physlib
  let imp :  Import := {module := mods}
  let mFile ← findOLean imp.module
  unless (← mFile.pathExists) do
        throw <| IO.userError s!"object file '{mFile}' of module {imp.module} does not exist"
  let (physlibMod, _) ← readModuleData mFile
  let mut out :  String :=  ""
  for imp in physlibMod.imports do
    if imp.module == `Init then continue
    let filePath := (mkFilePath (imp.module.toString.split (· == '.'))).addExtension "lean"
    let l ← physlibLintFile filePath
    if l != "" then
      out := out ++ "\n### " ++ imp.module.toString ++ "\n"
      out := out ++ l
  let fileOut : System.FilePath := {toString := "./docs/TODOList.md"}
  /- Below here is concerned with writing out to the docs. -/
  if "mkFile" ∈ args then
    IO.println (s!"TODOList file made.")
    IO.FS.writeFile fileOut (todoFileHeader ++ out)
  return 0
