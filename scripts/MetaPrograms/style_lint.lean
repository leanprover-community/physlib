/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Lean
import Mathlib.Tactic.Linter.TextBased
import Batteries.Data.Array.Merge
/-!

# PhysLean style linter

A number of linters on PhysLean to enforce a consistent style.

There are currently not enforced at the GitHub action level.

## Note

Parts of this file are adapted from `Mathlib.Tactic.Linter.TextBased`,
  authored by Michael Rothgang.

## TODO

Some of the linters here can be replaced by regex.

-/
open Lean System Meta

/-- Given a list of lines, outputs an error message and a line number. -/
def PhysLeanTextLinter : Type := Array String → Array (String × ℕ × ℕ)

/-- Checks if there are two consecutive empty lines. -/
def doubleEmptyLineLinter : PhysLeanTextLinter := fun lines ↦ Id.run do
  let enumLines := (lines.toList.zipIdx 1)
  let pairLines := List.zip enumLines (List.tail! enumLines)
  let errors := pairLines.filterMap (fun ((l1, lno1), l2, _) ↦
    if l1.length == 0 && l2.length == 0  then
      some (s!" Double empty line. ", lno1, 1)
    else none)
  errors.toArray

/-- Checks if there is a double space in the line, which is not at the start. -/
def doubleSpaceLinter : PhysLeanTextLinter := fun lines ↦ Id.run do
  let enumLines := (lines.toList.zipIdx 1)
  let errors := enumLines.filterMap (fun (l, lno) ↦
    if String.containsSubstr l.trimLeft "  " then
      let k := (Substring.findAllSubstr l "  ").toList.getLast?
      let col := match k with
        | none => 1
        | some k => String.offsetOfPos l k.stopPos
      some (s!" Non-initial double space in line.", lno, col)
    else none)
  errors.toArray

def longLineLinter : PhysLeanTextLinter := fun lines ↦ Id.run do
  let enumLines := (lines.toList.zipIdx 1)
  let errors := enumLines.filterMap (fun (l, lno) ↦
    if l.length > 100 ∧ ¬ String.containsSubstr l "http" then
      some (s!" Line is too long.", lno, 100)
    else none)
  errors.toArray

/-- Substring linter. -/
def substringLinter (s : String) : PhysLeanTextLinter := fun lines ↦ Id.run do
  let enumLines := (lines.toList.zipIdx 1)
  let errors := enumLines.filterMap (fun (l, lno) ↦
    if String.containsSubstr l s then
      let k := (Substring.findAllSubstr l s).toList.getLast?
      let col := match k with
        | none => 1
        | some k => String.offsetOfPos l k.stopPos
      some (s!" Found instance of substring `{s}`.", lno, col)
    else none)
  errors.toArray

def endLineLinter (s : String) : PhysLeanTextLinter := fun lines ↦ Id.run do
  let enumLines := (lines.toList.zipIdx 1)
  let errors := enumLines.filterMap (fun (l, lno) ↦
    if l.endsWith s then
      some (s!" Line ends with `{s}`.", lno, l.length)
    else none)
  errors.toArray

/-- Number of space at new line must be even. -/
def numInitialSpacesEven : PhysLeanTextLinter := fun lines ↦ Id.run do
  let enumLines := (lines.toList.zipIdx 1)
  let errors := enumLines.filterMap (fun (l, lno) ↦
    let numSpaces := (l.takeWhile (· == ' ')).length
    if numSpaces % 2 != 0 then
      some (s!"Number of initial spaces is not even.", lno, 1)
    else none)
  errors.toArray

structure PhysLeanErrorContext where
  /-- The underlying `message`. -/
  error : String
  /-- The line number -/
  lineNumber : ℕ
  /-- The column number -/
  columnNumber : ℕ
  /-- The file path -/
  path : FilePath

def printErrors (errors : Array PhysLeanErrorContext) : IO Unit := do
  for e in errors do
    IO.println (s!"error: {e.path}:{e.lineNumber}:{e.columnNumber}: {e.error}")

def hepLeanLintFile (path : FilePath) : IO (Array PhysLeanErrorContext) := do
  let lines ← IO.FS.lines path
  let allOutput := (Array.map (fun lint ↦
    (Array.map (fun (e, n, c) ↦ PhysLeanErrorContext.mk e n c path)) (lint lines)))
    #[doubleEmptyLineLinter, doubleSpaceLinter, numInitialSpacesEven, longLineLinter,
    substringLinter ".-/", substringLinter " )",
    substringLinter "( ", substringLinter "=by", substringLinter "  def ",
    substringLinter "/-- We ", substringLinter "[ ", substringLinter " ]", substringLinter " ,",
    substringLinter "⟨ ", substringLinter " ⟩",  substringLinter "):",  substringLinter "(_)",
    endLineLinter "("]
  let errors := allOutput.flatten
  return errors

def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mods : Name :=  `PhysLean
  let imp : Import := {module := mods}
  let mFile ← findOLean imp.module
  unless (← mFile.pathExists) do
        throw <| IO.userError s!"object file '{mFile}' of module {imp.module} does not exist"
  let (hepLeanMod, _) ← readModuleData mFile
  let filePaths := hepLeanMod.imports.filterMap (fun imp ↦
    if imp.module == `Init then
      none
    else
      some ((mkFilePath (imp.module.toString.splitToList (· == '.'))).addExtension "lean"))
  let errors := (← filePaths.mapM hepLeanLintFile).flatten
  let errorMessagesPresent := (errors.map (fun e => e.error)).sortDedup
  for eM in errorMessagesPresent do
    IO.println s!"\n\n\x1b[31mError: {eM}\x1b[0m"
    for e in errors do
      if e.error == eM then
        IO.println s!"{e.path}:{e.lineNumber}:{e.columnNumber}: {e.error}"
  if errors.size > 0 then
    throw <| IO.userError s!"Errors found."
  else
    IO.println "\x1b[32mNo linting issues found.\x1b[0m"
  return 0
