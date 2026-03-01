/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Lean
import Mathlib.Tactic.Linter.TextBased
import Batteries.Data.Array.Merge
import Mathlib.Logic.Function.Basic
/-!

# Linting of module documentation

This file lints the module documentation for consistency.
It currently only checks module headings, and as such many improvements to this file could
be made.

-/

open Lean System Meta


/-!

## Checking headings

-/

structure DocLintError where
  msg : String
  file : FilePath

def getHeaddings (f : FilePath) : IO (Array String) := do
  let lines ← IO.FS.lines f
  return lines.filter (fun l ↦ l.trim.startsWith "#")

def getTableOfContents (f : FilePath) : IO (Array String) := do
  let lines := (← IO.FS.lines f).toList
  let tofC := ((lines.splitAt (lines.findIdx (fun l ↦ l.trim == "## iii. Table of contents")+1))).2
  let toc := (tofC.splitAt (tofC.findIdx (fun l ↦ l.trim == "## iv. References"))).1
  return toc.toArray

inductive Steps where
  | titleHead
  | overviewHead
  | keyResultsHead
  | tableOfContentsHead
  | referencesHead
  | otherHeadings
  | headingsNoFullStops
  | tableOfContentsCorrect
deriving DecidableEq

def Steps.toString : Steps → String
  | .titleHead => "Add a title heading starting with '# ' for the whole module."
  | .overviewHead => "Add an overview section '## i. Overview' after the title heading."
  | .keyResultsHead => "Add a key results section '## ii. Key results' after the overview section."
  | .tableOfContentsHead => "Add a table of contents section '## iii. Table of contents' after the key results section. This can be filled in later."
  | .referencesHead => "Add a references section '## iv. References' after the table of contents section."
  | .otherHeadings => "Add other headings for sections and subsections using e.g. '## A.', '### A.1.', '#### A.1.2' etc."
  | .headingsNoFullStops => "Ensure all headings do not end in a full stop."
  | .tableOfContentsCorrect => "Fix the table of contents to match the headings in the file."

def Steps.anyTrue (e  : Steps → Bool × String) : Bool :=
  (e .titleHead).1 || (e .overviewHead).1 || (e .keyResultsHead).1 ||
  (e .tableOfContentsHead).1 || (e .referencesHead).1 ||
  (e .otherHeadings).1 || (e .headingsNoFullStops).1 ||
  (e .tableOfContentsCorrect).1

def checkHeadings (f : FilePath) : IO (List DocLintError) := do
  let headings ← getHeaddings f
  let mut errors : Steps → Bool × String := fun _ ↦ (false, "")

  /- Step: titleHead. -/

  let title := headings[0]?
  let mut titleError := ""
  match title with
  | none =>
    titleError := "No title heading found"
  | some t =>
    if !(t.startsWith "# ") then
      titleError := s!"Title heading '{t}' does not start with '# '"
  if titleError ≠ "" then
    errors := Function.update errors .titleHead (true, titleError)

  /- Step: overviewHead -/

  let overview := headings[1]?
  let mut overviewError := ""
  match overview with
  | none =>
    overviewError := "  No overview heading found"
  | some o =>
    if o ≠  "## i. Overview" then
      overviewError := s!"  Overview heading '{o}' is not '## i. Overview'"
  if overviewError ≠ "" then
    errors := Function.update errors .overviewHead (true, overviewError)

  /- Step: keyResultsHead -/

  let keyResults := headings[2]?
  let mut keyResultsError := ""
  match keyResults with
  | none =>
    keyResultsError := "  No key results heading found"
  | some k =>
    if k ≠ "## ii. Key results" then
      keyResultsError := s!"  Key results heading '{k}' is not '## ii. Key results'"
  if keyResultsError ≠ "" then
    errors := Function.update errors .keyResultsHead (true, keyResultsError)

  /- Step: tableOfContentsHead -/
  let toc := headings[3]?
  let mut tocError := ""
  match toc with
  | none =>
    tocError := " No table of contents heading found"
  | some t =>
    if t ≠ "## iii. Table of contents" then
      tocError := s!"Table of contents heading '{t}' is not '## iii. Table of contents'"
  if tocError ≠ "" then
    errors := Function.update errors .tableOfContentsHead (true, tocError)

  /- Step: referencesHead -/
  let references := headings[4]?
  let mut referencesError := ""
  match references with
  | none =>
    referencesError := "  No references heading found"
  | some r =>
    if r ≠ "## iv. References" then
      referencesError := s!"  References heading '{r}' is not '## iv. References'"
  if referencesError ≠ "" then
    errors := Function.update errors .referencesHead (true, referencesError)
  /- Step: otherHeadings. -/
  let mut otherHeadingsError := ""
  let otherHeadings := headings.drop 5
  if otherHeadings.any (fun h ↦ h.startsWith "# ") then
    otherHeadingsError := otherHeadingsError ++ s!"  Other headings found with `# `: {otherHeadings.filter (fun h ↦ h.startsWith "# ")}"
  if otherHeadings = #[] then
    otherHeadingsError := otherHeadingsError ++ "  No other headings found"
  let otherHeaddingsSplit := otherHeadings.map (fun h ↦ (h.splitOn " ").take 2)
  /- Should be something like '[##, ###, ##]`. -/
  let levels := otherHeaddingsSplit.map (fun h ↦ h[0]!)
  /- levels should be something like '[##, ###, ##]`. -/
  let notJustHashes := levels.filter (fun l ↦ !(l.all (· == '#')))
  if notJustHashes.size ≠ 0 then
    otherHeadingsError := otherHeadingsError ++ s!"\n Malformed space: {notJustHashes}"
  /- Every section reference should end in a dot.  -/
  let levelsNoDot := otherHeaddingsSplit.filter (fun l ↦ !(l[1]!.endsWith "."))
  if levelsNoDot.size ≠ 0 then
    otherHeadingsError := otherHeadingsError ++ s!"\n Section references not ending in a dot: {levelsNoDot}"
  /- The number of dots should equal one less then the number of dashes e.g.
    ## A., ### A.1. etc. -/
  let badLevels := otherHeaddingsSplit.filter (fun l ↦ l[0]!.count '#' ≠ l[1]!.count '.' + 1 )
  if badLevels.size ≠ 0 then
    otherHeadingsError := otherHeadingsError ++ s!"\n Section references with the wrong number of hashes: {badLevels}"
  /- Duplicate tags -/
  if ¬ List.Nodup otherHeaddingsSplit.toList then
    let dups := otherHeaddingsSplit.toList.filter (fun x ↦ otherHeaddingsSplit.toList.count x > 1)
    otherHeadingsError := otherHeadingsError ++ s!"\n Duplicate section tags found {dups}"
  if otherHeadingsError ≠ "" then
    errors := Function.update errors .otherHeadings (true, otherHeadingsError)
  /- Step: headingsNoFullStops -/

  let mut headingsNoFullStopsError := ""
  let headingsWithFullStops := headings.filter (fun h ↦ h.trim.endsWith ".")
  if headingsWithFullStops.size ≠ 0 then
    headingsNoFullStopsError := s!"  Headings ending in a full stop found: {headingsWithFullStops}"
  if headingsNoFullStopsError ≠ "" then
    errors := Function.update errors .headingsNoFullStops (true, headingsNoFullStopsError)
  /- Table of contents check. -/
  let tocLines ← getTableOfContents f
  let mut tocCorrectError := ""
  let expectedLevel1 (n : ℕ) := (otherHeadings.filter (fun l ↦ l.count '#' ≤ n)).map fun l =>
    let l' := l
    let l' := l'.replace "#### "  "    - "
    let l' := l'.replace "### "  "  - "
    let l' := l'.replace "## "  "- "
    l'
  let tocLinesNoEmpty := tocLines.filter (fun l ↦ l.trim ≠ "")
  if tocLinesNoEmpty ≠ expectedLevel1 4 then
    tocCorrectError := s!"  Table of contents does not match headings. \n Given:
{String.intercalate "\n" tocLinesNoEmpty.toList}\n Expected:
{String.intercalate "\n" (expectedLevel1 4).toList}\nEnd of Error."
  if tocCorrectError ≠ "" then
    errors := Function.update errors .tableOfContentsCorrect (true, tocCorrectError)

  /-
  ## Formatting the error
  -/
  if Steps.anyTrue errors then
    let mut errormsg := "\n"
    let mut n := (1 : ℕ)
    for e in  [Steps.titleHead, .overviewHead, .keyResultsHead, .tableOfContentsHead,
      .referencesHead, .otherHeadings, .headingsNoFullStops, .tableOfContentsCorrect] do
      let (b, s) := errors e

      if b then
        errormsg := errormsg ++ "\x1b[33mStep " ++ toString n ++ ": " ++ Steps.toString e ++ "\x1b[0m\n" ++ s ++ "\n"
      else
        errormsg := errormsg ++ "\x1b[32mStep " ++ toString n ++ ": " ++ Steps.toString e ++ "\x1b[0m\n"
      n := n + 1
    return [{msg := errormsg, file := f}]
  else
    return []


/-- The array of modules not to be linted. -/
def noLintArray : IO (Array FilePath) := do
  let path := (mkFilePath ["scripts", "MetaPrograms", "module_doc_no_lint"]).addExtension "txt"
  let lines ← IO.FS.lines path
  return lines.map (fun l ↦ mkFilePath [l])

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
  let noLint ← noLintArray
  let modulesToCheck := filePaths.filter (fun p ↦ !noLint.contains p)
  let errors := (← modulesToCheck.mapM checkHeadings).toList.flatten
  /- Printing the errors -/
  for eM in errors do
    IO.println s!"\x1b[31mError: \x1b[0m {eM.file}: {eM.msg}"
  if errors.length > 0 then
    IO.println "\n"
    throw <| IO.userError s!"Errors found."
  else
    IO.println "\x1b[32mNo documentation style issues found.\x1b[0m"
  return 0
