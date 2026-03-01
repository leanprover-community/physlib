/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Informal.Post
import Mathlib.Lean.CoreM
import PhysLean.Meta.Linters.Sorry
import PhysLean.Meta.Sorry
import Mathlib.Data.List.Defs
import Lean.DocString.Extension
import PhysLean.Meta.AllFilePaths
/-!

# Script to help checking spelling of results

This script collects all words in doc-strings of definitions, theorems and lemmas
in PhysLean, as well as module doc-strings, and compares them to a custom dictionary
of correctly spelled words. It then outputs all words which are not in the dictionary,
so that the user can either correct them or add them to the dictionary file.

This code makes no attempt to guess the correct spelling of words, it simply lists
all unknown words found.

-/

open Lean

/-- The strings appearing as documentation within PhysLean. -/
def moduleDocs : MetaM (Array String) := do
  let env ← getEnv
  let allModules ← allPhysLeanModules
  let modDocs := allModules.filterMap fun c =>
    Lean.getModuleDoc? env c
  let modDocs := modDocs.flatten
  let modDocs := modDocs.map fun d => d.doc
  return modDocs

/-- All the words in either module doc-strings or doc-strings of definitions, theorems
  and lemmas. -/
def allWords : MetaM (Array String) := do
  let allConstants ← PhysLean.allUserConsts
  let allModuleDocs ← moduleDocs
  let allDocStrings ← allConstants.mapM fun c => Lean.Name.getDocString c.name
  let allDocStrings := allDocStrings ++ allModuleDocs
  let allDocStrings := allDocStrings.filter (fun x => x ≠ "")
  let allList := allDocStrings.flatMap (fun s =>
      (s.split (fun c => c.isWhitespace || ".,?!:;()[]{}<>\"'".contains c)).toArray)
  let allList := (allList.filter (fun w => w ≠ "" ∧ w ≠ " ")).toList.dedup.toArray

  let allList := allList.qsort (fun a b => a.toLower < b.toLower)
  let allList := allList.filter (fun s => s.all Char.isAlpha)

  return allList

/-- The custom dictionary of correctly spelled words. -/
def dictionary : MetaM (Array String) := do
  let path : System.FilePath := "./scripts/MetaPrograms/spellingWords.txt"
  let lines ← IO.FS.lines path
  return lines.map (fun s => s.toLower)

unsafe def main (_ : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  println! "Checking spelling."
  let env ← importModules (loadExts := true) #[`PhysLean] {} 0
  let fileName := ""
  let options : Options := {}
  let ctx : Core.Context := {fileName, options, fileMap := default }
  let state := {env}
  let (array, _) ← (Lean.Core.CoreM.toIO · ctx state) do (allWords).run'
  let (dict, _) ← (Lean.Core.CoreM.toIO · ctx state) do (dictionary).run'
  let misspelled := array.filter fun w => ¬ (w.toLower) ∈ dict
  println! "The following words are not in the dictionary, please correct or add them to
    the spellingWords.txt file:"
  println! "{misspelled}"
