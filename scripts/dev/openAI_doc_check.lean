/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Batteries.Lean.IO.Process
import Lean
import Lean.Parser
import Lean.Data.Json
import Mathlib.Lean.CoreM
import LLM.GPT.Json
import LLM.GPT.API
/-!

# Physlib OpenAI doc check

This file uses the openAI API to check the doc strings of definitions and theorems in a
Lean 4 file.

This file depends on `https://github.com/leanprover-community/llm` being imported.
This is not currently done by default.

-/
open Lean
open LLM
open System Meta

def getDocString (constName : Array ConstantInfo) : MetaM String := do
  let env ← getEnv
  let mut docString := ""
  for c in constName do
    if ¬ Lean.Name.isInternalDetail c.name then
        let doc ← Lean.findDocString? env c.name
        match doc with
        | some x => docString := docString ++ "- " ++ x ++ "\n"
        | none =>  docString := docString
  return docString

def header : String := "
  Answer as if you an expert mathematician, physicist and software engineer.
  Below I have listed the doc strings of definitions and theorems in a Lean 4 file.
  Output a list of 1) spelling mistakes. 2) grammatical errors. 3) suggestions for improvement.
  Note that text within `...` should be treated as code and not spellchecked. Doc strings
  should be a complete sentence, or a noun phrase.


"

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  Lean.enableInitializersExecution
  let firstArg := args.head?
  match firstArg with
  | some x => do
    let mut imp : Import := Import.mk x.toName false
    if x == "random" then
      let mods : Name :=  `Physlib
      let imps :  Import := {module := mods}
      let mFile ← findOLean imps.module
      unless (← mFile.pathExists) do
            throw <| IO.userError s!"object file '{mFile}' of module {imps.module} does not exist"
      let (physlibMod, _) ← readModuleData mFile
      let imports := physlibMod.imports
      let y ← IO.rand 0 (imports.size -1)
      imp := imports.get! y
    let mFile ← findOLean imp.module
    let filePath := (mkFilePath (imp.module.toString.split (· == '.'))).addExtension "lean"
    IO.println s!"Checking: {filePath}"
    let (modData, _) ← readModuleData mFile
    let cons := modData.constants
    let docString ← CoreM.withImportModules #[imp.module] (getDocString cons).run'
    let message : LLM.Message := {role := Role.user, content := header ++ docString}
    let request : GPT.Request := {messages := [message]}
    let response ← LLM.GPT.chat (toString <| ToJson.toJson request)
    let parsedRespone := GPT.parse response
    match parsedRespone with
    | .ok x => IO.println x
    | .error e => IO.println e
  | none => IO.println "No module provided."
  return 0
