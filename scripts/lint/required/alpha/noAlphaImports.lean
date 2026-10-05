import Lean
import Physlib.Meta.AllFilePaths

/-!
Copyright (c) 2026 Fergus Munro. All rights reserved.
Released under Apache 2.0 license.
Authors: Fergus Munro

This module validates that no files in the Physlib and QuantumInfo directories
contain import statements that reference PhyslibAlpha. It walks through all .lean
files in these directories and reports any violations found, returning an exit code
indicating success or failure of the validation check.
-/

open Lean
open System

/-- 
  Returns True if not files in Physlib or QuantumInfo import import any 
  PhyslibAlpha files, and False otherwise, printing the offending files and 
  imports to the standard output.
  -/
def areNoAlphaImports (modules : List String) : IO Bool := do
  let mut violations  : Array (FilePath × Name) := #[]

  for module in modules do

    let filePaths ← getFilePaths module
    for filePath in filePaths do 
      
      let contents ← IO.FS.readFile filePath
      let (imports, _pos, _messages) ← Elab.parseImports contents filePath.toString
      
      for imp in imports do
        if imp.module.toString.contains "PhyslibAlpha" then
          violations := violations.push (
            filePath, imp.module
          )

  if violations.size > 0 then
    IO.println "Found Violations:"
    for violation in violations do
      IO.println s!"  {violation.fst} : {violation.snd}"

    return False
  else 
    IO.println "No violations found. All files passed the check."
    return True

unsafe def main (args : List String) : IO Unit := do
  let dirs := match args with
    | [] => ["./Physlib", "./QuantumInfo"]
    | _ => args

  let success ← areNoAlphaImports dirs

  if !success then
    IO.Process.exit 1
  



    
