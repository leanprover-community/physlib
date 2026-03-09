/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
module

public meta import Lean.Elab.Command
/-!

# Basic underlying structure for TODOs.

-/

@[expose] public section

namespace PhysLean
open Lean

/-- The information from a `TODO ...` command. -/
structure todoInfo where
  /-- The content of the note. -/
  content : String
  /-- The file name where the note came from. -/
  fileName : Name
  /-- The line from where the note came from. -/
  line : Nat
  /-- The tag of the TODO item -/
  tag : String

/-- Environment extension to store `todo ...`. -/
meta initialize todoExtension : SimplePersistentEnvExtension todoInfo (Array todoInfo) ←
  registerSimplePersistentEnvExtension {
    name := `todoExtension
    addEntryFn := fun arr todoInfor => arr.push todoInfor
    addImportedFn := fun es => es.foldl (· ++ ·) #[]
  }

/-- Syntax for the `TODO ...` command. -/
syntax (name := todo_comment) "TODO " str str : command

/-- Elaborator for the `TODO ...` command -/
@[command_elab todo_comment]
meta def elabTODO : Elab.Command.CommandElab := fun stx =>
  match stx with
  | `(TODO $t $s) => do
    let str : String := s.getString
    let tag : String := t.getString
    let pos := stx.getPos?
    match pos with
    | some pos => do
      let env ← getEnv
      let fileMap ← getFileMap
      let filePos := fileMap.toPosition pos
      let line := filePos.line
      let modName := env.mainModule
      let todoInfo : todoInfo := { content := str, fileName := modName, line := line, tag := tag }
      modifyEnv fun env => todoExtension.addEntry env todoInfo
    | none => throwError "Invalid syntax for `TODO` command"
  | _ => throwError "Invalid syntax for `TODO` command"

end PhysLean
