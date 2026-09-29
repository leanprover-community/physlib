/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
module

public meta import Lean.Elab.Command
/-!

## Underlying structure for remarks
-/

@[expose] public section

namespace Physlib
open Lean

/-- The information from a `remark ...` command. To be used in a note file-/
structure RemarkInfo where
  /-- The content of the remark. -/
  content : String
  /-- The file name where the remark came from. -/
  fileName : Name
  /-- The line from where the remark came from. -/
  line : Nat
  /-- The name of the remark. -/
  name : Name
  /-- The namespace of the remark. -/
  nameSpace : Name

/-- Environment extension to store `remark ...`. -/
meta initialize remarkExtension : SimplePersistentEnvExtension RemarkInfo (Array RemarkInfo) ←
  registerSimplePersistentEnvExtension {
    name := `remarkExtension
    addEntryFn := fun arr remarkInfoT => arr.push remarkInfoT
    addImportedFn := fun es => es.foldl (· ++ ·) #[]
  }

/-- A remark is a string used for important information. -/
syntax (name := remark_syntax) "remark " ident ":=" str : command

/-- Elaborator for the `note ...` command -/
@[command_elab remark_syntax]
meta def elabRemark : Elab.Command.CommandElab := fun stx =>
  match stx with
  | `(remark $n := $s) => do
    let str : String := s.getString
    let pos := stx.getPos?
    match pos with
    | some pos => do
      let env ← getEnv
      let fileMap ← getFileMap
      let filePos := fileMap.toPosition pos
      let line := filePos.line
      let modName := env.mainModule
      let nameSpace := (← getCurrNamespace)

      let noteInfo : RemarkInfo := {
          content := str,
          fileName := modName,
          line := line,
          name := n.getId,
          nameSpace := nameSpace}
      modifyEnv fun env => remarkExtension.addEntry env noteInfo
    | none => throwError "Invalid syntax for `note` command"
  | _ => throwError "Invalid syntax for `note` command"

end Physlib
