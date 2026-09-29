/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
module

public meta import Lean.Elab.Command
/-!

## Underlying structure for notes

This file contains the necessary structures that must be imported into a file
for it to be turned into a Lean note.

It allows for the
- `note ...` command to be used to add notes to a Lean file
- `note_attr` attribute to be used to display formally verified commands within a note.
- `note_attr_informal` attribute to be used to display informal commands within a note.

Other results relating to notes are in other files.

-/

@[expose] public section

namespace Physlib
open Lean

/-- The information from a `note ...` command. To be used in a note file-/
structure NoteInfo where
  /-- The content of the note. -/
  content : String
  /-- The file name where the note came from. -/
  fileName : Name
  /-- The line from where the note came from. -/
  line : Nat

/-- Environment extension to store `note ...`. -/
meta initialize noteExtension : SimplePersistentEnvExtension NoteInfo (Array NoteInfo) ←
  registerSimplePersistentEnvExtension {
    name := `noteExtension
    addEntryFn := fun arr nodeInfor => arr.push nodeInfor
    addImportedFn := fun es => es.foldl (· ++ ·) #[]
  }

/-- Syntax for the `note ...` command -/
syntax (name := note_comment) "note " str : command

/-- Elaborator for the `note ...` command -/
@[command_elab note_comment]
meta def elabNote : Lean.Elab.Command.CommandElab := fun stx =>
  match stx with
  | `(note $s) => do
    let str : String := s.getString
    let pos := stx.getPos?
    match pos with
    | some pos => do
      let env ← getEnv
      let fileMap ← getFileMap
      let filePos := fileMap.toPosition pos
      let line := filePos.line
      let modName := env.mainModule
      let noteInfo : NoteInfo := { content := str, fileName := modName, line := line }
      modifyEnv fun env => noteExtension.addEntry env noteInfo

    | none => throwError "Invalid syntax for `note` command"
  | _ => throwError "Invalid syntax for `note` command"

/-!

## Note attribute

-/

/-- Environment extension to store `note_attr`. -/
meta initialize noteDeclExtension : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    name := `noteDeclExtension
    addEntryFn := fun arr nodeInfor => arr.push nodeInfor
    addImportedFn := fun es => es.foldl (· ++ ·) #[]
  }

/-- The `note_attr` attribute is used to display formally verified commands within a note. -/
meta initialize noteAttribute : Unit ←
  registerBuiltinAttribute {
    name := `note_attr
    descr := "Note attribute"
    applicationTime := AttributeApplicationTime.afterCompilation
    add := fun declName _ _ => do
      modifyEnv fun env => noteDeclExtension.addEntry env declName
  }

/-- Environment extension to store `note_attr_informal`. -/
meta initialize noteInformalDeclExtension : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    name := `noteInformalDeclExtension
    addEntryFn := fun arr nodeInfor => arr.push nodeInfor
    addImportedFn := fun es => es.foldl (· ++ ·) #[]
  }

/-- The `note_attr_informal` attribute is used to display informal commands within a note. -/
meta initialize noteInformalAttribute : Unit ←
  registerBuiltinAttribute {
    name := `note_attr_informal
    descr := "Informal note attribute"
    applicationTime := AttributeApplicationTime.afterCompilation
    add := fun declName _ _ => do
      modifyEnv fun env => noteInformalDeclExtension.addEntry env declName
  }

end Physlib
