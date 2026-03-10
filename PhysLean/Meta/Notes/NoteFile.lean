/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
module

public import Lean.Environment
/-!

# Note file

A note file is a structure which contains the information to go into a note.

-/

@[expose] public section

namespace PhysLean
open Lean

/-- A note consists of a title and a list of Lean files which make up the note. -/
structure NoteFile where
  /-- The overall title of the note. -/
  title : String
  /-- The abstract of the note. -/
  abstract : String
  /-- A list of authors. -/
  authors : List String
  /-- The files making up the note in the order in which they should appear. -/
  files : List Name

namespace NoteFile

variable (N : NoteFile)

/-- All imports associated to a note. -/
def imports : Array Import := (N.files.map fun f => {module := f}).toArray

end NoteFile

end PhysLean
