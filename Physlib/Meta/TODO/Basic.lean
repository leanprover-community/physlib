/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
module

public meta import Lean.Elab.Command
/-!

# Basic underlying structure for TODOs.

A `TODO "..."` command records a note about the module it appears in.

A TODO item can also record the range of lines of code that the note is about. This is
done with an optional `(lines := ...)` clause, which comes between `TODO` and the string:

- `TODO (lines := 82) "..."` refers to line `82` of the module.
- `TODO (lines := 201-223) "..."` refers to lines `201` to `223` of the module.

A TODO item written without such a clause refers to the line the command itself is on,
which is the behaviour of every TODO item written before ranges of lines existed.

The ranges are rendered in the form used by links into GitHub, so `#L82` for a single
line and `#L201-L223` for a range of lines.

## Note on the syntax

The clause is written `(lines := 201-223)` rather than `#L201-L223` because the latter
would need `#L` and `-L` as new tokens for the whole of Physlib, and `-L` in particular
already occurs in Physlib as the negation of a term whose name starts with `L`.

## Writing one from the editor

Selecting the lines a note is about and running the task `Physlib: TODO about selection`
from the command palette writes the command for you, and puts the cursor between the
quotes of the note ready to type. It goes at the nearest position below the selection at
which a command is legal, which is not in general the line below the selection: a `TODO`
inside a term, a tactic block, a docstring or a `/- -/` comment does not parse, so the
placement steps down past any of those, and past the end of the enclosing declaration.
The line range in the clause is the range that was selected, not where the command ended
up.

The command goes below the selection rather than above it so that the lines it names are
still the lines it was written about: the clause counts lines of the file, and a command
inserted above the selection would push the selection down.

The task is defined in `.vscode/tasks.json` and calls `scripts/insert_todo.py`, which can
also be run directly. To reach it with one keystroke, bind the task in `keybindings.json`:

```
{ "key": "cmd+shift+t", "command": "workbench.action.tasks.runTask",
  "args": "Physlib: TODO about selection" }
```

-/

@[expose] public section

namespace Physlib
open Lean

/-- The information from a `TODO ...` command. -/
structure todoInfo where
  /-- The content of the note. -/
  content : String
  /-- The file name where the note came from. -/
  fileName : Name
  /-- The line from where the note came from. If the note carries a range of lines,
  this is the first line of that range. -/
  line : Nat
  /-- The last line of the range of lines the note is about. For a note which does not
  carry a range of lines this is equal to `line`. -/
  endLine : Nat := line
  /-- The tag of the TODO item -/
  tag : String

/-- Environment extension to store `todo ...`. -/
meta initialize todoExtension : SimplePersistentEnvExtension todoInfo (Array todoInfo) ←
  registerSimplePersistentEnvExtension {
    name := `todoExtension
    addEntryFn := fun arr todoInfor => arr.push todoInfor
    addImportedFn := fun es => es.foldl (· ++ ·) #[]
  }

/-- Syntax for the optional range of lines of a `TODO ...` command. This is
`(lines := 82)` for a single line, and `(lines := 201-223)` for a range of lines. -/
syntax todoLines := "(" &"lines" " := " num ("-" num)? ")"

/-- Syntax for the `TODO ...` command. -/
syntax (name := todo_comment) "TODO " (todoLines)? str : command

/-- The first and last line of the range of lines of a `TODO ...` command, read off from
the optional `(lines := ...)` clause. The argument `line` is the line the command itself
is on, and is the answer when no such clause is present. -/
meta def todoLinesOfSyntax (stx : Syntax) (line : Nat) :
    Elab.Command.CommandElabM (Nat × Nat) := do
  if stx.getNumArgs == 0 then
    return (line, line)
  let clause := stx[0]
  let some first := clause[3].isNatLit? |
    throwError "Invalid range of lines for the `TODO` command"
  let lastStx := clause[4]
  if lastStx.getNumArgs == 0 then
    return (first, first)
  let some last := lastStx[1].isNatLit? |
    throwError "Invalid range of lines for the `TODO` command"
  if last < first then
    throwError "The `TODO` command was given a range of lines ending before it starts"
  return (first, last)

/-- Elaborator for the `TODO ...` command -/
@[command_elab todo_comment]
meta def elabTODO : Elab.Command.CommandElab := fun stx => do
  let some str := stx[2].isStrLit? |
    throwError "Invalid syntax for `TODO` command"
  let some pos := stx.getPos? |
    throwError "Invalid syntax for `TODO` command"
  let tag : String := toString (String.hash str)
  let env ← getEnv
  let fileMap ← getFileMap
  let commandLine := (fileMap.toPosition pos).line
  let (line, endLine) ← todoLinesOfSyntax stx[1] commandLine
  let modName := env.mainModule
  let todoInfo : todoInfo := {
    content := str, fileName := modName, line := line, endLine := endLine, tag := tag}
  modifyEnv fun env => todoExtension.addEntry env todoInfo
  Elab.Command.liftTermElabM <| Lean.Elab.Term.addTermInfo' stx[2]
    (Lean.mkStrLit s!"TODO tag: {tag}") (expectedType? := none)

end Physlib
