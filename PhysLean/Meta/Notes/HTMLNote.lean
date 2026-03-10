/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
-- import DocGen4.Output.DocString
module

public import PhysLean.Meta.Basic
public import PhysLean.Meta.Notes.Basic
public import PhysLean.Meta.Informal.Basic
/-!

## Turns a declaration into a html note structure.

-/

@[expose] public section

namespace PhysLean
open Lean

/-- A `HTMLNote` is a structure containing the html information from
  individual contributions (commands, informal commands, note ..) etc. to a note file. -/
structure HTMLNote where
  /-- The name of the file the contribution came from. -/
  fileName : Name
  /-- The html contribution of the content. -/
  content : String
  /-- The line in the file where the contribution came from. -/
  line : Nat

/-- Converts a note info into a HTMLNote. -/
def HTMLNote.ofNodeInfo (ni : NoteInfo) : HTMLNote :=
  { ni with }

/-- An formal definition or lemma to html for a note. -/
def HTMLNote.ofFormal (name : Name) : CoreM HTMLNote := do
  let line ← name.lineNumber
  let fileName ← name.fileName
  return {
    fileName, line,
    content := s!"
<div class=\"code-block-container\">
  <a href=\"{fileName.toGitHubLink line}\" class=\"code-button\">View/Improve</a>
  <pre><code>{← name.getDeclString}</code></pre>
</div>"
  }

/-- An informal definition or lemma to html for a note. -/
unsafe def HTMLNote.ofInformal (name : Name) : CoreM HTMLNote := do
  let line ← name.lineNumber
  let fileName ← name.fileName
  let constInfo ← getConstInfoDefn name
  let webAddress := fileName.toGitHubLink line
  let mut content := ""
  if constInfo.type.isConstOf ``InformalDefinition then
    let doc ← name.getDocString
    -- let html ← DocGen4.Output.docStringToHtml doc name.toString
    -- let X ← Informal.constantInfoToInformalDefinition constInfo
    -- let fragment := X.math.replace "\n" "<br>"
    let fragment := doc.replace "\n" "<br>"
    content := s!"
<div class=\"informal-def\">
  <a href=\"{webAddress}\" class=\"button\">Improve/Formalize</a>
  <b>Informal definition:</b> {name}<br>
  {fragment}
</div>"
  else if constInfo.type.isConstOf ``InformalLemma then
    -- let X ← Informal.constantInfoToInformalLemma constInfo
    -- let fragment := X.math.replace "\n" "<br>"
    let doc ← name.getDocString
    let fragment := doc.replace "\n" "<br>"
    content := s!"
<div class=\"informal-def\">
  <a href=\"{webAddress}\" class=\"button\">Improve/Formalize</a>
  <b>Informal lemma:</b> {name}<br>
  {fragment}
</div>"
  return { content, fileName, line }

end PhysLean
