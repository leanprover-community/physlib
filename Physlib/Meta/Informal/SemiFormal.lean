/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
module

public meta import Lean.Elab.Command

/-!

# Semiformal results

Semiformal results sit in between informal and formal results. There type or proposition is
defined, by the proof or definition is not.

## Note

The code here is modified from the `Util.ProofWanted` module of the Batteries library.
Released under the Apache 2.0 license, copyright 2023 Lean FRO, authored by
David Thrane Christiansen.

-/

@[expose] public section

open Lean Parser Elab Command

/-- The information from a `TODO ...` command. -/
structure WantedInfo where
  /-- The content of the note. -/
  content : String
  /-- Name of result. -/
  name : Name
  /-- The file name where the note came from. -/
  fileName : Name
  /-- The line from where the note came from. -/
  line : Nat
  /-- The tag of the TODO item -/
  tag : String

/-- The environment extension for semiformal results. -/
meta initialize wantedExtension : SimplePersistentEnvExtension WantedInfo (Array WantedInfo) ←
  registerSimplePersistentEnvExtension {
    name := `wantedExtension
    addEntryFn := fun arr todoInfor => arr.push todoInfor
    addImportedFn := fun es => es.foldl (· ++ ·) #[]
  }

/-- A semiformal result is either a
- definition in which the type is given but not the definition.
- proof in which the proposition is given but not the proof.
Semiformal results cannot be used in further code. They are essentially
forgot about after made.

With minor modification they act in a similar way to `proof_wanted`, however
they appear in Physlib's TODO list and must be tagged accordingly.
They must also always have a doc-string. -/
@[command_parser]
meta def «semiformal_result» := leading_parser
    docComment >> "semiformal_result" >> strLit >> declId >> ppIndent declSig

/-- The elaborator for semiformal results. -/
@[command_elab «semiformal_result»]
meta def elabLemmaWanted : CommandElab := fun stx =>
  match stx with
  | `($doc:docComment semiformal_result $s $name $args* : $res) =>
    let tag : String := s.getString
    let pos := stx.getPos?
    let docString : String := doc.getDocString
    match pos with
    | some pos => do
      let env ← getEnv
      let fileMap ← getFileMap
      let filePos := fileMap.toPosition pos
      let line := filePos.line
      let modName := env.mainModule
      let wantedInfo : WantedInfo := {
        content := docString,
        name := (Lean.Elab.expandDeclIdCore name).1,
        fileName := modName,
        line := line,
        tag := tag }
      let _ ← modifyEnv fun env => wantedExtension.addEntry env wantedInfo
      let _ ← withoutModifyingEnv do
      elabCommand <| ←
        `(section
        set_option linter.unusedVariables false
        axiom helper {α : Sort _} : α
        $doc:docComment noncomputable def $name $args* : $res := helper
        end)
      pure ()
    | none => throwError "Invalid syntax for `lemma_wanted` command"
  | _ => throwError "Invalid syntax for `lemma_wanted` command"
