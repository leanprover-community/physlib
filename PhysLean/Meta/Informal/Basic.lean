/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
module

public meta import Lean.Parser.Term
/-!

## Informal definitions and lemmas

This file contains the necessary structures that must be imported into a file for it to contain
informal definitions and lemmas.

Everything else about informal definitions and lemmas are in the `Informal.Post` module.

-/

@[expose] public section

/-- The structure representing an informal definition. -/
structure InformalDefinition where
  /-- The names of top-level commands we expect this definition to depend on. -/
  deps : List Lean.Name
  /-- The tag of the informal definition. This should be unique amongst informal results
    and todo items. -/
  tag : String

/-- The structure representing an informal lemma. -/
structure InformalLemma where
  /-- The names of top-level commands we expect this lemma to depend on. -/
  deps : List Lean.Name
  /-- The tag of the informal lemma. This should be unique amongst informal results
    and todo items. -/
  tag : String

namespace Informal

/-!

## Syntax

Using macros for syntax rewriting works better with the language server compared to
`Lake.DSL.LeanLibDecl`. Hovering over any definition of `informal_definition` or `informal_lemma`
gives a proper type hint like any proper definition using `def` whereas definitions of `lake_lib`
and `lake_exe` don't show docstrings and infer the type `Lean.Name`.

-/

open Lean.Parser.Term

/-- A placeholder for definitions to be formalized in the future. Docstrings of informal definitions
should outline its mathematical or physical content and specify useful references. Use the attribute
`note_attr_informal` from `PhysLean.Meta.Notes.Basic` to mark the informal definition as a note.
-/
macro (name := informalDefinitionDecl)
doc?:(docComment)? attrs?:(attributes)? "informal_definition " name:ident body:declVal : command =>
  `($[$doc?]? $[$attrs?]? def $name : InformalDefinition $body:declVal)

/-- A placeholder for lemmas to be formalized in the future. Docstrings of informal lemmas
should outline its mathematical or physical content and specify useful references. Use the attribute
`note_attr_informal` from `PhysLean.Meta.Notes.Basic` to mark the informal definition as a note.
-/
macro (name := informalLemmaDecl)
doc?:(docComment)? attrs?:(attributes)? "informal_lemma " name:ident body:declVal : command =>
  `($[$doc?]? $[$attrs?]? def $name : InformalLemma $body:declVal)

end Informal
