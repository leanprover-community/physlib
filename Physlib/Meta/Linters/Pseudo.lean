/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
module

public meta import Physlib.Meta.Basic
/-!

# The `pseudo` attribute

The attribute marking declarations which depend on the `Lean.ofReduceBool` axiom.

## i. Overview

This module defines the attribute `pseudo`, marking declarations that depend on the
`Lean.ofReduceBool` axiom, and the environment extension `pseudoExtension` recording them.
The check that the attribute is correctly applied is `Physlib.pseudoTest` in
`Physlib.Meta.Pseudo`.

## ii. Key results

- `pseudoExtension` : The environment extension recording the declarations attributed `pseudo`.
- `Pseudo_attr` : The `pseudo` attribute.

## iii. Table of contents

- A. The `pseudo` environment extension
- B. The `pseudo` attribute

## iv. References

* None.

-/

@[expose] public meta section

open Lean

/-!

## A. The `pseudo` environment extension

-/

/-- The information stored for a declaration marked with `pseudo`. -/
structure PseudoInfo where
  /-- Name of result. -/
  name : Name

/-- An environment extension containing the information of declarations
  which carry the `pseudo` attribute. -/
initialize pseudoExtension : SimplePersistentEnvExtension PseudoInfo (Array PseudoInfo) ←
  registerSimplePersistentEnvExtension {
    name := `pseudoExtension
    addEntryFn := fun arr info => arr.push info
    addImportedFn := fun es => es.foldl (· ++ ·) #[]
  }

/-- Adds an entry to `pseudoExtension`. -/
def addPseudofulEntry {m : Type → Type} [MonadEnv m]
    (declName : Name) : m Unit :=
  modifyEnv (pseudoExtension.addEntry · ⟨declName⟩)

/-!

## B. The `pseudo` attribute

-/

/-- The `pseudo` attribute allows declarations to contain the `Lean.ofReduceBool` axiom.
  In converse, a declaration with the `pseudo` attribute must contain the
  `Lean.ofReduceBool` axiom. -/
syntax (name := Pseudo_attr) "pseudo" : attr

/-- Registration of the `pseudo` attribute. -/
initialize Lean.registerBuiltinAttribute {
  name := `Pseudo_attr
  descr := "The `pseudo` attribute allows declarations to contain the `Lean.ofReduceBool` axiom.
    In converse, a declaration with the `pseudo` attribute must contain the
    `Lean.ofReduceBool` axiom."
  add := fun decl stx _attrKind => do
    let pos := stx.getPos?
    -- match pos with
    -- | some pos => do
      -- let env ← getEnv
      -- let fileMap ← getFileMap
      -- let filePos := fileMap.toPosition pos
      -- let line := filePos.line
      --- let modName := env.mainModule
      -- let nameSpace := (← getCurrNamespace)
      -- let docstring ← Name.getDocString decl
    addPseudofulEntry decl
  applicationTime := AttributeApplicationTime.beforeElaboration
}
