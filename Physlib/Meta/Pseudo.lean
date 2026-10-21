/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Meta.Linters.Pseudo
/-!

# Meta results regarding the `pseudo` attribution

## i. Overview

The purpose of this module is to collect all results which depend on the `Lean.ofReduceBool`
axiom, and check that they are exactly the results attributed `pseudo`.

## ii. Key results

- `pseudoTest` : A test, over given libraries, that the results attributed `pseudo` are exactly
  those depending on the `Lean.ofReduceBool` axiom.

## iii. Table of contents

- A. Collecting results depending on `Lean.ofReduceBool`
  - A.1. The state information to be collected
  - A.2. The monad for collecting names
  - A.3. The collection function
  - A.4. Given an array updating the state with all names depending on axioms
  - A.5. Given an array getting all names depending on axioms
  - A.6. Getting all names depending on axioms from all user defined constants
- B. Collecting all names attributed `pseudo`
- C. Testing that the `pseudo` attribution is correctly applied

## iv. References

* Adapted from `Lean.Util.CollectAxioms`, copyright (c) 2020 Microsoft
  Corporation, authored by Leonardo de Moura.
-/

@[expose] public meta section
open Lean

namespace Physlib

/-!

## A. Collecting results depending on `Lean.ofReduceBool`

-/

namespace CollectOfReduceBool

/-!

### A.1. The state information to be collected

-/

/-- A structure used for collecting names of results dependent on the
  `Lean.ofReduceBool` axiom. -/
structure State where
  /-- The names which have already been visited as part of the state. -/
  visited : NameSet := {}
  /-- The names which depend on the `Lean.ofReduceBool` axiom. -/
  containsOfReduceBool : NameSet := {}

/-!

### A.2. The monad for collecting names

-/

/-- A monad used for collecting names of results dependent on the
  `Lean.ofReduceBool` axiom. -/
abbrev M := ReaderT Environment $ StateM State

/-!

### A.3. The collection function

-/

/-- Given a `c : Name` updating the monad `M` based on which results which `c` uses
  depend on the `Lean.ofReduceBool` axiom. -/
partial def collect (c : Name) (parents : NameSet) : M Unit := do
  let collectExpr (e : Expr) : M Unit := e.getUsedConstants.forM fun x =>
    collect x (parents.insert c)
  let s ← get
  if s.containsOfReduceBool.contains c then
    modify fun s => { s with containsOfReduceBool := s.containsOfReduceBool.append parents}
  unless s.visited.contains c do
    modify fun s => { s with visited := s.visited.insert c }
    let env ← read
    -- We should take the constant from the kernel env, which may differ from the one in the elab
    -- env in case of (async) errors.
    match env.checked.get.find? c with
    | some (ConstantInfo.axiomInfo v) =>
        if v.name == `Lean.ofReduceBool || (toString v.name).contains "native_decide" then
            modify fun s => { s with containsOfReduceBool :=
              s.containsOfReduceBool.append (parents.insert c)}
        collectExpr v.type
    | some (ConstantInfo.defnInfo v) =>
        collectExpr v.type *> collectExpr v.value
    | some (ConstantInfo.thmInfo v) =>
        collectExpr v.type *> collectExpr v.value
    | some (ConstantInfo.opaqueInfo v) =>
        collectExpr v.type *> collectExpr v.value
    | some (ConstantInfo.quotInfo _) => pure ()
    | some (ConstantInfo.ctorInfo v) =>
        collectExpr v.type
    | some (ConstantInfo.recInfo v) =>
        collectExpr v.type
    | some (ConstantInfo.inductInfo v) =>
        collectExpr v.type *> v.ctors.forM fun x => collect x (parents.insert c)
    | none => pure ()

/-!

### A.4. Given an array updating the state with all names depending on axioms

-/

/-- Given a `c : Array Name` updating the monad `M` based on which results
  depend on the `Lean.ofReduceBool` axiom. -/
partial def allOfReduceBool (c : Array Name) : M Unit := do
  c.forM fun x => collect x {}

end CollectOfReduceBool

/-!

### A.5. Given an array getting all names depending on axioms

-/

/-- Given a `c : Array Name` the names of all results used to defined
  the results in `c` with the `Lean.ofReduceBool` axiom. -/
def collectOfReduceBool (c : Array Name) : CoreM (Array Name) := do
  let env ← getEnv
  let (_, s) := ((CollectOfReduceBool.allOfReduceBool c).run env).run {}
  pure s.containsOfReduceBool.toArray

/-!

### A.6. Getting all names depending on axioms from all user defined constants

-/

/-- The files of the libraries with root modules `libs`, as the imports of those roots. -/
def libraryImports (libs : Array Name) : IO (Array Import) := libs.flatMapM fun lib => do
  let (mod, _) ← readModuleData (← findOLean lib)
  return mod.imports.filter (·.module != `Init)

/-- The user defined constants of the libraries with root modules `libs`. -/
def libraryUserConsts (libs : Array Name) : CoreM (Array ConstantInfo) := do
  (← libraryImports libs).flatMapM Physlib.Imports.getUserConsts

/-- The user defined constants of the libraries `libs` depending on the
  `Lean.ofReduceBool` axiom. -/
def allWithOfReduceBool (libs : Array Name) : CoreM (Array Name) := do
  collectOfReduceBool ((← libraryUserConsts libs).map fun c => c.name)

/-!

## B. Collecting all names attributed `pseudo`

-/

/-- All names which are attributed `pseudo`. -/
unsafe def allPseudoAttributed : CoreM (Array Name) := do
  let env ← getEnv
  let pseudoInfos := (pseudoExtension.getState env)
  return pseudoInfos.map fun info => info.name

/-!

## C. Testing that the `pseudo` attribution is correctly applied

-/

/-- Checks, over the libraries with root modules `libs`, that the results attributed `pseudo`
  are exactly those depending on the `Lean.ofReduceBool` axiom. Returns whether the test
  passed. -/
unsafe def pseudoTest (libs : Array Name) : MetaM Bool := do
  let allWithPseudo ← Physlib.allWithOfReduceBool libs
  let allConst ← libraryUserConsts libs
  let allConst := allConst.map fun c => c.name
  let allWithPseudo := allWithPseudo.filter fun n => n ∈ allConst
  let pseudoAttributed := (← allPseudoAttributed).filter fun n => n ∈ allConst
  let withPseudoAxiomNotAttributed :=
    allWithPseudo.filter fun x => ¬ x ∈ pseudoAttributed
  let attributedNotWithPseudoAxiom :=
    pseudoAttributed.filter fun x => ¬ x ∈ allWithPseudo
  if withPseudoAxiomNotAttributed ≠ #[] ∨ attributedNotWithPseudoAxiom ≠ #[] then
    panic! s!"
\x1b[31mThere is an error in the pseudo test:\x1b[0m
  The following names depend on `Lean.ofReduceBool` or `native_decide`
  but are not attributed `pseudo`:
  {withPseudoAxiomNotAttributed}
  The following names are attributed `pseudo` but do not depend on `Lean.ofReduceBool`
  or `native_decide`:
  {attributedNotWithPseudoAxiom}"
    return false
  println! "\x1b[32mPseudo results are all correctly attributed: test passed.\x1b[0m"
  return true

end Physlib
