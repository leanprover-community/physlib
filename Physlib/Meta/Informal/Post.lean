/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Meta.Basic
public import Physlib.Meta.Informal.Basic
/-!

## Informal definitions and lemmas

-/

@[expose] public section
open Lean

namespace Informal

/-- Is true if and only if a `ConstantInfo` corresponds to an `InformalLemma` or a
  `InformalDefinition`. -/
def isInformal : ConstantInfo → Bool
  | .defnInfo c => c.type.isConstOf ``InformalDefinition ∨ c.type.isConstOf ``InformalLemma
  | _ => false

/-- Is true if and only if a `ConstantInfo` corresponds to an `InformalLemma`. -/
def isInformalLemma : ConstantInfo → Bool
  | .defnInfo c => c.type.isConstOf ``InformalLemma
  | _ => false

/-- Is true if and only if a `ConstantInfo` corresponds to an `InformalDefinition`. -/
def isInformalDef : ConstantInfo → Bool
  | .defnInfo c => c.type.isConstOf ``InformalDefinition
  | _ => false

/-- Takes a `ConstantInfo` corresponding to a `InformalLemma` and returns
  the corresponding `InformalLemma`. -/
unsafe def constantInfoToInformalLemma (c : ConstantInfo) : CoreM InformalLemma := do
  match c with
  | .defnInfo c => evalConstCheck InformalLemma ``InformalLemma c.name
  | _ => panic! "Passed constantInfoToInformalLemma a `ConstantInfo` that is not a `InformalLemma`"

/-- Takes a `ConstantInfo` corresponding to a `InformalDefinition` and returns
  the corresponding `InformalDefinition`. -/
unsafe def constantInfoToInformalDefinition (c : ConstantInfo) : CoreM InformalDefinition := do
  match c with
  | .defnInfo c => evalConstCheck InformalDefinition ``InformalDefinition c.name
  | _ => panic!
    "Passed constantInfoToInformalDefinition a `ConstantInfo` that is not a `InformalDefinition`"

/-- Gets the tag associated with an informal definition or lemma. -/
unsafe def getTag (c : ConstantInfo) : CoreM String := do
  if isInformalLemma c then
    let i ← constantInfoToInformalLemma c
    return i.tag
  else if isInformalDef c then
    let i ← constantInfoToInformalDefinition c
    return i.tag
  else
    panic! "getTag: Not an informal lemma or definition"

end Informal

namespace Physlib

/-- The number of informal lemmas in Physlib. -/
def noInformalLemmas : CoreM Nat := do
  let imports ← allImports
  let x ← imports.mapM Imports.getUserConsts
  x.flatFilterSizeM fun c => return Informal.isInformalLemma c

/-- The number of informal definitions in Physlib. -/
def noInformalDefs : CoreM Nat := do
  let imports ← allImports
  let x ← imports.mapM Imports.getUserConsts
  x.flatFilterSizeM fun c => return Informal.isInformalDef c

/-- All informal results. -/
def AllInformal : CoreM (Array ConstantInfo) := do
  let imports ← allImports
  let x ← (imports.mapM Imports.getUserConsts)
  let y := x.flatten.filter fun c => Informal.isInformal c
  return y

end Physlib
