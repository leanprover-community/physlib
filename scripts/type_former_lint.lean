/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Batteries.Lean.HashSet
import Lean
/-!

# Type former Lint

This file checks that all definitions which form types start with a capital letter
(or some non-latin character). This linter is not currently strictly enforced
in PhysLean.


-/
open Lean System Meta


/-- A rough definition of Upper Camal, checking that if a string starts with a
latin letter then that letter is capital.  -/
def IsUpperCamal (s : String) : Bool :=
  let parts := s.splitOn "."
  let lastPart := parts.get! (parts.length - 1)
  lastPart = "noConfusionType" ∨
  (¬ (lastPart.get 0 ≥ 'A' ∧ lastPart.get 0 ≤ 'z')) ∨ (lastPart.get 0 ≥ 'A' ∧ lastPart.get 0 ≤ 'Z')


def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mods : Name :=  `PhysLean
  let imp :  Import := {module := mods}
  let mFile ← findOLean imp.module
  unless (← mFile.pathExists) do
        throw <| IO.userError s!"object file '{mFile}' of module {imp.module} does not exist"
  let (hepLeanMod, _) ← readModuleData mFile
  let mut warned := false
  for imp in hepLeanMod.imports do
    let mFile ← findOLean imp.module
    let (modData, _) ← readModuleData mFile
    let cons := modData.constants
    for c in cons do
      if c.hasValue ∧ ¬ Lean.Name.isInternal c.name ∧ Lean.Compiler.LCNF.isTypeFormerType c.type
        ∧ ¬ IsUpperCamal c.name.toString then
          warned := true
          IO.println s!"name: #{c.name}"
  if warned then
    throw <| IO.userError s!"There are type former definitions not in upper camal style."
  pure 0
