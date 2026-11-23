/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Meta.Basic
public import Mathlib.Lean.CoreM

/-!

# Checking redundant imports

Checks imports without losing module visibility or execution phases.

## i. Overview

An import is redundant only when another import supplies the same module with sufficient
visibility, including `public`, `meta`, and `import all` requirements.

## ii. Key results

- `Imports.suppliesImport` checks whether an import is supplied by a public dependency path.
- `Imports.redundantVisibleImports` finds imports that can be removed together.

## iii. Table of contents

- A. Import visibility
- B. Reporting redundant imports

## iv. References

* None.

-/

@[expose] public section

open Lean System Meta Physlib

/-! ## A. Import visibility -/

/-- Whether one import supplies another through publicly exported dependencies. -/
def Imports.suppliesImport (importsOf : Name → Array Import) (source target : Import) : Bool :=
  Id.run do
    let mut pending := [source]
    let mut seen : Std.HashSet Import := {}
    while let current :: rest := pending do
      pending := rest
      if seen.contains current then continue
      seen := seen.insert current
      if current.module == target.module &&
          (!target.isExported || current.isExported) &&
          (!target.importAll || current.importAll) && current.isMeta == target.isMeta then
        return true
      for dependency in importsOf current.module do
        if dependency.isExported then
          pending := { dependency with
            isExported := current.isExported && dependency.isExported
            importAll := current.importAll && dependency.importAll
            isMeta := current.isMeta || dependency.isMeta } :: pending
    return false

/-- Find removable imports while retaining at least one copy of duplicate imports. -/
def Imports.redundantVisibleImports (importsOf : Name → Array Import)
    (imports : Array Import) : Array Import := Id.run do
  let mut kept := imports
  let mut redundant := #[]
  for candidate in imports do
    let others := kept.erase candidate
    if others.any (fun source => suppliesImport importsOf source candidate) then
      kept := others
      redundant := redundant.push candidate
  return redundant

/-! ## B. Reporting redundant imports -/

/-- Report redundant imports using each module's exported import edges. -/
def Imports.RedundantImports (imp : Import) : MetaM UInt32 := do
  let env ← getEnv
  let importsOf := fun name =>
    match env.getModuleIdx? name with
    | some idx => env.header.moduleData[idx.toNat]!.imports.filter (·.module != `Init)
    | none => #[]
  let x := redundantVisibleImports importsOf (importsOf imp.module)
  if x.isEmpty then return 0
  println! "\n"
  println! s!"\x1b[31mError: Transitive imports in {Name.toFilePath imp.module} (please remove them):\x1b[0m"
  for redundant in x do
    println! s!"  {redundant}"
  return 1

unsafe def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  Lean.enableInitializersExecution
  let imports ← allImports
  let results ← CoreM.withImportModules #[`Physlib, `QuantumInfo]
    (imports.mapM Imports.RedundantImports).run'
  return if results.any (· != 0) then 1 else 0
