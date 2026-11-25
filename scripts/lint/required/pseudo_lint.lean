/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Meta.Informal.Post
public import Mathlib.Lean.CoreM
public import Physlib.Meta.Pseudo

@[expose] public meta section
/-!

# Script to check the pseudo attribution

This script checks that all declarations which depend on `Lean.ofReduceBool` are marked
with the `pseudo` attribute, and vice versa.

`lake exe pseudo_lint` checks `Physlib`, `QuantumInfo` and `PhyslibAlpha`;
`lake exe pseudo_lint Physlib QuantumInfo` checks only the libraries given.

-/
open Lean

/-- The libraries which are checked. -/
def libraries : Array Name := #[`Physlib, `QuantumInfo, `PhyslibAlpha]

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  Lean.enableInitializersExecution
  let toCheck := if args.isEmpty then libraries else (args.map String.toName).toArray
  for library in toCheck do
    unless libraries.contains library do
      IO.eprintln s!"Unknown library `{library}`, expected one of {libraries}."
      return 1
  println! "Checking the pseudo attribution in {", ".intercalate (toCheck.map toString).toList}."
  -- Initialize the pseudo extension even when the libraries being checked do not import it.
  let imports := #[{ module := `Physlib.Meta.Linters.Pseudo }] ++ toCheck.map ({ module := · })
  let env ← importModules (loadExts := true) imports {} 0
  let fileName := ""
  let options : Options := {}
  let ctx : Core.Context := {fileName, options, fileMap := default }
  let state := {env}
  let (passed, _) ← (Lean.Core.CoreM.toIO · ctx state) do (Physlib.pseudoTest toCheck).run'
  return if passed then 0 else 1
