/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Physlib.Meta.Informal.Post
import Mathlib.Lean.CoreM
import Physlib.Meta.Linters.Sorry
import Physlib.Meta.Sorry
/-!

# Script to check for `sorry` and the pseudo attribution

This script checks that no declaration depends on `sorryAx`, whether or not it is marked with
the `sorryful` attribute. It also checks that all declarations which depend on
`Lean.ofReduceBool` are marked with the `pseudo` attribute, and vice versa.

`lake exe sorry_lint` checks `Physlib`, `QuantumInfo` and `PhyslibAlpha`;
`lake exe sorry_lint Physlib QuantumInfo` checks only the libraries given.

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
  println! "Checking for sorry in {", ".intercalate (toCheck.map toString).toList}."
  let env ← importModules (loadExts := true) (toCheck.map ({ module := · })) {} 0
  let fileName := ""
  let options : Options := {}
  let ctx : Core.Context := {fileName, options, fileMap := default }
  let state := {env}
  let (passed, _) ← (Lean.Core.CoreM.toIO · ctx state) do (Physlib.sorryfulPseudoTest toCheck).run'
  return if passed then 0 else 1
