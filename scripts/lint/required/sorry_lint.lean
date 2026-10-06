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

# Script to check sorryful/pseudo attribution

This script checks that all declarations which depend on `sorryAx` are marked with the
`sorryful` attribute, and vice versa. It also checks that all declarations which depend on
`Lean.ofReduceBool` are marked with the `pseudo` attribute, and vice versa.

-/
open Lean

unsafe def main (_ : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  Lean.enableInitializersExecution
  println! "Checking sorryful results."
  let env ← importModules (loadExts := true) #[`Physlib, `QuantumInfo] {} 0
  let fileName := ""
  let options : Options := {}
  let ctx : Core.Context := {fileName, options, fileMap := default }
  let state := {env}
  let _ ← (Lean.Core.CoreM.toIO · ctx state) do (Physlib.sorryfulPseudoTest).run'
