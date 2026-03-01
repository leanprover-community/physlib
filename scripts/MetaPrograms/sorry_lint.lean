/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Meta.Informal.Post
import Mathlib.Lean.CoreM
import PhysLean.Meta.Linters.Sorry
import PhysLean.Meta.Sorry
/-!

# Script to check sorryful/pseudo attribution

This script checks that all declarations which depend on `sorryAx` are marked with the
`sorryful` attribute, and vice versa. It also checks that all declarations which depend on
`Lean.ofReduceBool` are marked with the `pseudo` attribute, and vice versa.

-/
open Lean

unsafe def main (_ : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  println! "Checking sorryful results."
  let env ← importModules (loadExts := true) #[`PhysLean] {} 0
  let fileName := ""
  let options : Options := {}
  let ctx : Core.Context := {fileName, options, fileMap := default }
  let state := {env}
  let _ ← (Lean.Core.CoreM.toIO · ctx state) do (PhysLean.sorryfulPseudoTest).run'
