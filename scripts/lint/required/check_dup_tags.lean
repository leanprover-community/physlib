/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Physlib.Meta.Basic
import Physlib.Meta.TODO.Basic
import Mathlib.Lean.CoreM
import Physlib.Meta.Informal.Post
import Physlib.Meta.Informal.SemiFormal
/-!

# Checks for duplicate TODO tags

-/

open Lean System Meta Physlib Core


def tagsFromTODOs : MetaM (Array String) := do
  let env ← getEnv
  let todoInfo := (todoExtension.getState env)
  -- pure (todoInfo.qsort (fun x y => x.fileName.toString < y.fileName.toString)).toList
  pure (todoInfo.map fun x => x.tag)

unsafe def informalTODO (x : ConstantInfo) : CoreM String := do
  let tag ← Informal.getTag x
  return tag

unsafe def tagsFromInformal : CoreM (Array String) := do
  (← AllInformal).mapM (fun x => Informal.getTag x)

unsafe def tagsFromSemiformal  : CoreM (Array String) := do
  let env ← getEnv
  let semiInformalInfos := (wantedExtension.getState env)
  pure (semiInformalInfos.map fun x => x.tag)

unsafe def tagDuplicateTest : MetaM Unit := do
  let tags := ((← tagsFromTODOs) ++ (← tagsFromInformal) ++ (← tagsFromSemiformal)).toList
  if !tags.Nodup then
    let duplicates := tags.filter (fun tag => tags.count tag > 1) |>.eraseDups
    println! duplicates
    panic! s!"Duplicate tags found: {duplicates}"
  pure ()

unsafe def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  Lean.enableInitializersExecution
  println! "Checking for duplicate tags."
  let env ← importModules (loadExts := true) #[`Physlib, `QuantumInfo] {} 0
  let fileName := ""
  let options : Options := {}
  let ctx : Core.Context := {fileName, options, fileMap := default }
  let state := {env}
  let _ ← (Lean.Core.CoreM.toIO · ctx state) do (tagDuplicateTest).run'
  println! "\x1b[32mLinter finished, no duplicaate tags found.\x1b[0m"
  pure 0
