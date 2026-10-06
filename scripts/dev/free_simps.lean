/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Batteries.Lean.HashSet
import Batteries.Data.String.Matcher
import Lean
import Physlib.Meta.AllFilePaths
import Physlib.Meta.TransverseTactics
/-!

This file checks for non-terminating `simp` tactics which do not appear as `simp only`.
## References

The content of this file is based on the following sources (released under the Apache 2.0
license), with modifications made to the original content here.

* https://github.com/dwrensha/tryAtEachStep/blob/main/tryAtEachStep.lean.
  [ref: github_tryateachstep]
* https://github.com/lean-dojo/LeanDojo/blob/main/src/lean_dojo/data_extraction/ExtractData.lean.
  [ref: github_leandojo_extractdata]
* See also: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Memory.20increase.20in.20loops.2E.
-/
open Lean Elab System

namespace Lean.Elab.TacticInfo

def name? (t : TacticInfo) : Option Name :=
  match t.stx with
  | Syntax.node _ n _ => some n
  | _ => none

/-- Decide whether a tactic is "substantive",
or is merely a tactic combinator (e.g. `by`, `;`, multiline tactics, parenthesized tactics). -/
def isSimp (t : TacticInfo) : Bool :=
  match t.name? with
  | some ``Lean.Parser.Tactic.simp => true
  | some ``Lean.Parser.Tactic.dsimp => true
  | some ``Lean.Parser.Tactic.simpAll => true
  | _ => false

end Lean.Elab.TacticInfo

def visitTacticInfo (file : FilePath) (ci : ContextInfo) (ti : TacticInfo) : MetaM Unit := do
  if not ti.isSimp then return ()
  let stx := ti.stx
  match stx.getHeadInfo? with
  | .some (.synthetic ..) =>
     -- Not actual concrete syntax the user wrote. Ignore.
    return ()
  | _ =>  pure ()
  let some sp := stx.getPos? | return ()
  let startPosition := ci.fileMap.toPosition sp
  let some ep := stx.getTailPos? | return ()
  let s := Substring.mk ci.fileMap.source sp ep
  if ti.goalsAfter.length ≠ 0  ∧ ¬ String.containsSubstr s.toString  "only" then
    println! "./{file}:{startPosition.line}"

/- See conversation here: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Memory.20increase.20in.20loops.2E -/
unsafe def processAllFiles : IO Unit := do
  let files ← allFilePaths
  let tasks := files.map fun f =>
    ((IO.asTask $ IO.Process.run
    {cmd := "lake", args := #["exe", "free_simps", f.toString]}), f)
  tasks.toList.zipIdx.forM fun ((t, path), n) => do
    let tn ← IO.wait (← t)
    match tn with
    | .ok x =>
      if x ≠ "" then
      println! "{n} of {tasks.toList.length}: {path}"
      println! x
    | .error _ => println! "Error"

unsafe def processFileArray (files : Array FilePath) : IO Unit := do
  if files.toList.length = 0 then
    return ()
  if files.toList.length = 1 then
    let path? := files[0]?
    match path? with
    | some path =>
      transverseTactics path visitTacticInfo
      return ()
    | none =>
      return ()
  let tasks := files.map fun f =>
    ((IO.asTask $ IO.Process.run
    {cmd := "lake", args := #["exe", "free_simps","-file", f.toString]}), f)
  tasks.toList.zipIdx.forM fun ((t, path), n) => do
    let tn ← IO.wait (← t)
    match tn with
    | .ok x =>
      if x ≠ "" then
      println! "{n} of {tasks.toList.length}: {path}"
      println! x
    | .error _ => println! "Error"
  IO.println "Finished!"

unsafe def argToArrayFilePath (args : List String) : IO (Array FilePath) := do
  match args with
  | ["-file", path] => return #[path]
  | ["-dir", dir] => do
    let files ← allFilePaths.go (#[] : Array FilePath) dir (dir : FilePath)
    return files
  | [] => do
    let files ← allFilePaths
    return files
  | _ => do
    panic! "Invalid arguments"

unsafe def main (args : List String) : IO Unit := do
  let files ← argToArrayFilePath args
  processFileArray files
