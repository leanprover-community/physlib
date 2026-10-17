/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Batteries.Lean.HashSet
import Batteries.Data.List.Basic
import Lean
import Physlib.Meta.AllFilePaths
import Physlib.Meta.TransverseTactics
/-!

This file produces a list of places where `rfl` will complete the goal.

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
def isSubstantive (t : TacticInfo) : Bool :=
  match t.name? with
  | none => false
  | some `null => false
  | some ``cdot => false
  | some ``cdotTk => false
  | some ``Lean.Parser.Tactic.inductionAlt => false
  | some ``Lean.Parser.Tactic.case => false
  | some ``Lean.Parser.Term.byTactic => false
  | some ``Lean.Parser.Tactic.tacticSeq => false
  | some ``Lean.Parser.Tactic.tacticSeq1Indented => false
  | some ``Lean.Parser.Tactic.«tactic_<;>_» => false
  | some ``Lean.Parser.Tactic.paren => false
  | some ``Lean.Parser.Tactic.exact => false
  | _ => true

end Lean.Elab.TacticInfo

def visitTacticInfo (file : FilePath) (ci : ContextInfo) (ti : TacticInfo) : MetaM Unit := do
  if not ti.isSubstantive then return ()
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
  for g in ti.goalsBefore do
    (← IO.getStdout).flush
    let mctx := ti.mctxBefore
    --let doprint : MetaM _ := Meta.ppGoal g
    --let x ← doprint.run' (s := { mctx := mctx })
    let dotac := Term.TermElabM.run (ctx := {declName? := ci.parentDecl?})
              <| Tactic.run g (Tactic.evalTactic  (← `(tactic| rfl)))
    try
      let ((mvars, _tstate), _mstate) ← dotac.run {} { mctx := mctx }
      if mvars.length == 0 ∧ s.toString ≠ "rfl"
      then
        println! "./{file}:{startPosition.line}"
      pure ()
    catch _e =>
      pure ()
    pure ()


/- See conversation here: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Memory.20increase.20in.20loops.2E -/
unsafe def processAllFiles : IO Unit := do
  let files ← allFilePaths
  let tasks := files.map fun f =>
    ((IO.asTask $ IO.Process.run
    {cmd := "lake", args := #["exe", "check_rfl", f.toString]}), f)
  (tasks.toList.indexesValues (fun _ => true)).forM fun (n, (t, path)) => do
    println! "{n} of {tasks.toList.length}: {path}"
    let tn ← IO.wait (← t)
    match tn with
    | .ok x => println! x
    | .error _ => println! "Error"

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [path] => transverseTactics path visitTacticInfo
  | _ => processAllFiles
