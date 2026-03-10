/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
module

public import Lean
public import PhysLean.Meta.TODO.Basic
/-!

This file enables us to transverse tactics and test for conditions.

## References
The content of this file is based on the following sources (released under the Apache 2.0 license).

- https://github.com/dwrensha/tryAtEachStep/blob/main/tryAtEachStep.lean
- https://github.com/lean-dojo/LeanDojo/blob/main/src/lean_dojo/data_extraction/ExtractData.lean

Modifications have been made to the original content of these files here.

See also:
- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Memory.20increase.20in.20loops.2E
-/

@[expose] public section

open Lean Elab System

namespace transverseTactics

/-- Takes in a file and returns the infostates of commands and the corresponding
  environment before the command is processed. -/
partial def processCommands : Frontend.FrontendM (List (Environment × InfoState)) := do
  /- Very roughly, `Frontend.FrontendM (List (Environment × InfoState))` is equivalent
    to `Frontend.Context → Frontend.state → List (Environment × InfoState)`.

    The `←get` here is returning the inputted value of `Frontend.state`,
    from which we get the environment.
    -/
  let env := (← get).commandState.env
  /- Processes a single command, adding it to `env`. This is done using
    `modify fun s => { s with commands := s.commands.push cmd }` as part of
    `Frontend.processCommand`. -/
  let done ← Frontend.processCommand
  /- Gets the updated `Frontend.state`. -/
  let st := ← get
  /- Gets the infostate associated with the single command. -/
  let infoState := st.commandState.infoState
  set {st with commandState := {st.commandState with infoState := {}}}
  if done
  then return [(env, infoState)]
  else
    /- For each command, we return the environment before the command is processed,
      and the `infoState` associated with that command. -/
    return (env, infoState) :: (← processCommands)

/-- Tests if a given `info` is `ofTacticInfo` and if so runs `visitTacticInfo`. -/
def visitInfo (file : FilePath) (env : Environment)
    (visitTacticInfo : FilePath → ContextInfo → TacticInfo → MetaM Unit) (ci : ContextInfo)
    (info : Info) (acc : List (IO Unit)) : List (IO Unit) :=
  match info with
  | .ofTacticInfo ti =>
    (ci.runMetaM default
    (do setEnv env
        try visitTacticInfo file ci ti
        catch e =>
          println! "caught: {←e.toMessageData.toString}")) :: acc
  | _ => acc

/-- Applies `visitInfo` to each node of the info trees. -/
def traverseForest (file : FilePath)
    (visitTacticInfo : FilePath → ContextInfo → TacticInfo → MetaM Unit)
    (steps : List (Environment × InfoState)) : List (IO Unit) :=
  let t := steps.map fun (env, infoState) ↦
    (infoState.trees.toList.map fun t ↦
      (Lean.Elab.InfoTree.foldInfo (visitInfo file env visitTacticInfo) [] t).reverse)
  t.flatten.flatten

end transverseTactics

TODO "6VZEW" "Find a way to free the environment `env` in `transverseTactics`.
  This leads to memory problems when using `transverseTactics` directly in loops."

open transverseTactics in
/-- Applies `visitTacticInfo` to each tactic in a file. -/
unsafe def transverseTactics (file : FilePath)
  (visitTacticInfo : FilePath → ContextInfo → TacticInfo → MetaM Unit) : IO Unit := do
  initSearchPath (← findSysroot)
  /- This is equivalent to `(IO.FS.readFile file).bind (fun fileContent => do ...)`. -/
  let fileContent ← IO.FS.readFile file
  enableInitializersExecution
  /- Get `Parser.InputContext` from file. -/
  let inputCtx := Parser.mkInputContext fileContent file.toString -- The input content of the file
  /- We parse the header. Recall that the parser is takes a string and
    outputs a Lean syntax object. -/
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  /- Recall that the elaborator turns a Lean syntax object into a Lean Expr object.
    In the below, we process the header, creating an environment with the relevant imports.
    This can be thought of as creating an import only file. -/
  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == .error then
        println! "ERROR: {← msg.toString}"
    throw $ IO.userError "Errors during import; aborting"
  for msg in messages.toList do
    println! "{← msg.toString}"
  let (env, messages) ← processHeader header {} messages inputCtx
  if messages.hasErrors then
    for msg in messages.toList do
      if msg.severity == .error then
        println! "ERROR: {← msg.toString}"
    throw $ IO.userError "Errors during import; aborting"
  /- As part of the environment header is the module name. This is not included
    in our current `env`. So we include it now. -/
  let env1 := env.setMainModule (← moduleNameOfFileName file none)
  /- From the environment, we create a state of the `Command` monad. -/
  let commandState := {Command.mkState env1 messages {} with infoState.enabled := true}
  /- We create a state of the `Frontend` monad-/
  /- Runs the `processCommands` function on the context defined by `inputCtx`, and the
  state defined by `frontendState`. -/
  let (steps, _frontendState) ← (processCommands.run { inputCtx := inputCtx }).run
    { commandState := commandState, parserState := parserState, cmdPos := parserState.pos }
  /- Note that for us, each `infoState.trees` is actually of length 1. -/
  for t in traverseForest file visitTacticInfo steps do
    try t
    catch e =>
      println! "caught top level: {e}"
  pure ()
