import Batteries.Tactic.Lint
import Batteries.Data.Array.Basic
import Lake.CLI.Main
import Physlib.Meta.Linters.DefsWithUnderscore
/-!

A minimized version of the Batteries script runLinter dedicated to Physlib.

Made as an attempt to overcome issues outline here:
https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/runLinter.20in.20github.20workflow.20not.20terminating/with/546421343

-/
open Lean Core Elab Command Batteries.Tactic.Lint
open System (FilePath)

open Lake

/-- Run the Batteries linter on a given module and update the linter if `update` is `true`. -/
unsafe def runLinterOnModule  (module : Name): IO Unit := do
  initSearchPath (← findSysroot)
  Lean.enableInitializersExecution
  -- If the linter is being run on a target that doesn't import `Batteries.Tactic.List`,
  -- the linters are ineffective. So we import it here.
  let lintModule := `Batteries.Tactic.Lint
  let lintFile ← findOLean lintModule
  unless (← lintFile.pathExists) do
    -- run `lake build +Batteries.Tactic.Lint` (and ignore result) if the file hasn't been built yet
    let child ← IO.Process.spawn {
      cmd := (← IO.getEnv "LAKE").getD "lake"
      args := #["build", s!"+{lintModule}"]
      stdin := .null
    }
    _ ← child.wait
  let nolints := #[]
  let env ← importModules #[module, lintModule] {} (trustLevel := 1024) (loadExts := true)
  let ctx := { fileName := "", fileMap := default }
  let state := { env }
  Prod.fst <$> (CoreM.toIO · ctx state) do
    let decls ← getDeclsInPackage module.getRoot
    let linters ← getChecks (slow := true) (runAlways := none) (runOnly := none)
    -- The `defsWithUnderscore` linter also reports names that Physlib does not choose, such as
    -- the ones Lean generates for anonymous instances; see `Physlib.defsWithUnderscoreExempt`.
    let linters := linters.map fun l =>
      if l.name == `defsWithUnderscore then Physlib.withDefsWithUnderscoreExemptions l else l
    println! "Results been linted with the following linters:"
    println! linters.map (·.name)
    println! "Starting parallel running on linters on all declarations. Results if any are
      shown below."
    let results ← lintCore decls linters
    let results := results.map fun (linter, decls) =>
      .mk linter <| nolints.foldl (init := decls) fun decls (linter', decl') =>
        if linter.name == linter' then decls.erase decl' else decls
    let failed := results.any (!·.2.isEmpty)
    if failed then
      let fmtResults ←
        formatLinterResults results decls (groupByFilename := true) (useErrorFormat := true)
          s!"in {module}" (runSlowLinters := true) .medium linters.size
      IO.print (← fmtResults.toString)
      IO.Process.exit 1
    else
      IO.println s!"-- Linting passed for {module}."
      IO.Process.exit 0

unsafe def main (_ : List String) : IO Unit := do
  let modulesToLint := #[`PhyslibAlpha]
  modulesToLint.forM <| runLinterOnModule
