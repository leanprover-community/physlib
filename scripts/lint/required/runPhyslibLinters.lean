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

/-- The file paths of modules exempt from all linters, read from
  `scripts/lint/exemptions/LinterExemption.txt`. This is used to lint `QuantumInfo` file-by-file. -/
def linterExemptions : IO (Array String) := do
  let path : FilePath :=
    (System.mkFilePath ["scripts", "lint", "exemptions", "LinterExemption"]).addExtension "txt"
  unless (← path.pathExists) do return #[]
  let lines ← IO.FS.lines path
  return lines.filterMap (fun l ↦ if l.trimAscii.copy == "" then none else some l.trimAscii.copy)

/-- The file path (as a string e.g. `QuantumInfo/Foo/Bar.lean`) of the module `mod`. -/
def moduleToFilePathString (mod : Name) : String :=
  ((System.mkFilePath (mod.toString.splitToList (· == '.'))).addExtension "lean").toString

/-- Run the Batteries linter on a given module, skipping declarations in exempt modules.
  Returns `true` if linting failed. -/
unsafe def runLinterOnModule (module : Name) (exemptions : Array String) : IO Bool := do
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
    let env ← getEnv
    let decls ← getDeclsInPackage module.getRoot
    -- Skip declarations whose source module is listed in
    -- `scripts/lint/exemptions/LinterExemption.txt`.
    let decls := decls.filter fun n =>
      match env.getModuleIdxFor? n with
      | some idx => !exemptions.contains (moduleToFilePathString env.header.moduleNames[idx]!)
      | none => true
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
      return true
    else
      IO.println s!"-- Linting passed for {module}."
      return false

unsafe def main (_ : List String) : IO Unit := do
  let exemptions ← linterExemptions
  let modulesToLint := #[`Physlib, `QuantumInfo]
  let failures ← modulesToLint.mapM (runLinterOnModule · exemptions)
  if failures.any id then
    IO.Process.exit 1
  else
    IO.Process.exit 0
