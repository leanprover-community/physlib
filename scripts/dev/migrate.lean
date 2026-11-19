/-
Copyright (c) 2026 Physlib contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Physlib contributors
-/
import Lean
import Lake.CLI.Main

/-!
# Migrating deprecated declarations
Replace references to deprecated declarations with their declared alternatives.

## i. Overview

`lake exe migrate` processes every top-level `lean_lib` in the Lake configuration.
`lake exe migrate Physlib` processes only the library named `Physlib`. Imports must be built.
References are identified by elaboration, preserving comments, strings, and local variables.
Deprecations with only a prose message are left alone. Each changed file is elaborated again
before being written; failures leave that file untouched and produce a nonzero exit status.
Field notation is migrated when the replacement stays in the same namespace; other field
notation requires a manual rewrite and is reported. Each file runs in a separate process so
imported environments are released between files.

## ii. Key results

* `Migrate.collectEdit` identifies references using Lean's deprecation attribute.
* `Migrate.migrateFile` checks the migrated source before writing it.

## iii. Table of contents

* A. Finding replacements
* B. Elaborating and editing files
* C. Command line interface

## iv. References

See `Lean.Linter.Deprecated` for the deprecation attribute.

## A. Finding replacements
-/

open Lean Elab System

namespace Migrate

/-- An identifier replacement, using UTF-8 byte positions in the original source. -/
structure Edit where
  /-- The replaced source range. -/
  range : Syntax.Range
  /-- The replacement identifier. -/
  text : String
  deriving BEq

/-- Follow a chain of explicit alternatives, rejecting cycles. -/
partial def replacement? (env : Environment) (name : Name)
    (seen : List Name := []) : Option Name := do
  guard (!seen.contains name)
  let next ← Linter.getDeprecatedNewName env name
  if (Linter.getDeprecatedNewName env next).isSome then
    replacement? env next (name :: seen)
  else
    some next

/-- Collect an edit for a resolved constant, ignoring binders and generated syntax. -/
def collectEdit (ctx : ContextInfo) (info : Info) (edits : Array Edit) : IO (Array Edit) := do
  let .ofTermInfo ti := info | return edits
  if ti.isBinder then return edits
  let .const name _ := ti.expr | return edits
  let some next := replacement? ctx.env name | return edits
  let isField := ti.stx.isOfKind Parser.Term.identProjKind
  let stx := if isField then ti.stx[0] else ti.stx
  let .ident _ _ written _ := stx | return edits
  if written.hasMacroScopes then return edits
  let some range := stx.getRange? (canonicalOnly := true) | return edits
  let text? ← if isField then
      pure <| if name.getPrefix == next.getPrefix then
        some (Name.mkSimple next.getString!).toString else none
    else
      ctx.runMetaM ti.lctx do
        return (← unresolveNameGlobalAvoidingLocals? next).map (·.toString)
  let some text := text? | do
    let pos := ctx.fileMap.toPosition range.start
    IO.eprintln s!"{ctx.env.mainModule}:{pos.line}:{pos.column}: manual migration needed: \
      {name} → {next}"
    return edits
  let edit := { range, text : Edit }
  return if edits.contains edit then edits else edits.push edit

/-!
## B. Elaborating and editing files
-/

/-- Parse imports and elaborate a source file, returning its edits and diagnostics. -/
unsafe def elaborate (file : FilePath) (mod : Name) (source : String) :
    IO (Array Edit × MessageLog) := do
  enableInitializersExecution
  let inputCtx := Parser.mkInputContext source file.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let opts := ({} : Options).setBool `Elab.async false
  let (env, messages) ← processHeader header opts messages inputCtx
  if messages.hasErrors then return (#[], messages)
  let env := env.setMainModule mod
  let commandState := { Command.mkState env messages opts with infoState.enabled := true }
  let state ← IO.processCommands inputCtx parserState commandState
  let mut edits := #[]
  for tree in state.commandState.infoState.trees do
    edits ← tree.foldInfoM collectEdit edits
  return (edits, state.commandState.messages)

/-- Apply nonoverlapping edits from the end, preserving original byte positions. -/
def applyEdits (source : String) (edits : Array Edit) : Except String String := do
  let edits := edits.qsort fun a b => a.range.start.byteIdx > b.range.start.byteIdx
  let mut boundary := source.utf8ByteSize
  let mut result := source
  for edit in edits do
    if edit.range.stop.byteIdx > boundary then
      throw "Overlapping replacements; file left unchanged."
    result := (Substring.Raw.mk result 0 edit.range.start).toString ++ edit.text ++
      (Substring.Raw.mk result edit.range.stop result.rawEndPos).toString
    boundary := edit.range.start.byteIdx
  return result

/-- Print elaboration errors, returning whether the source failed to elaborate. -/
def reportErrors (messages : MessageLog) : IO Bool := do
  for msg in messages.toList do
    if msg.severity == .error then IO.eprintln (← msg.toString)
  return messages.hasErrors

/-- Migrate one file only if both the original and edited source elaborate successfully. -/
unsafe def migrateFile (file : FilePath) (mod : Name) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let source ← IO.FS.readFile file
  let (edits, messages) ← elaborate file mod source
  if ← reportErrors messages then return 1
  if edits.isEmpty then return 0
  let .ok updated := applyEdits source edits | do
    IO.eprintln s!"{file}: overlapping replacements; file left unchanged."
    return 1
  let (_, messages) ← elaborate file mod updated
  if ← reportErrors messages then
    IO.eprintln s!"{file}: migrated source failed to elaborate; file left unchanged."
    return 1
  IO.FS.writeFile file updated
  IO.println s!"{file}: migrated {edits.size} reference(s)"
  return 0

/-!
## C. Command line interface
-/

/-- Collect library roots and submodules, including files not yet imported by a root module. -/
def modulesInLibrary (lib : Lake.LeanLib) : IO (Array Lake.Module) := do
  let (_, modules) ← StateT.run (s := #[]) do
    let add := fun name => do
      let mod : Lake.Module := { lib, name }
      if ← mod.leanFile.pathExists then
        unless (← get).contains mod do modify (·.push mod)
    for glob in lib.roots.map Lake.Glob.andSubmodules ++ lib.config.globs do
      match glob with
      | .one name => add name
      | .submodules name | .andSubmodules name =>
        if glob == Lake.Glob.andSubmodules name then add name
        let dir := modToFilePath lib.srcDir name ""
        if ← dir.isDir then
          forEachModuleInDir dir fun suffix => add (name ++ suffix)
  return modules

/-- Read the root package's libraries from Lake, respecting source directories and globs. -/
def libraryModules (names : List String) : IO (Array Lake.Module) := do
  let (elanInstall?, leanInstall?, lakeInstall?) ← Lake.findInstall?
  let config ← Lake.MonadError.runEIO <|
    Lake.mkLoadConfig { elanInstall?, leanInstall?, lakeInstall? }
  let some workspace ← Lake.loadWorkspace config |>.toBaseIO
    | throw <| IO.userError "Failed to load the Lake workspace."
  let libraries := workspace.root.leanLibs
  for name in names do
    unless libraries.any (·.name.toString == name) do
      throw <| IO.userError s!"Unknown top-level lean_lib: {name}. Available: \
        {", ".intercalate (libraries.toList.map (·.name.toString))}"
  let mut modules := #[]
  for lib in libraries do
    if names.isEmpty || names.contains lib.name.toString then
      for mod in (← modulesInLibrary lib) do
        unless modules.contains mod do modules := modules.push mod
  return modules.qsort fun a b => a.name.toString < b.name.toString

/-- Run each file in its own worker process and propagate failures. -/
def run (args : List String) : IO UInt32 := do
  let modules ← libraryModules args
  let executable ← IO.appPath
  let mut failures := 0
  for (mod, index) in modules.toList.zipIdx do
    let file := mod.leanFile
    IO.eprintln s!"[{index + 1}/{modules.size}] {file}"
    let child ← IO.Process.spawn {
      cmd := executable.toString, args := #["--worker", file.toString, mod.name.toString] }
    if (← child.wait) != 0 then failures := failures + 1
  IO.println s!"Checked {modules.size} file(s); {failures} failed."
  return if failures == 0 then 0 else 1

end Migrate

/-- Migrate all top-level libraries, or only the named libraries supplied as arguments. -/
unsafe def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["--help"] =>
      IO.println "Usage: lake exe migrate [LEAN_LIB ...]"
      IO.println "Defaults to every top-level lean_lib in the Lake configuration."
      IO.println "Build imports first."
      return 0
    | ["--worker", file, mod] => Migrate.migrateFile file mod.toName
    | _ => Migrate.run args
  catch e =>
    IO.eprintln s!"migrate: {e}"
    return 1
