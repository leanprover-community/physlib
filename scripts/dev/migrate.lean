/-
Copyright (c) 2026 Physlib contributors. All rights reserved.
Released under Apache 2.0 license.
Authors: Physlib contributors
-/
import Lean
import Lean.Server.References
import Lake.CLI.Main

/-!
# Migrating deprecated declarations
Replace references to deprecated declarations with their declared alternatives.

## i. Overview

`lake exe migrate` processes every top-level `lean_lib` in the Lake configuration.
`lake exe migrate Physlib` processes only the library named `Physlib`. Imports must be built.
References are read from the latest local build's `.ilean` file, including restored cache data,
when its build trace matches the source and reference file hashes. Missing or stale build data
falls back to elaboration. Comments, strings, and local variables are preserved.
Deprecations with only a prose message are left alone. Each changed file is elaborated
before being written; failures leave that file untouched and produce a nonzero exit status.
Field notation is migrated when the replacement stays in the same namespace; other field
notation requires a manual rewrite and is reported. Each file runs in a separate process so
imported environments are released between files.

## ii. Key results

* `Migrate.collectEdit` identifies references using Lean's deprecation attribute.
* `Migrate.cachedEdits?` reuses resolved references from a matching build or restored cache.
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

/-- Verify a restored artifact against Lake's current input hash without building any source. -/
def restoredCacheMatches (mod : Name) (saved : Json) : IO Bool := do
  let expected ← IO.ofExcept <| saved.getObjValAs? Lake.Hash "depHash"
  let output ← IO.Process.output {
    cmd := "lake"
    args := #["--quiet", "--no-build", "--no-cache", "--rehash", "--json",
      "query", s!"+{mod}:depHash"] }
  if output.exitCode != 0 then return false
  let actual ← IO.ofExcept <| Json.parse output.stdout >>= fromJson? (α := Lake.Hash)
  return actual == expected

/-- Check that a saved build's source and reference hashes match the files being used. -/
def cacheMatches (file : FilePath) (mod : Name) (ilean trace : FilePath) : IO Bool := do
  let saved ← IO.ofExcept <| Json.parse (← IO.FS.readFile trace)
  let inputs ← IO.ofExcept <| saved.getObjValAs? (Array (String × Json)) "inputs"
  let matchesSource ← if inputs.isEmpty then restoredCacheMatches mod saved else do
    let sourceHash ← Lake.computeFileHash file (text := true)
    pure <| inputs.any fun (caption, value) =>
      caption.endsWith ".lean" && (fromJson? (α := Lake.Hash) value).toOption == some sourceHash
  unless matchesSource do return false
  let output ← IO.ofExcept <| saved.getObjVal? "outputs" >>= (·.getObjValAs? String "i")
  return output == s!"{(← Lake.computeFileHash ilean).hex}.ilean"

/-- Index imported deprecations by the escaped names stored in `.ilean` references. -/
def cachedReplacements (env : Environment) : Std.HashMap String (Name × Name) := Id.run do
  let mut result := ∅
  for index in [:env.header.moduleNames.size] do
    for (name, _) in Linter.deprecatedAttr.ext.getModuleEntries env index do
      if let some next := replacement? env name then
        result := result.insert name.toString (name, next)
  return result

/-- Read resolved references from a compatible build, without elaborating the source. -/
unsafe def cachedEdits? (file : FilePath) (mod : Name) (source : String)
    (ilean trace : FilePath) : IO (Option (Array Edit)) := do
  unless (← ilean.pathExists) && (← trace.pathExists) do return none
  try
    unless ← cacheMatches file mod ilean trace do
      IO.eprintln s!"{file}: cached source or reference hash differs; using elaboration"
      return none
    let saved ← Server.Ilean.load ilean
    unless saved.version == 5 && saved.module == mod do return none
    enableInitializersExecution
    let env ← importModules #[{ module := mod }] {} (loadExts := true)
    let replacements := cachedReplacements env
    let fileMap := FileMap.ofString source
    let mut edits := #[]
    for (ident, refs) in saved.references do
      let .const _ name := ident | continue
      let some (old, next) := replacements[name]? | continue
      -- Private names need the local context available in an elaborated info tree.
      if isPrivateName old || isPrivateName next then return none
      for usage in refs.usages do
        let range := fileMap.lspRangeToUtf8Range usage.range
        let written := (Substring.Raw.mk source range.start range.stop).toString
        let .ok stx := Parser.runParserCategory env `term written | return none
        unless stx.isIdent do return none
        let before := (Substring.Raw.mk source 0 range.start).toString
        let isField := before.endsWith "."
        if isField && old.getPrefix != next.getPrefix then return none
        let text := if isField then
            (Name.mkSimple next.getString!).toString
          else
            -- Cached references do not store local variables or namespace scopes.
            ((`_root_).append next).toString
        let edit := { range, text : Edit }
        unless edits.contains edit do edits := edits.push edit
    return some edits
  catch error =>
    IO.eprintln s!"{file}: cannot use cached references ({error}); using elaboration"
    return none

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

/-- Find replacements using a matching build or elaboration, checking edits before writing. -/
unsafe def migrateFile (file : FilePath) (mod : Name)
    (ilean trace : FilePath) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let source ← IO.FS.readFile file
  let cached? ← cachedEdits? file mod source ilean trace
  let (edits, messages) ← match cached? with
    | some edits => pure (edits, {})
    | none => elaborate file mod source
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
  let method := if cached?.isSome then "cached references" else "elaboration"
  IO.println s!"{file}: migrated {edits.size} reference(s) using {method}"
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
      cmd := executable.toString
      args := #["--worker", file.toString, mod.name.toString,
        mod.ileanFile.toString, mod.traceFile.toString] }
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
    | ["--worker", file, mod, ilean, trace] =>
      Migrate.migrateFile file mod.toName ilean trace
    | _ => Migrate.run args
  catch e =>
    IO.eprintln s!"migrate: {e}"
    return 1
