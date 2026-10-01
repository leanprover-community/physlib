/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Lean
/-!

# The `ForMathlib` linter

The directory `Physlib/Mathematics/ForMathlib/` holds results which are not yet in Mathlib, and
are kept in Physlib only until they are upstreamed. This linter checks two properties of that
directory:

1. No file in `ForMathlib` imports a module of `Physlib`, `PhyslibAlpha` or `QuantumInfo` from
   outside `ForMathlib`. Imports from Mathlib, Batteries, Lean, etc. are allowed. This ensures that
   every file in `ForMathlib` can be upstreamed without the rest of Physlib.
2. Every file in `ForMathlib` is used outside of `ForMathlib`: it is imported, either directly or
   through other files in `ForMathlib`, by a file in `Physlib`, `PhyslibAlpha` or `QuantumInfo`
   which is not itself in `ForMathlib`. The library root files such as `Physlib.lean` do not
   count as uses.

The linter only reads the import headers of files, so it does not need a build.

It can be run from the terminal using
`lake exe forMathlib_lint`.

-/

open Lean System

/-- The module name prefix of the files in `Physlib/Mathematics/ForMathlib/`. -/
def forMathlibPrefix : Name := `Physlib.Mathematics.ForMathlib

/-- The library directories whose files are read by the linter. -/
def libraryDirs : List String := ["Physlib", "PhyslibAlpha", "QuantumInfo"]

/-- Whether a module lives in `Physlib/Mathematics/ForMathlib/`. -/
def isForMathlib (n : Name) : Bool := forMathlibPrefix.isPrefixOf n

/-- Whether a module lives in one of the libraries `Physlib`, `PhyslibAlpha` or `QuantumInfo`. -/
def isLibraryModule (n : Name) : Bool := libraryDirs.any fun dir => dir.toName.isPrefixOf n

/-- The module name of a `.lean` file, given its path relative to the repository root. -/
def moduleNameOfPath (path : FilePath) : Name :=
  (path.withExtension "").components.foldl (fun n c => n.str c) .anonymous

/-- The modules of `libraryDirs`, each paired with the modules of `libraryDirs` it imports. -/
def libraryImports : IO (Array (Name × Array Name)) := do
  let mut result := #[]
  for dir in libraryDirs do
    let paths ← FilePath.walkDir dir
    for path in paths.filter (·.extension == some "lean") do
      let contents ← IO.FS.readFile path
      let (imports, _, _) ← Elab.parseImports contents path.toString
      let libImports := (imports.map (·.module)).filter isLibraryModule
      result := result.push (moduleNameOfPath path, libImports)
  return result

/-- The pairs `(m, i)` of a module `m` in `ForMathlib` importing a module `i` of `libraryDirs`
  which is not in `ForMathlib`. -/
def outsideImports (graph : Array (Name × Array Name)) : Array (Name × Name) := Id.run do
  let mut result := #[]
  for (m, imps) in graph.filter (isForMathlib ·.1) do
    for i in imps.filter (! isForMathlib ·) do
      result := result.push (m, i)
  return result

/-- The modules in `ForMathlib` which are not imported, directly or through other modules in
  `ForMathlib`, by any module outside of `ForMathlib`. -/
def unusedModules (graph : Array (Name × Array Name)) : Array Name := Id.run do
  let importsOf : NameMap (Array Name) :=
    graph.foldl (fun acc (m, imps) => acc.insert m imps) {}
  -- The modules in `ForMathlib` imported directly from outside of `ForMathlib`.
  let mut todo : Array Name := #[]
  for (_, imps) in graph.filter (! isForMathlib ·.1) do
    todo := todo ++ imps.filter isForMathlib
  -- Close under the imports of modules in `ForMathlib`.
  let mut used : NameSet := {}
  while h : todo.size > 0 do
    let m := todo[todo.size - 1]
    todo := todo.pop
    unless used.contains m do
      used := used.insert m
      todo := todo ++ ((importsOf.find? m).getD #[]).filter isForMathlib
  return (graph.map (·.1)).filter fun m => isForMathlib m && ! used.contains m

/-- Sorts an array of names alphabetically. -/
def sortNames (ns : Array Name) : Array Name := ns.qsort (·.toString < ·.toString)

/-- Runs both checks, printing any violations, and returns `1` if there are any. -/
def main : IO UInt32 := do
  let graph ← libraryImports
  let outside := (outsideImports graph).qsort fun a b => a.1.toString < b.1.toString
  let unused := sortNames (unusedModules graph)
  let forMathlibCount := (graph.filter (isForMathlib ·.1)).size
  if outside.size > 0 then
    IO.println s!"\x1b[31mError: Files in `{forMathlibPrefix}` must only import files \
      from within `{forMathlibPrefix}`:\x1b[0m"
    for (m, i) in outside do
      IO.println s!"  {m} imports {i}"
  if unused.size > 0 then
    IO.println s!"\x1b[31mError: Files in `{forMathlibPrefix}` must be used outside of \
      `{forMathlibPrefix}`. The following are not:\x1b[0m"
    for m in unused do
      IO.println s!"  {m}"
  if outside.size > 0 || unused.size > 0 then
    return 1
  IO.println s!"\x1b[32mAll {forMathlibCount} files in `{forMathlibPrefix}` import only from \
    `{forMathlibPrefix}` and are used outside of it.\x1b[0m"
  return 0
