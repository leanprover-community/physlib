/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Lean.Expr.Basic
import ImportGraph.Imports.RequiredModules
/-!

## Basic Lean meta programming commands

-/

/-- The size of a flattened array of arrays. -/
def Array.flatSize {α} : Array (Array α) → Nat :=
  foldl (init := 0) fun sizeAcc as => sizeAcc + as.size

/-- The size of a flattened array of arrays after applying an element-wise filter. -/
def Array.flatFilterSizeM {α m} [Monad m] (p : α → m Bool) : Array (Array α) → m Nat :=
  foldlM (init := 0) fun sizeAcc as => return sizeAcc + (← as.filterM p).size

open Lean

/-!

## Imports

-/

/-- Gets all imports within PhysLean. -/
def PhysLean.allImports : IO (Array Import) := do
  initSearchPath (← findSysroot)
  let mods := `PhysLean
  let mFile ← findOLean mods
  unless ← mFile.pathExists do
    throw <| IO.userError s!"object file '{mFile}' of module {mods} does not exist"
  let (hepLeanMod, _) ← readModuleData mFile
  hepLeanMod.imports.filterM fun c => return c.module != `Init

/-- Number of files within PhysLean. -/
def PhysLean.noImports : IO Nat := do
  let imports ← allImports
  return imports.size

/-- Gets all constants from an import. -/
def PhysLean.Imports.getConsts (imp : Import) : IO (Array ConstantInfo) := do
  let mFile ← findOLean imp.module
  let (modData, _) ← readModuleData mFile
  return modData.constants

/-- Gets all user defined constants from an import. -/
def PhysLean.Imports.getUserConsts (imp : Import) : CoreM (Array ConstantInfo) := do
  let env ← getEnv
  let consts ← Imports.getConsts imp
  consts.filterM fun c =>
    let name := c.name
    return !name.isInternal
      && !isCasesOnRecursor env name
      && !isRecOnRecursor env name
      && !isNoConfusion env name
      && !isBRecOnRecursor env name
      && !isAuxRecursorWithSuffix env name brecOnSuffix
      && !isAuxRecursorWithSuffix env name belowSuffix
      && !isAuxRecursorWithSuffix env name belowSuffix
      /- Removing syntax category declarations. -/
      && name.toString != "TensorTree.indexExprTT.quot"
      && name.toString != "TensorTree.tensorExprTT.quot"

/-- Turns a name into a system file path. -/
def Lean.Name.toFilePath (c : Name) : System.FilePath :=
  System.mkFilePath (c.toString.splitOn ".") |>.addExtension "lean"

/-- Lines from import. -/
def PhysLean.Imports.getLines (imp : Import) : IO (Array String) := do
  IO.FS.lines imp.module.toFilePath

namespace Lean.Name
/-!

## Name

-/

variable {m} [Monad m] [MonadEnv m] [MonadLiftT BaseIO m]

/-- Turns a name into a Lean file. -/
def toRelativeFilePath (c : Name) : System.FilePath :=
  System.FilePath.join "." c.toFilePath

/-- Turns a name, which represents a module, into a link to github. -/
def toGitHubLink (c : Name) (line : Nat) : String :=
  s!"https://github.com/HEPLean/PhysLean/blob/master/{c.toFilePath}#L{line}"

/-- Given a name, returns the line number. -/
def lineNumber (c : Name) : m Nat := do
  match ← findDeclarationRanges? c with
  | some decl => return decl.range.pos.line
  | none => panic! s!"{c} is a declaration without position"

/-- Given a name, returns the file name corresponding to that declaration. -/
def fileName (c : Name) : m Name := do
  let env ← getEnv
  match env.getModuleFor? c with
  | some decl => return decl
  | none => panic! s!"{c} is a declaration without position"

/-- Returns the location of a name. -/
def location (c : Name) : m String := do
  let env ← getEnv
  match env.getModuleFor? c with
  | some decl => return s!"{decl.toRelativeFilePath}:{← c.lineNumber} {c}"
  | none => panic! s!"{c} is a declaration without position"

/-- Determines if a name has a location. -/
def hasPos (c : Name) : m Bool := do
  let ranges? ← findDeclarationRanges? c
  return ranges?.isSome

/-- Determines if a name has a doc string. -/
def hasDocString (c : Name) : CoreM Bool := do
  let env ← getEnv
  let doc? ← findDocString? env c
  return doc?.isSome

/-- The doc string from a name. -/
def getDocString (c : Name) : CoreM String := do
  let env ← getEnv
  let doc? ← findDocString? env c
  return doc?.getD ""

/-- Given a name, returns the source code defining that name, including doc strings. -/
def getDeclString (name : Name) : CoreM String := do
  let env ← getEnv
  match ← findDeclarationRanges? name with
  | some { range := { pos, endPos, .. }, .. } =>
    match env.getModuleFor? name with
    | some fileName =>
      let fileContent ← IO.FS.readFile fileName.toRelativeFilePath
      let fileMap := fileContent.toFileMap
      return (String.Pos.Raw.extract fileMap.source)
        (fileMap.ofPosition pos) (fileMap.ofPosition endPos)
    | none => return ""
  | none => return ""

/-- Given a name, returns the source code defining that name,
  starting with the def ... or lemma... etc. -/
def getDeclStringNoDoc (name : Name) : CoreM String := do
  let declarationString ← getDeclString name
  let headerLine (line : String) : Bool :=
    line.startsWith "def " ∨ line.startsWith "lemma " ∨ line.startsWith "inductive "
    ∨ line.startsWith "structure " ∨ line.startsWith "theorem "
    ∨ line.startsWith "instance " ∨ line.startsWith "abbrev " ∨
    line.startsWith "noncomputable def " ∨ line.startsWith "noncomputable abbrev "
  let lines := declarationString.splitOn "\n"
  match lines.findIdx? headerLine with
  | none => panic! s!"{name} has no header line"
  | some i => return String.intercalate "\n" (lines.drop i)

end Lean.Name

namespace PhysLean

/-- Number of definitions. -/
def noDefs : CoreM Nat := do
  let imports ← PhysLean.allImports
  let x ← imports.mapM PhysLean.Imports.getUserConsts
  x.flatFilterSizeM fun c => return c.isDef && (← c.name.hasPos)

/-- Number of definitions. -/
def noLemmas : CoreM Nat := do
  let imports ← PhysLean.allImports
  let x ← imports.mapM PhysLean.Imports.getUserConsts
  x.flatFilterSizeM fun c => return !c.isDef && (← c.name.hasPos)

/-- All docstrings present in PhysLean. -/
def allDocStrings : CoreM (Array String) := do
  let imports ← PhysLean.allImports
  let x ← imports.mapM PhysLean.Imports.getUserConsts
  let x' := x.flatten
  let docString ← x'.mapM fun c => Lean.Name.getDocString c.name
  return docString

/-- Number of definitions without a doc-string. -/
def noDefsNoDocString : CoreM Nat := do
  let imports ← PhysLean.allImports
  let x ← imports.mapM PhysLean.Imports.getUserConsts
  x.flatFilterSizeM fun c =>
    return c.isDef && (← c.name.hasPos) && !(← c.name.hasDocString)

/-- Number of definitions without a doc-string. -/
def noLemmasNoDocString : CoreM Nat := do
  let imports ← PhysLean.allImports
  let x ← imports.mapM PhysLean.Imports.getUserConsts
  x.flatFilterSizeM fun c =>
    return !c.isDef && (← c.name.hasPos) && !(← c.name.hasDocString)

/-- The number of lines in PhysLean. -/
def noLines : IO Nat := do
  let imports ← PhysLean.allImports
  let x ← imports.mapM PhysLean.Imports.getLines
  return x.flatSize

/-- The number of TODO items. -/
def noTODOs : IO Nat := do
  let imports ← PhysLean.allImports
  let x ← imports.mapM PhysLean.Imports.getLines
  x.flatFilterSizeM fun l => return l.startsWith "TODO "

/-- The number of files with a TODO item. -/
def noFilesWithTODOs : IO Nat := do
  let imports ← PhysLean.allImports
  let x ← imports.mapM PhysLean.Imports.getLines
  let x := x.filter fun bs => bs.any fun l => l.startsWith "TODO "
  return x.size

/-- All user defined declarations. -/
def allUserConsts : CoreM (Array ConstantInfo) := do
  let imports ← PhysLean.allImports
  return (← imports.flatMapM PhysLean.Imports.getUserConsts)

end PhysLean
