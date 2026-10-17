/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Physlib.Meta.Basic
import Physlib.Meta.TODO.Basic
import Mathlib.Lean.CoreM
import Physlib.Meta.Informal.Post
import Physlib.Meta.Informal.SemiFormal
import Physlib.Meta.Linters.Sorry
/-!

# Creates TODO yml file from the TODO items.

The TODO yml file is used to generate the TODO list for the website.
This lean file collects the TODOs and generates the YML file.

It collects the following TODO items:
- TODO items `TODO ...`.
- Informal definitions and lemmas.
- Semi-formal results.
- Sorryful results.

-/

open Lean System Meta Physlib


/-!

## Physlib categories.

To be moved.

-/
inductive PhyslibCategory
  | ClassicalMechanics
  | CondensedMatter
  | Cosmology
  | Elctromagnetism
  | Mathematics
  | Meta
  | Optics
  | Particles
  | QFT
  | QuantumMechanics
  | Relativity
  | StringTheory
  | StatisticalMechanics
  | Thermodynamics
  | QuantumInfo
  | PhyslibAlpha
  | Other
deriving BEq, DecidableEq

def PhyslibCategory.string :  PhyslibCategory → String
  | ClassicalMechanics => "Classical Mechanics"
  | CondensedMatter => "Condensed Matter"
  | Cosmology => "Cosmology"
  | Elctromagnetism => "Electromagnetism"
  | Mathematics => "Mathematics"
  | Meta => "Meta"
  | Optics => "Optics"
  | Particles => "Particles"
  | QFT => "QFT"
  | QuantumMechanics => "Quantum Mechanics"
  | Relativity => "Relativity"
  | StringTheory => "String Theory"
  | StatisticalMechanics => "Statistical Mechanics"
  | Thermodynamics => "Thermodynamics"
  | QuantumInfo => "Quantum Information"
  | PhyslibAlpha => "Physlib Alpha"
  | Other => "Other"

def PhyslibCategory.emoji : PhyslibCategory → String
  | ClassicalMechanics => "⚙️"
  | CondensedMatter => "🧊"
  | Cosmology => "🌌"
  | Elctromagnetism => "⚡"
  | Mathematics => "➗"
  | Meta => "🏛️"
  | Optics => "🔍"
  | Particles => "💥"
  | QFT => "🌊"
  | QuantumMechanics => "⚛️"
  | Relativity => "⏳"
  | StringTheory => "🧵"
  | StatisticalMechanics => "🎲"
  | Thermodynamics => "🔥"
  | QuantumInfo => "💻"
  | PhyslibAlpha => "🧪"
  | Other => "❓"

def PhyslibCategory.List :  List PhyslibCategory :=
  [ PhyslibCategory.ClassicalMechanics,
    PhyslibCategory.CondensedMatter,
    PhyslibCategory.Cosmology,
    PhyslibCategory.Elctromagnetism,
    PhyslibCategory.Mathematics,
    PhyslibCategory.Meta,
    PhyslibCategory.Optics,
    PhyslibCategory.Particles,
    PhyslibCategory.QFT,
    PhyslibCategory.QuantumMechanics,
    PhyslibCategory.Relativity,
    PhyslibCategory.StringTheory,
    PhyslibCategory.StatisticalMechanics,
    PhyslibCategory.Thermodynamics,
    PhyslibCategory.QuantumInfo,
    PhyslibCategory.PhyslibAlpha,
    PhyslibCategory.Other]

instance : ToString PhyslibCategory where
  toString := PhyslibCategory.string

def PhyslibCategory.ofFileName (n : Name) : PhyslibCategory :=
  let s : String := n.toString
  if s.startsWith "Physlib.ClassicalMechanics"  then
    PhyslibCategory.ClassicalMechanics
  else if s.startsWith "Physlib.CondensedMatter" then
    PhyslibCategory.CondensedMatter
  else if s.startsWith "Physlib.Cosmology" then
    PhyslibCategory.Cosmology
  else if s.startsWith "Physlib.Electromagnetism" then
    PhyslibCategory.Elctromagnetism
  else if s.startsWith "Physlib.Mathematics" then
    PhyslibCategory.Mathematics
  else if s.startsWith "Physlib.Meta" then
    PhyslibCategory.Meta
  else if s.startsWith "Physlib.Optics" then
    PhyslibCategory.Optics
  else if s.startsWith "Physlib.Particles" then
    PhyslibCategory.Particles
  else if s.startsWith "Physlib.QFT" then
    PhyslibCategory.QFT
  else if s.startsWith "Physlib.QuantumMechanics" then
    PhyslibCategory.QuantumMechanics
  else if s.startsWith "Physlib.Relativity" then
    PhyslibCategory.Relativity
  else if s.startsWith "Physlib.StatisticalMechanics" then
    PhyslibCategory.StatisticalMechanics
  else if s.startsWith "Physlib.Thermodynamics" then
    PhyslibCategory.Thermodynamics
  else if s.startsWith "Physlib.QuantumInfo" then
    PhyslibCategory.QuantumInfo
  else if s.startsWith "PhyslibAlpha" then
    PhyslibCategory.PhyslibAlpha
  else
    PhyslibCategory.Other

/-########################-/

/-!

## FullTODOInfo

-/

structure FullTODOInfo where
  content : String
  fileName : Name
  name : Name
  line : Nat
  isInformalDef : Bool
  isInformalLemma : Bool
  isSemiFormalResult : Bool
  isSorryfulResult : Bool := false
  category : PhyslibCategory
  tag : String

/-- Converts a `FullTODOInfo` to an entry in a YAML code. -/
def FullTODOInfo.toYAML (todo : FullTODOInfo) : MetaM String := do
  let content := todo.content
  let contentIndent := content.replace "\n" "\n      "
  return s!"
  - file: {todo.fileName}
    githubLink: {Name.toGitHubLink todo.fileName todo.line}
    line: {todo.line}
    isInformalDef: {todo.isInformalDef}
    isInformalLemma: {todo.isInformalLemma}
    isSemiFormalResult: {todo.isSemiFormalResult}
    isSorryfulResult: {todo.isSorryfulResult}
    category: {todo.category}
    name: {todo.name}
    tag: {todo.tag}
    content: |
      {contentIndent}"

/-!

## TODO items

-/

def FullTODOInfo.ofTODO (t : todoInfo) : FullTODOInfo :=
  {content := t.content, fileName := t.fileName, line := t.line, name := t.fileName,
   isInformalDef := false, isInformalLemma := false,
   isSemiFormalResult := false, category := PhyslibCategory.ofFileName t.fileName,
   tag := t.tag}

unsafe def getTodoInfo : MetaM (Array FullTODOInfo) := do
  let env ← getEnv
  let todoInfo := (todoExtension.getState env)
  -- pure (todoInfo.qsort (fun x y => x.fileName.toString < y.fileName.toString)).toList
  pure (todoInfo.map FullTODOInfo.ofTODO)

/-!

## Informal lemmas and definitions

-/

unsafe def informalTODO (x : ConstantInfo) : CoreM FullTODOInfo := do
  let name := x.name
  let tag ← Informal.getTag x
  let lineNo ← Name.lineNumber name
  let docString ← Name.getDocString name
  let file ← Name.fileName name
  let isInformalDef := Informal.isInformalDef x
  let isInformalLemma := Informal.isInformalLemma x
  let category := PhyslibCategory.ofFileName file
  return {content := docString, fileName := file, line := lineNo, name := name,
          isInformalDef := isInformalDef, isInformalLemma := isInformalLemma,
          isSemiFormalResult := false, category := category,
          tag := tag}

unsafe def allInformalTODO : CoreM (Array FullTODOInfo) := do
  let x ← AllInformal
  x.mapM informalTODO

/-!

## Semi-formal results

-/

def FullTODOInfo.ofSemiFormal (t : WantedInfo) : FullTODOInfo :=
  {content := t.content, fileName := t.fileName, line := t.line, name := t.name,
   isInformalDef := false, isInformalLemma := false,
   isSemiFormalResult := true, category := PhyslibCategory.ofFileName t.fileName,
   tag := t.tag}

unsafe def allSemiInformal  : CoreM (Array FullTODOInfo) := do
  let env ← getEnv
  let semiInformalInfos := (wantedExtension.getState env)
  pure (semiInformalInfos.map FullTODOInfo.ofSemiFormal)

/-!

## Sorryful results
-/

def SorryfulInfo.toFullTODOInfo (s : SorryfulInfo) : FullTODOInfo where
  content := s.docstring
  fileName := s.fileName
  line := s.line
  name := s.name
  isInformalDef := false
  isInformalLemma := false
  isSemiFormalResult := false
  isSorryfulResult := true
  category := PhyslibCategory.ofFileName s.fileName
  tag := s.name.toString

unsafe def allSorryfulResults  : CoreM (Array FullTODOInfo) := do
  let env ← getEnv
  let sorryfulInfos := (sorryfulExtension.getState env)
  pure (sorryfulInfos.map SorryfulInfo.toFullTODOInfo)

/-!

## All TODOs

Collecting all of the TODO items

-/

unsafe def allTODOs : MetaM (List FullTODOInfo) := do
  let todos ← getTodoInfo
  let informalTODOs ← allInformalTODO
  let semiInformal ← allSemiInformal
  let sorryfulResults ← allSorryfulResults
  let all := todos ++ informalTODOs ++ semiInformal ++ sorryfulResults
  return  (all.qsort (fun x y => x.fileName.toString < y.fileName.toString
    ∨ (x.fileName.toString = y.fileName.toString ∧ x.line < y.line))).toList


/-!

## Creating the YAML file

-/
unsafe def categoriesToYML : MetaM String := do
  let todos ← allTODOs
  let mut cat := "Category:\n"
  for c in PhyslibCategory.List do
    let num := (todos.filter (fun x => x.category == c)).length
    cat := cat ++
    s!"
  - name: \"{c}\"
    num: {num}
    emoji: \"{c.emoji}\""
  return cat ++ "\n"

unsafe def todosToYAML : MetaM String := do
  let todos ← allTODOs
  /- Check no duplicate tags-/
  let tags := todos.map (fun x => x.tag)
  if !tags.Nodup then
    let duplicates := tags.filter (fun tag => tags.count tag > 1) |>.eraseDups
    println! duplicates
    panic! s!"Duplicate tags found: {duplicates}"
  /- End of check. -/
  let todosYAML ← todos.mapM FullTODOInfo.toYAML
  return "TODOItem:\n" ++ String.intercalate "\n" todosYAML

unsafe def fullTODOYML : MetaM String := do
  let cat ← categoriesToYML
  let todos ← todosToYAML
  return cat ++ todos

/-!

## Main function

-/

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  Lean.enableInitializersExecution
  println! "Generating TODO list."
  let env ← importModules (loadExts := true) #[`Physlib, `QuantumInfo, `PhyslibAlpha] {} 0
  let fileName := ""
  let options : Options := {}
  let ctx : Core.Context := {fileName, options, fileMap := default }
  let state := {env}
  let ymlString' ← (Lean.Core.CoreM.toIO · ctx state) do (fullTODOYML).run'
  let ymlString := ymlString'.1
  println! ymlString
  let fileOut : System.FilePath := {toString := "./docs/_data/TODO.yml"}
  if "mkFile" ∈ args then
    IO.println (s!"TODOList file made.")
    -- Create directory if it doesn't exist
    let dir : System.FilePath := {toString := "./docs/_data"}
    if !(← System.FilePath.pathExists dir) then
      IO.FS.createDirAll dir
    IO.FS.writeFile fileOut ymlString
  pure 0
