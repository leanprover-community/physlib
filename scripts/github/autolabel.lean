/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Copyright (c) 2026 Shlok Vaibhav. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, Damiano Testa, Shlok Vaibhav

Adapted from mathlib4 `scripts/autolabel.lean`.
Modified for PhysLean repository labels and paths.
-/

import Lean.Elab.Command

/-!
# Automatic labelling of PRs

This file contains the script to automatically assign a GitHub label to a PR.

## Label definition

The mapping from GitHub labels to Physlib folders is done in this file and
needs to be updated here if necessary:

* `AutoLabel.physlibLabels` contains an assignment of GitHub labels to folders inside
  the physlib repository. If no folder is specified, a label like `t-quantum-mechanics` will be
  interpreted as matching the folder `"Physlib" / "QuantumMechanics"`.
* The `PhyslibAlpha` label is exclusive: it is only added when every modified file lies in
  `PhyslibAlpha/` or is `PhyslibAlpha.lean`.
* `AutoLabel.physlibUnlabelled` contains subfolders of `Physlib/` which are deliberately
  left without topic label.

## lake exe autolabel

`lake exe autolabel` uses `git diff --name-only origin/master...HEAD` to determine which
files have been modified and then finds all labels which should be added based on these changes.
These are printed for testing purposes.

`lake exe autolabel [NUMBER]` will further try to add the applicable labels
to the PR specified. This requires the **GitHub CLI** `gh` to be installed!

The script can add up to `MAX_LABELS` labels (defined below).
If more than `MAX_LABELS` labels would be applicable, nothing happens.

## Workflow

There is a physlib workflow `.github/workflows/add_label_from_diff.yaml` which executes
this script automatically.

Currently it is set to run only one time when a PR is created.

## Tests

Additionally, the script does a few consistency checks:

- it ensures all paths in specified in `AutoLabel.physlibLabels` exist
- It makes sure all subfolders of `Physlib/` belong to at least one label.
  There is `AutoLabel.physlibUnlabelled` to add exceptions for this test.

-/
open Lean System

namespace AutoLabel

/-! 1. An inductive class `Label` is defined to contain all permissible labels
    2. A function `Label.toString` is defined to convert a `Label` to its string
    3. A structure `LabelData` is defined to contain the directories, exclusions, and dependencies for each label
       (exclusions and dependencies are currently empty)
    4. A function `physlibLabelData` is defined to map each LabelData structure
       to its corresponding `LabelData` fields (i.e. directories, exclusions, and dependencies)
    5. Physlibunlabelled and quantuminfoUnlabelled are defined to contain the paths which are not
    covered by any label (empty for now)
    6. A function `getMatchingLabels` is defined to return all labels in `physlibLabels` which match
       folder for at least one of the modified files.
    7. A function `dropDependentLabels` is defined to reduce a list of labels to not include any
       which are dependencies of other labels in the list.

    Then a section Test is defined to :

    1. Few guards are defined to test the functionality of the declarations defined above
    2. A function `findUncoveredPaths` is defined to ensure the labels defined in `physlibLabels`
       cover all subfolders of `Physlib/` and `QuantumInfo/`.

    Then the github routine is defined:

    1. A function `githubAnnotation` is defined to create a message which GitHub CI parses as
    annotation and displays at the specified file.

    2. IO AutoLabel command is opened to define the main function which takes in a list of
    arguments and returns an IO UInt32. This is the function run during github action.

-/


/-- Maximal number of labels which can be added. If more are applicable, nothing will be added. -/
def MAX_LABELS := 1

/-- Physlib's Github topic labels -/
inductive Label where
  -- Physlib
  | «t-classical-field-theory»
  | «t-classical-mechanics»
  | «t-condensed-matter»
  | «t-cosmology»
  | «t-electromagnetism»
  | «t-fluid-dynamics»
  | «t-mathematics»
  | «t-meta»
  | «t-optics»
  | «t-particles»
  | «t-qft»
  | «t-quantum-mechanics»
  | «t-relativity»
  | «t-space-and-time»
  | «t-statistical-mechanics»
  | «t-string-theory»
  | «t-thermodynamics»
  | «t-units»

  -- QuantumInfo
  | «t-capacity-qi»
  | «t-channels-qi»
  | «t-classical-info-qi»
  | «t-entropy-qi»
  | «t-for-mathlib-qi»
  | «t-measurements-qi»
  | «t-operators-qi»
  | «t-resource-theory-qi»
  | «t-states-qi»
  | «CI»

  -- PhyslibAlpha
  | «PhyslibAlpha»

  deriving BEq, Hashable, Repr

def physlibLabels : Array Label := #[
  .«t-classical-field-theory», .«t-classical-mechanics», .«t-condensed-matter», .«t-cosmology»,
  .«t-electromagnetism», .«t-fluid-dynamics», .«t-mathematics», .«t-meta», .«t-optics»,
  .«t-particles», .«t-qft», .«t-quantum-mechanics», .«t-relativity»,
  .«t-space-and-time», .«t-statistical-mechanics», .«t-string-theory», .«t-thermodynamics»,
  .«t-units», .«t-capacity-qi», .«t-channels-qi», .«t-classical-info-qi», .«t-entropy-qi»,
  .«t-for-mathlib-qi», .«t-measurements-qi», .«t-operators-qi», .«t-resource-theory-qi», .«t-states-qi»,
  .«CI», .«PhyslibAlpha»
]


def Label.toString : Label → String
  | .«t-classical-field-theory»                    => "t-classical-field-theory"
  | .«t-classical-mechanics»         => "t-classical-mechanics"
  | .«t-condensed-matter»         => "t-condensed-matter"
  | .«t-cosmology»                   => "t-cosmology"
  | .«t-electromagnetism»            => "t-electromagnetism"
  | .«t-fluid-dynamics»            => "t-fluid-dynamics"
  | .«t-mathematics»              => "t-mathematics"
  | .«t-meta»                       => "t-meta"
  | .«t-optics»                     => "t-optics"
  | .«t-particles»                  => "t-particles"
  | .«t-qft»                        => "t-qft"
  | .«t-quantum-mechanics»          => "t-quantum-mechanics"
  | .«t-relativity»                => "t-relativity"
  | .«t-space-and-time»             => "t-space-and-time"
  | .«t-statistical-mechanics»      => "t-statistical-mechanics"
  | .«t-string-theory»              => "t-string-theory"
  | .«t-thermodynamics»             => "t-thermodynamics"
  | .«t-units»                      => "t-units"
  | .«t-capacity-qi»                   => "t-capacity-qi"
  | .«t-channels-qi»                   => "t-channels-qi"
  | .«t-classical-info-qi»             => "t-classical-info-qi"
  | .«t-entropy-qi»                    => "t-entropy-qi"
  | .«t-for-mathlib-qi»                => "t-for-mathlib-qi"
  | .«t-measurements-qi»               => "t-measurements-qi"
  | .«t-operators-qi»                  => "t-operators-qi"
  | .«t-resource-theory-qi»            => "t-resource-theory-qi"
  | .«t-states-qi»                     => "t-states-qi"
  | .«CI»                              => "CI"
  | .«PhyslibAlpha»                    => "PhyslibAlpha"

instance : ToString Label where
  toString := Label.toString

/--
A `LabelData` consists of the
* The `dirs` field is the array of all "root paths" such that a modification in a file contained
  in one of these paths should be labelled with `label`.
* The `exclusions` field is the array of all "root paths" that are excluded, among the
  ones that start with the ones in `dirs`.
  Any modifications to a file in an excluded path is ignored for the purposes of labelling.
* The `dependencies` field is the array of all labels, which are lower in the import hierarchy
  and which should be excluded if the label is present.
* The `exclusive` field, if `true`, makes the label applicable only when every modified file
  lies in one of `dirs`.-/
structure LabelData (label : Label) where
  /-- Array of paths which fall under this label. e.g. `"Physlib" / "Cosmology"`.

  For a label of the form `t-cosmology` this defaults to `#["Physlib" / "Cosmology"]`.
  For a label of the form `t-states-qi` this defaults to `#["QuantumInfo" / "States"]`. -/

  dirs : Array FilePath := if label.toString.startsWith "t-" && label.toString.endsWith "-qi" then
      #["QuantumInfo" / ("".intercalate (label.toString.splitOn "-" |>.drop 1 |>.dropLast |>.map .capitalize))]
  else if label.toString.startsWith "t-" then
    #["Physlib" / ("".intercalate (label.toString.splitOn "-" |>.drop 1 |>.map .capitalize))]
    else #[]
  /-- Array of paths which should be excluded.
  Any modifications to a file in an excluded path are ignored for the purposes of labelling. -/
  exclusions : Array FilePath := #[]
  /-- Labels which are "lower" in the Physlib import order. These labels will not be added
  alongside the label. For example, in Mathlib, any PR to `t-ring-theory` might modify files from `t-algebra`
  but should only get the former label -/
  dependencies : Array Label := #[]
  /-- If `true`, the label is only applicable when every (non-excluded) modified file lies in
  one of `dirs`. -/
  exclusive : Bool := false
  deriving BEq, Hashable


/-- This function maps each label to the corresponding paths
For now, no exclusions or dependencies are specified --/
def physlibLabelData: (l: Label) → LabelData l
  | .«t-classical-field-theory» => {}
  | .«t-classical-mechanics» => {}
  | .«t-condensed-matter» => {}
  | .«t-cosmology» => {}
  | .«t-electromagnetism» => {}
  | .«t-fluid-dynamics» => {}
  | .«t-mathematics» => {}
  | .«t-meta» => {}
  | .«t-optics» => {}
  | .«t-particles» => {}
  | .«t-qft» => { dirs := #["Physlib" / "QFT"] }
  | .«t-quantum-mechanics» => {}
  | .«t-relativity» => {}
  | .«t-space-and-time» => {}
  | .«t-statistical-mechanics» => {}
  | .«t-string-theory» => {}
  | .«t-thermodynamics» => {}
  | .«t-units» => {}
  | .«t-capacity-qi» => {}
  | .«t-channels-qi» => {}
  | .«t-classical-info-qi» => {}
  | .«t-entropy-qi» => {}
  | .«t-for-mathlib-qi» => {}
  | .«t-measurements-qi» => {}
  | .«t-operators-qi» => {}
  | .«t-resource-theory-qi» => {}
  | .«t-states-qi» => {}
  | .«CI» => { dirs := #["scripts"] }
  | .«PhyslibAlpha» => { dirs := #["PhyslibAlpha", "PhyslibAlpha.lean"], exclusive := true }

/-- Exceptions inside `Physlib/` which are not covered by any label.
(For the First versions, no exceptions) -/
def physlibUnlabelled : Array FilePath := #[ ]
/-- Exceptions inside `QuantumInfo/` which are not covered by any label.
(For the First versions, no exceptions) -/
def quantuminfoUnlabelled : Array FilePath := #[ ]

/-- Checks if the folder `path` lies inside the folder `dir`.
Copied verbatim from mathlib `scripts/autolabel.lean` -/
def _root_.System.FilePath.isPrefixOf (dir path : FilePath) : Bool :=
  -- use `dir / ""` to prevent partial matching of folder names
  (dir / "").normalize.toString.isPrefixOf (path / "").normalize.toString

/--
Return all labels in `physlibLabels` which match
at least one of the `files`. A label with `exclusive := true` must instead match all of
the `files`.
* `files`: array of relative paths starting from the physlib root directory. -/
def getMatchingLabels (files : Array FilePath) : Array Label :=
  let applicable := physlibLabels.filter fun label ↦
    -- first exclude all files the label excludes,
    -- then see if any (or, for an exclusive label, every) remaining file is included by the label
    let data := physlibLabelData label
    let notExcludedFiles := files.filter fun file ↦
      data.exclusions.all (!·.isPrefixOf file)
    let isIncluded (file : FilePath) : Bool := data.dirs.any (·.isPrefixOf file)
    notExcludedFiles.any isIncluded && (!data.exclusive || notExcludedFiles.all isIncluded)
  -- return sorted list of labels
  applicable |>.qsort (·.toString < ·.toString)

/-- Helper function: union of all labels and all their dependent labels -/
partial def collectLabelsAndDependentLabels (labels: Array Label) : Array Label :=
  labels.flatMap fun label ↦
    (collectLabelsAndDependentLabels (physlibLabelData label).dependencies).push label

/-- Reduce a list of labels to not include any which are dependencies of other
labels in the list -/
def dropDependentLabels (labels: Array Label) : Array Label :=
  let dependentLabels := collectLabelsAndDependentLabels <|
    labels.flatMap fun label ↦ (physlibLabelData label).dependencies
  labels.filter (!dependentLabels.contains ·)

/-!
Testing the functionality of the declarations defined in this script
-/
section Tests

-- Test `FilePath.isPrefixOf`
#guard ("Physlib" / "CondensedMatter" : FilePath).isPrefixOf ("Physlib" / "CondensedMatter" / "TightBindingChain" /"Basic.lean")

-- Test `FilePath.isPrefixOf` does not trigger on partial prefixes
#guard ! ("Physlib" / "Condensed" : FilePath).isPrefixOf ("Physlib" / "CondensedMatter" )

#guard getMatchingLabels #[] == #[]

-- Test default value for `label.dirs` works
#guard getMatchingLabels #["Physlib" / "CondensedMatter" / "TightBindingChain" / "Basic.lean"] == #[.«t-condensed-matter»]

-- Test QuantumInfo labels resolve to their topic folders
#guard getMatchingLabels #["QuantumInfo" / "Entropy" / "Basic.lean"] == #[.«t-entropy-qi»]
#guard getMatchingLabels #["QuantumInfo" / "ResourceTheory" / "Basic.lean"] == #[.«t-resource-theory-qi»]

-- Test exclusion
-- No exclusion exists in Physlib as of now

-- Test targeting a file instead of a directory
#guard getMatchingLabels #["scripts" / "lint-style.py"] == #[.«CI»]

-- Test the exclusive `PhyslibAlpha` label: applied only if every file is in `PhyslibAlpha/`
-- or is `PhyslibAlpha.lean`
#guard getMatchingLabels #["PhyslibAlpha" / "Relativity" / "Basic.lean"] == #[.«PhyslibAlpha»]
#guard getMatchingLabels #["PhyslibAlpha" / "Relativity" / "Basic.lean", "PhyslibAlpha.lean"] ==
  #[.«PhyslibAlpha»]
#guard getMatchingLabels #["PhyslibAlpha.lean"] == #[.«PhyslibAlpha»]
#guard getMatchingLabels #["PhyslibAlpha.lean", "Physlib" / "Cosmology" / "Basic.lean"] ==
  #[.«t-cosmology»]
#guard getMatchingLabels #["PhyslibAlpha.lean", "README.md"] == #[]

/-- Testing function to ensure the labels defined in `physlibLabels` cover all
subfolders of `Physlib/` and `QuantumInfo/`. -/
partial def findUncoveredPaths (path : FilePath) (exceptions : Array FilePath := #[]) :
    IO <| Array FilePath := do
  let mut notMatched : Array FilePath := #[]
  -- all directories inside `path`
  let subDirs ← (← path.readDir).map (·.path) |>.filterM (do FilePath.isDir ·)
  for dir in subDirs do
    -- if the sub directory is not matched by a label,
    -- we go recursively into it
    if (getMatchingLabels #[dir]).size == 0 then
      notMatched := notMatched ++ (← findUncoveredPaths dir exceptions)
  -- a directory should be flagged if none of its sub-directories is matched by a label
  -- note: we assume here the base directory, i.e. "Physlib" is never matched by a label,
  -- therefore we skip this test.
  if notMatched.size == subDirs.size then
    if exceptions.contains path then
      return #[]
    else
      return #[path]
  else
    return notMatched

end Tests

/--
Create a message which GitHub CI parses as annotation and displays at the specified file.

Note: `file` is duplicated below so that it is also visible in the plain text output.

* `type`: "error" or "warning"
* `file`: file where the annotation should be displayed
* `title`: title of the annotation
* `message`: annotation message
-/
def githubAnnotation (type file title message : String) : String :=
  s!"::{type} file={file},title={title}::{file}: {message}"

end AutoLabel

open IO AutoLabel in

/-- `args` is expected to have length 0 or 1, where the first argument is the PR number.

If a PR number is provided, the script requires GitHub CLI `gh` to be installed in order
to add the label to the PR.

## Exit codes:

- `0`: success
- `1`: invalid arguments provided
- `2`: invalid labels defined
- `3`: ~labels do not cover all of `Physlib/`~ (unused; only emitting warning)
-/
unsafe def main (args : List String): IO UInt32 := do
  if args.length > 1 then
    println s!"::error:: autolabel: invalid number of arguments ({args.length}), \
    expected at most 1. Please run without arguments or provide the target PR's \
    number as a single argument!"
    return 1
  let prNumber? := args[0]?

  -- test: validate that all paths in `physlibLabelData` actually exist
  let mut valid := true
  for label in physlibLabels do
    let data := physlibLabelData label
    for dir in data.dirs do
      unless ← FilePath.pathExists dir do
        -- print github annotation error
        println <| AutoLabel.githubAnnotation "error" "scripts/github/autolabel.lean"
          s!"Misformatted `{ ``AutoLabel.physlibLabelData }`"
          s!"directory '{dir}' does not exist but is included by label '{label}'. \
          Please update `{ ``AutoLabel.physlibLabelData }`!"
        valid := false
    for dir in data.exclusions do
      unless ← FilePath.pathExists dir do
        -- print github annotation error
        println <| AutoLabel.githubAnnotation "error" "scripts/github/autolabel.lean"
          s!"Misformatted `{ ``AutoLabel.physlibLabelData }`"
          s!"directory '{dir}' does not exist but is excluded by label '{label}'. \
          Please update `{ ``AutoLabel.physlibLabelData }`!"
        valid := false
  unless valid do
    return 2

  -- test: validate that the labels cover all of the `Physlib/` folder
  let notMatchedPaths ← findUncoveredPaths "Physlib" (exceptions := physlibUnlabelled)
  if notMatchedPaths.size > 0 then
    -- print github annotation warning
    -- note: only emitting a warning because the workflow is only triggered on the first commit
    -- of a PR and could therefore lead to unexpected behaviour if a folder was created later.
    println <| AutoLabel.githubAnnotation "warning" "scripts/github/autolabel.lean"
      s!"Incomplete `{ ``AutoLabel.physlibLabelData }`"
      s!"the following paths inside `Physlib/` are not covered \
      by any label: {notMatchedPaths} Please modify `AutoLabel.physlibLabels` accordingly!"
    -- return 3

  -- get the modified files
  println "Computing 'git diff --name-only origin/master...HEAD'"
  let gitDiff ← IO.Process.run {
    cmd := "git",
    args := #["diff", "--name-only", "origin/master...HEAD"] }
  println s!"---\n{gitDiff}\n---"
  -- drop the empty entry from the trailing newline, which would block exclusive labels
  let modifiedFiles : Array FilePath :=
    (gitDiff.splitOn "\n").toArray.filter (!·.isEmpty) |>.map (⟨·⟩)

  -- find labels covering the modified files
  let labels := dropDependentLabels <| getMatchingLabels modifiedFiles
  println s!"::notice::Applicable labels: {labels}"

  match labels with
  | #[] =>
    println s!"::warning::no label to add"
  | newLabels =>
    match prNumber? with
    | some n =>
      if newLabels.size > MAX_LABELS then
        println s!"::notice::not adding more than {MAX_LABELS} labels: {newLabels}"
        return 0
      let labelsPresent ← IO.Process.run {
        cmd := "gh"
        args := #["pr", "view", n, "--json", "labels", "--jq", ".labels .[] .name"]}
      let labels := labelsPresent.splitToList (· == '\n')
      let autoLabels := physlibLabels.map (·.toString)
      match labels.filter autoLabels.contains with
      | [] => -- if the PR does not have a label that this script could add, then we add a label
        let _ ← IO.Process.run {
          cmd := "gh",
          args := #["pr", "edit", n, "--add-label", s!"\"{",".intercalate <| newLabels.toList.map (·.toString)}\""] }
        println s!"::notice::added labels: {newLabels}"
      | t_labels_already_present =>
        println s!"::notice::Did not add labels '{newLabels}', \
                  since {t_labels_already_present} were already present"
    | none =>
      println s!"::warning::no PR-number provided, not adding labels. \
      (call `lake exe autolabel 150602` to add the labels to PR `150602`)"
  return 0
