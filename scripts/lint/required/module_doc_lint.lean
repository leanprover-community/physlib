/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Lean
import Mathlib.Tactic.Linter.TextBased
import Batteries.Data.Array.Merge
import Mathlib.Logic.Function.Basic
/-!

# Linting of module documentation

This file lints the module documentation for consistency.
It currently only checks module headings, and as such many improvements to this file could
be made.

Headings are only read from module documentation (`/-! … -/` blocks), outside of code fences,
so `#check` commands and headings in declaration docstrings are ignored.
Errors are reported grouped by the kind of error, each with a file and line number.

This linter is run in CI and must pass. Files listed in
`scripts/lint/exemptions/module_doc_no_lint.txt` are not checked.

-/

open Lean System Meta

/-!

## Reading the module documentation

-/

/-- `s` with leading and trailing whitespace removed. -/
def strip (s : String) : String := s.trimAscii.copy

/-- `s` with trailing whitespace removed. -/
def rstrip (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile Char.isWhitespace).reverse

/-- The lines of module documentation in a file, paired with their (1-indexed) line numbers.
  Lines inside code fences, and the fence markers themselves, are left out. -/
def moduleDocLines (lines : Array String) : Array (Nat × String) := Id.run do
  let mut out : Array (Nat × String) := #[]
  let mut inDoc := false
  let mut inFence := false
  let mut n := 0
  for line in lines do
    n := n + 1
    let content : Option String :=
      if inDoc then some line
      else
        let t := strip line
        if t.startsWith "/-!" then some ("/-!".intercalate ((t.splitOn "/-!").drop 1)) else none
    if let some c := content then
      unless inDoc do
        inDoc := true
        inFence := false
      let (c, closes) := match c.splitOn "-/" with
        | x :: _ :: _ => (x, true)
        | _ => (c, false)
      if (strip c).startsWith "```" then
        inFence := !inFence
      else if !inFence then
        out := out.push (n, c)
      if closes then inDoc := false
  return out

/-- A heading in the module documentation. -/
structure Heading where
  /-- The line number of the heading. -/
  line : Nat
  /-- The number of leading `#`s. -/
  level : Nat
  /-- The heading after the leading `#`s, with surrounding whitespace removed. -/
  text : String
  /-- The whole heading, with surrounding whitespace removed. -/
  raw : String
  /-- Whether the leading `#`s are followed by a space (or nothing). -/
  spaced : Bool
deriving Inhabited

def parseHeading (n : Nat) (line : String) : Option Heading :=
  let raw := strip line
  if !raw.startsWith "#" then none else
  let cs := raw.toList
  let hashes := cs.takeWhile (· == '#')
  let rest := cs.drop hashes.length
  some { line := n, level := hashes.length, text := strip (String.ofList rest), raw,
         spaced := rest.head?.all (· == ' ') }

/-!

## Kinds of errors

-/

inductive ErrorKind where
  | noModuleDoc
  | titleHead
  | extraTitle
  | overviewHead
  | keyResultsHead
  | tableOfContentsHead
  | referencesHead
  | sectionOrder
  | noSections
  | sectionTag
  | duplicateTag
  | headingFullStop
  | tableOfContentsCorrect
deriving DecidableEq

/-- All kinds of errors, in the order they are reported. -/
def ErrorKind.all : List ErrorKind :=
  [.noModuleDoc, .titleHead, .extraTitle, .overviewHead, .keyResultsHead, .tableOfContentsHead,
    .referencesHead, .sectionOrder, .noSections, .sectionTag, .duplicateTag, .headingFullStop,
    .tableOfContentsCorrect]

def ErrorKind.name : ErrorKind → String
  | .noModuleDoc => "No module documentation headings"
  | .titleHead => "Missing or malformed title"
  | .extraTitle => "Extra title headings"
  | .overviewHead => "Missing or malformed overview section"
  | .keyResultsHead => "Missing or malformed key results section"
  | .tableOfContentsHead => "Missing or malformed table of contents section"
  | .referencesHead => "Missing or malformed references section"
  | .sectionOrder => "Standard sections out of order"
  | .noSections => "No section headings"
  | .sectionTag => "Malformed section tags"
  | .duplicateTag => "Duplicate section tags"
  | .headingFullStop => "Headings ending in a full stop"
  | .tableOfContentsCorrect => "Table of contents does not match headings"

def ErrorKind.hint : ErrorKind → String
  | .noModuleDoc => "Add module documentation `/-! … -/` with the standard headings."
  | .titleHead => "Add a title heading starting with '# ' for the whole module, as the first heading."
  | .extraTitle => "Only the module title should use '# '; use '## A.', '### A.1.' etc. for sections."
  | .overviewHead => "Add an overview section '## i. Overview' after the title heading."
  | .keyResultsHead => "Add a key results section '## ii. Key results' after the overview section."
  | .tableOfContentsHead => "Add a table of contents section '## iii. Table of contents' after the key results section. This can be filled in later."
  | .referencesHead => "Add a references section '## iv. References' after the table of contents section."
  | .sectionOrder => "The headings should start: title, '## i. Overview', '## ii. Key results', '## iii. Table of contents', '## iv. References'."
  | .noSections => "Add other headings for sections and subsections using e.g. '## A.', '### A.1.', '#### A.1.2' etc."
  | .sectionTag => "Section tags end in a dot and have one dot fewer than the heading has '#'s, e.g. '## A.', '### A.1.', '#### A.1.2.'."
  | .duplicateTag => "Each section tag should be used only once."
  | .headingFullStop => "Ensure all headings do not end in a full stop."
  | .tableOfContentsCorrect => "Fix the table of contents to match the headings in the file."

structure DocLintError where
  kind : ErrorKind
  file : FilePath
  line : Nat
  msg : String

/-!

## Checking headings

-/

/-- One of the standard sections following the title. -/
structure StandardSection where
  kind : ErrorKind
  /-- The heading exactly as it should appear. -/
  expected : String
  /-- The heading with numbering, case and a trailing dot ignored, used to find near misses. -/
  key : String

def standardSections : List StandardSection :=
  [⟨.overviewHead, "## i. Overview", "overview"⟩,
   ⟨.keyResultsHead, "## ii. Key results", "key results"⟩,
   ⟨.tableOfContentsHead, "## iii. Table of contents", "table of contents"⟩,
   ⟨.referencesHead, "## iv. References", "references"⟩]

/-- The text of a heading with a leading roman numeral, case and a trailing dot ignored. -/
def Heading.key (h : Heading) : String :=
  let ws := (h.text.splitOn " ").filter (· ≠ "")
  let ws := match ws with
    | w :: rest => if ["i.", "ii.", "iii.", "iv."].contains w.toLower then rest else ws
    | [] => []
  let s := (" ".intercalate ws).toLower
  if s.endsWith "." then String.ofList s.toList.dropLast else s

def hashes (n : Nat) : String := String.ofList (List.replicate n '#')

/-- The first difference between the given table of contents entries (with line numbers) and the
  expected ones, as an optional line number and a message. -/
def tocMismatch : List (Nat × String) → List String → Option (Option Nat × String)
  | [], [] => none
  | (n, x) :: gs, y :: es =>
    if x == y then tocMismatch gs es else some (some n, s!"Entry '{x}' should be '{y}'")
  | [], y :: es =>
    some (none, s!"Missing entry '{y}'" ++ if es.isEmpty then "" else s!" (and {es.length} more)")
  | (n, x) :: gs, [] =>
    some (some n, s!"Unexpected entry '{x}'" ++ if gs.isEmpty then "" else s!" (and {gs.length} more)")

def checkHeadings (f : FilePath) : IO (Array DocLintError) := do
  let lines ← IO.FS.lines f
  let docLines := moduleDocLines lines
  let headings := docLines.filterMap fun (n, c) ↦ parseHeading n c
  let err (kind : ErrorKind) (line : Nat) (msg : String) : DocLintError :=
    { kind, file := f, line, msg }
  let some first := headings[0]?
    | return #[err .noModuleDoc 1 <| if docLines.isEmpty
        then "No module documentation `/-! … -/` found"
        else "The module documentation has no headings"]
  let mut errs : Array DocLintError := #[]

  /- Title. -/
  let hasTitle := first.level == 1
  let titleLine := first.line
  if !hasTitle then
    errs := errs.push <| err .titleHead first.line
      s!"The first heading '{first.raw}' should be a title starting with '# '"
  else if !first.spaced then
    errs := errs.push <| err .titleHead first.line
      s!"The title '{first.raw}' should start with '# '"
  for h in headings.toList.drop 1 do
    if h.level == 1 then
      errs := errs.push <| err .extraTitle h.line s!"'{h.raw}' uses '# ', which is for the title"

  /- Standard sections, found by name rather than by position. -/
  let mut standardIdx : Array (Option Nat) := #[]
  for s in standardSections do
    match headings.findIdx? (·.raw == s.expected) with
    | some i => standardIdx := standardIdx.push (some i)
    | none =>
      match headings.findIdx? (·.key == s.key) with
      | some i =>
        errs := errs.push <| err s.kind headings[i]!.line
          s!"Heading '{headings[i]!.raw}' should be exactly '{s.expected}'"
        standardIdx := standardIdx.push (some i)
      | none =>
        errs := errs.push <| err s.kind titleLine s!"Missing '{s.expected}'"
        standardIdx := standardIdx.push none
  let mut prev : Option Nat := if hasTitle then some 0 else none
  for oi in standardIdx do
    if let some i := oi then
      if let some p := prev then
        if i ≠ p + 1 then
          errs := errs.push <| err .sectionOrder headings[i]!.line
            s!"'{headings[i]!.raw}' should come directly after '{headings[p]!.raw}'"
      prev := some i

  let standardHeading (kind : ErrorKind) : Option Nat :=
    ((standardSections.zip standardIdx.toList).find? (·.1.kind == kind)).bind (·.2)
  /- The text of the module documentation between the heading `k` and the next heading. -/
  let body (k : Nat) : Array (Nat × String) :=
    let start := headings[k]!.line
    let stop := (headings[k + 1]?.map (·.line)).getD (lines.size + 1)
    (docLines.filter fun (n, c) ↦ start < n && n < stop && !(strip c).isEmpty).map
      fun (n, c) ↦ (n, rstrip c)

  /- Section headings: everything other than the title and the standard sections. -/
  let claimed := standardIdx.filterMap id
  let sections := (List.range headings.size).filterMap fun i ↦
    if (i == 0 && hasTitle) || claimed.contains i || headings[i]!.level == 1 then none
    else headings[i]?
  if sections.isEmpty then
    errs := errs.push <| err .noSections titleLine "No section headings found"
  let mut seen : List (String × Nat) := []
  for h in sections do
    if !h.spaced then
      errs := errs.push <| err .sectionTag h.line s!"'{h.raw}' needs a space after the '#'s"
      continue
    let tag := ((h.text.splitOn " ").head?).getD ""
    if tag.isEmpty then
      errs := errs.push <| err .sectionTag h.line s!"'{h.raw}' has no section tag"
      continue
    if !tag.endsWith "." then
      errs := errs.push <| err .sectionTag h.line s!"Section tag '{tag}' should end in a dot"
    else
      let depth := tag.toList.count '.'
      if depth + 1 ≠ h.level then
        errs := errs.push <| err .sectionTag h.line
          s!"Section tag '{tag}' should have heading level '{hashes (depth + 1)}', not '{hashes h.level}'"
    match seen.lookup tag with
    | some l =>
      errs := errs.push <| err .duplicateTag h.line s!"Section tag '{tag}' is already used on line {l}"
    | none => seen := (tag, h.line) :: seen

  /- Full stops. -/
  for h in headings do
    if h.raw.endsWith "." then
      errs := errs.push <| err .headingFullStop h.line s!"'{h.raw}' ends in a full stop"

  /- Table of contents: the module documentation lines between its heading and the next one. -/
  if let some k := standardHeading .tableOfContentsHead then
    let given := body k
    let expected := (sections.filter fun h ↦ 2 ≤ h.level && h.level ≤ 4).map fun h ↦
      String.ofList (List.replicate (2 * (h.level - 2)) ' ') ++ "- " ++ h.text
    if let some (line, msg) := tocMismatch given.toList expected then
      errs := errs.push <| err .tableOfContentsCorrect (line.getD headings[k]!.line) msg
  return errs

/-- The array of modules not to be linted. -/
def noLintArray : IO (Array FilePath) := do
  let path :=
    (mkFilePath ["scripts", "lint", "exemptions", "module_doc_no_lint"]).addExtension "txt"
  let lines ← IO.FS.lines path
  return lines.map (fun l ↦ mkFilePath [l])

/-- The array of modules exempt from all linters, read from
  `scripts/lint/exemptions/LinterExemption.txt`. This is used to lint `QuantumInfo` file-by-file. -/
def linterExemptions : IO (Array FilePath) := do
  let path := (mkFilePath ["scripts", "lint", "exemptions", "LinterExemption"]).addExtension "txt"
  unless (← path.pathExists) do return #[]
  let lines ← IO.FS.lines path
  return lines.filterMap (fun l ↦ if l.trimAscii.isEmpty then none else some (mkFilePath [l.trimAscii.copy]))

/-- The file paths of the modules imported by the root file of the library `lib`
  (e.g. `Physlib.lean`). This reads the source file, so no build is needed. -/
def importedFilePaths (lib : String) : IO (Array FilePath) := do
  let lines ← IO.FS.lines (System.FilePath.mk lib |>.addExtension "lean")
  return lines.filterMap fun l ↦
    match (strip l).splitOn " " |>.filter (· ≠ "") with
    | ["import", m] | ["public", "import", m] =>
      some ((mkFilePath (m.splitOn ".")).addExtension "lean")
    | _ => none

def main (_ : List String) : IO UInt32 := do
  let filePaths := (← importedFilePaths "Physlib") ++ (← importedFilePaths "QuantumInfo") ++
    (← importedFilePaths "PhyslibAlpha")
  let noLint ← noLintArray
  let exemptions ← linterExemptions
  let modulesToCheck := filePaths.filter (fun p ↦ !noLint.contains p ∧ !exemptions.contains p)
  let errors := (← modulesToCheck.mapM checkHeadings).flatten
  let annotate := (← IO.getEnv "GITHUB_ACTIONS") == some "true"
  let fileCount (es : Array DocLintError) := (es.map (·.file)).toList.eraseDups.length
  /- Printing the errors, grouped by kind. -/
  for kind in ErrorKind.all do
    let es := errors.filter (·.kind == kind)
    if es.isEmpty then continue
    IO.println s!"\x1b[1;31m{kind.name}\x1b[0m ({es.size} in {fileCount es} files)"
    IO.println s!"\x1b[33m  {kind.hint}\x1b[0m"
    for e in es do
      IO.println s!"  {e.file}:{e.line}: {e.msg}"
      if annotate then
        IO.println s!"::error file={e.file},line={e.line},title={kind.name}::{e.msg}"
    IO.println ""
  if errors.size > 0 then
    IO.println "\x1b[1mSummary\x1b[0m"
    for kind in ErrorKind.all do
      let es := errors.filter (·.kind == kind)
      unless es.isEmpty do
        IO.println s!"  {es.size}\t{kind.name}"
    IO.println s!"\x1b[1;31merror:\x1b[0m {errors.size} module documentation problems in \
      {fileCount errors} files."
    return 1
  IO.println "\x1b[32mNo documentation style issues found.\x1b[0m"
  return 0
