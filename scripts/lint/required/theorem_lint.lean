/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Lean
/-!

# Theorem linter

A linter checking that `theorem` is used exactly for the results listed in the theorems file.

## i. Overview

Each of the libraries `Physlib`, `QuantumInfo` and `PhyslibAlpha` reserves the `theorem` keyword
for its conceptually important results; every other result is a `lemma`. The fully qualified
names of the important results of all three libraries are listed, one per line, in
`scripts/lint/exemptions/Theorems.txt`, in a section `[L]` for each library `L`. This executable
checks, for each library `L`, that:

- every declaration of `L` written with `theorem` is listed in the section `[L]`,
- every name listed in the section `[L]` is a declaration of `L` written with `theorem`,
- every declaration of `L` written with `theorem` has a doc-string.

`lemma` is Mathlib syntax which expands to `theorem`, so the environment does not record which
of the two keywords was written. The linter recovers it without a text search. For each theorem
of the imported environment it takes the declaration range Lean stored for it, and runs Lean's
own parser, with the token table of the environment, at the start of that range: first the
declaration modifiers (doc-string, attributes, `private`, ...), then the keyword, then the
declaration identifier. The identifier is checked against the fully qualified name of the
constant, accounting for the enclosing namespaces, `_root_` and `private`. This check discards
the theorems generated from a declaration (by `to_additive`, `simps`, equation lemmas, ...),
which share its declaration range but not its name.

Run from the root of the repository with `lake exe theorem_lint`, after building the three
libraries. `lake exe theorem_lint Physlib` lints only `Physlib` (and similarly for the others).

## ii. Key results

- `TheoremLint.parseNames` reads the names listed in `scripts/lint/exemptions/Theorems.txt`.
- `TheoremLint.headTokens` reads the keyword and identifier of a declaration with Lean's parser.
- `TheoremLint.lint` gives the errors of the linter for one library.
- `TheoremLint.report` groups the errors by kind, with how to fix each kind.
- `main` runs the linter on the libraries given as arguments, or on all three.

## iii. Table of contents

- A. The theorems file
- B. The errors
- C. Parsing the theorems file
- D. The keyword of a theorem
- E. The linter
- F. Tests
  - F.1. The reports of the errors
  - F.2. Parsing the theorems file
  - F.3. Matching declaration identifiers
  - F.4. Reading the keyword of a declaration
- G. The executable

## iv. References

* None

-/

open Lean Parser

namespace TheoremLint

/-!

## A. The theorems file

The theorems file is split into sections, one for each library `L`, each starting with a line
`[L]`. Each section lists one fully qualified name per line. Blank lines, and comments, which
are lines starting with `--`, are ignored.

-/

/-- The libraries which are linted. -/
def libraries : Array Name := #[`Physlib, `QuantumInfo, `PhyslibAlpha]

/-- The file listing the theorems of the libraries, relative to the root of the repository. -/
def theoremsFile : System.FilePath := "scripts" / "lint" / "exemptions" / "Theorems.txt"

/-!

## B. The errors

-/

/-- The kinds of error the linter reports. -/
inductive ErrorKind where
  /-- A line of the theorems file starting with `[` which is not the section of a library. -/
  | unknownSection (text : String)
  /-- A line of the theorems file before its first section. -/
  | beforeFirstSection (text : String)
  /-- A line of the theorems file which is not a Lean name. -/
  | notAName (text : String)
  /-- A name listed a second time in a section, first listed on `firstLine`. -/
  | duplicate (name : Name) (firstLine : Nat)
  /-- A declaration written with `theorem` without a doc-string. -/
  | noDocString (name : Name)
  /-- A declaration of `library` written with `theorem` and not listed in its section. -/
  | notListed (library name : Name)
  /-- A listed name written with `lemma`, at `pos` in `file`. -/
  | writtenWithLemma (name : Name) (file : System.FilePath) (pos : Position)
  /-- A listed name which is not a declaration. -/
  | notADeclaration (name : Name)
  /-- A name listed in the section of `library` but declared in `module`, outside `library`. -/
  | wrongLibrary (library name module : Name)
  /-- A listed name which is a declaration of the library, but not a theorem. -/
  | notATheorem (name : Name)

/-- The place of the kind of `kind` in the order in which the errors are reported. -/
def ErrorKind.rank : ErrorKind → Nat
  | .unknownSection .. => 0
  | .beforeFirstSection .. => 1
  | .notAName .. => 2
  | .duplicate .. => 3
  | .noDocString .. => 4
  | .notListed .. => 5
  | .writtenWithLemma .. => 6
  | .notADeclaration .. => 7
  | .wrongLibrary .. => 8
  | .notATheorem .. => 9

/-- The heading of the errors of the kind of `kind`. -/
def ErrorKind.title : ErrorKind → String
  | .unknownSection .. => "Unknown sections"
  | .beforeFirstSection .. => "Names listed before the first section"
  | .notAName .. => "Lines which are not Lean names"
  | .duplicate .. => "Names listed twice"
  | .noDocString .. => "Theorems without a doc-string"
  | .notListed .. => s!"Theorems not listed in {theoremsFile}"
  | .writtenWithLemma .. => "Listed results written with `lemma`"
  | .notADeclaration .. => "Listed names which are not declarations"
  | .wrongLibrary .. => "Names listed under the wrong library"
  | .notATheorem .. => "Listed names which are not theorems"

/-- How to fix the errors of the kind of `kind`. -/
def ErrorKind.hint : ErrorKind → String
  | .unknownSection .. => s!"The sections are \
      {", ".intercalate (libraries.map (s!"`[{·}]`")).toList}."
  | .beforeFirstSection .. => "List each name under the section `[L]` of its library `L`."
  | .notAName .. => "Each line is a section `[L]`, a fully qualified name, or a comment starting \
      with `--`."
  | .duplicate .. => "Remove the repeated entries."
  | .noDocString .. => "Add a doc-string `/-- … -/` to each of these theorems."
  | .notListed .. => "Use `lemma`. Only list a result, under the section of its library, if it \
      is a significant result in physics, usually known by name."
  | .writtenWithLemma .. => "Use `theorem`, or remove the name from the theorems file."
  | .notADeclaration .. => "Give the fully qualified name of each result."
  | .wrongLibrary .. => "Move each name to the section of the library declaring it."
  | .notATheorem .. => "Only results written with `theorem` can be listed."

/-- The details of the error `kind`, shown after its location. -/
def ErrorKind.detail : ErrorKind → String
  | .unknownSection text | .beforeFirstSection text | .notAName text => text
  | .duplicate name firstLine => s!"{name}, first listed on line {firstLine}"
  | .noDocString name | .notListed _ name | .notADeclaration name | .notATheorem name =>
    name.toString
  | .writtenWithLemma name file pos =>
    s!"{name}, written with `lemma` at {file}:{pos.line}:{pos.column}"
  | .wrongLibrary library name module =>
    s!"{name}, listed under `[{library}]` but declared in {module}"

/-- An error of the linter, located in a source file. -/
structure LintError where
  /-- The file the error is located in. -/
  file : System.FilePath
  /-- The position of the error in `file`. -/
  pos : Position
  /-- The kind of the error. -/
  kind : ErrorKind

/-- An error of kind `kind` located at the line `line` of the theorems file. -/
def theoremsFileError (line : Nat) (kind : ErrorKind) : LintError :=
  ⟨theoremsFile, ⟨line, 0⟩, kind⟩

/-- The order of errors: by kind, then by file, then by position. -/
def LintError.lt (e f : LintError) : Bool :=
  e.kind.rank < f.kind.rank || e.kind.rank == f.kind.rank &&
    (e.file.toString < f.file.toString || e.file == f.file &&
      (e.pos.line < f.pos.line || e.pos.line == f.pos.line && e.pos.column < f.pos.column))

/-- The report of `errors`, grouped by kind. Each group has a heading with its number of errors,
how to fix them, and the location and details of each error. With `colour`, the headings and
hints are coloured for a terminal. -/
def report (errors : Array LintError) (colour : Bool := true) : String := Id.run do
  let paint (code text : String) := if colour then s!"\x1b[{code}m{text}\x1b[0m" else text
  let errors := errors.qsort LintError.lt
  let mut lines := #[]
  -- The rank of the kind of the previous error, to start a new group when it changes.
  let mut previous : Option Nat := none
  for e in errors do
    if previous != some e.kind.rank then
      unless previous.isNone do lines := lines.push ""
      let count := (errors.filter (·.kind.rank == e.kind.rank)).size
      lines := lines.push (paint "1;31" s!"{e.kind.title} ({count})")
      lines := lines.push (paint "33" s!"  {e.kind.hint}")
      previous := some e.kind.rank
    lines := lines.push s!"  {e.file}:{e.pos.line}:{e.pos.column}  {e.kind.detail}"
  return "\n".intercalate lines.toList

/-!

## C. Parsing the theorems file

-/

/-- The names listed in the theorems file, given as its lines, each with the library whose
section lists it and its line. -/
def parseNames (lines : Array String) : Except LintError (Array (Name × Name × Nat)) := do
  let mut library : Option Name := none
  let mut names := #[]
  for line in lines, lineNo in [1:lines.size + 1] do
    let text := line.trimAscii.toString
    if text.isEmpty || text.startsWith "--" then continue
    if text.startsWith "[" then
      let some lib := libraries.find? (text == s!"[{·}]")
        | throw <| theoremsFileError lineNo (.unknownSection text)
      library := lib
      continue
    let some lib := library
      | throw <| theoremsFileError lineNo (.beforeFirstSection text)
    let some name := Syntax.decodeNameLit ("`" ++ text)
      | throw <| theoremsFileError lineNo (.notAName text)
    names := names.push (lib, name, lineNo)
  return names

/-!

## D. The keyword of a theorem

-/

/-- A theorem of the library together with how it is written in the source. -/
structure WrittenTheorem where
  /-- The constant, with `private` names given as the user wrote them. -/
  name : Name
  /-- The source file of the module declaring the constant. -/
  file : System.FilePath
  /-- The position of the keyword in `file`. -/
  pos : Position
  /-- The keyword the declaration is written with, `theorem` or `lemma`. -/
  keyword : String
  /-- Whether the declaration has a doc-string. -/
  hasDocString : Bool

/-- The source file of a module, relative to the root of the repository. -/
def moduleFile (module : Name) : System.FilePath :=
  (System.mkFilePath (module.components.map Name.toString)).addExtension "lean"

/-- Parses, with Lean's parser in the environment `env`, the declaration modifiers at `pos`
followed by two tokens, and returns these tokens. For a `theorem` or `lemma` declaration they
are its keyword and its declaration identifier. -/
def headTokens (env : Environment) (ictx : InputContext) (pos : String.Pos.Raw) :
    Option (Syntax × Syntax) :=
  let p := andthenFn (Command.declModifiers false).fn (andthenFn (tokenFn []) (tokenFn []))
  let s := p.run ictx { env, options := {} } (getTokenTable env)
    ((mkParserState ictx.inputString).setPos pos)
  if s.hasError then none
  else some (s.stxStack.get! (s.stxStack.size - 2), s.stxStack.back)

/-- Whether the declaration identifier `ident`, written in some namespace, declares the constant
`name`: `name` is `ident` prefixed by the namespace, or `ident` with `_root_` removed. -/
def declares (ident name : Name) : Bool :=
  let name := privateToUserName name
  if ident.getRoot == `_root_ then
    ident.replacePrefix `_root_ .anonymous == name
  else
    ident.isSuffixOf name

/-- The theorems declared in `module`, written with `theorem` or `lemma`. -/
def writtenTheorems (env : Environment) (module : Name) (constants : Array ConstantInfo) :
    CoreM (Array WrittenTheorem) := do
  let file := moduleFile module
  let ictx := mkInputContext (← IO.FS.readFile file) file.toString
  let mut result := #[]
  for c in constants do
    let .thmInfo _ := c | continue
    let some ranges ← findDeclarationRanges? c.name | continue
    let start := ictx.fileMap.ofPosition ranges.range.pos
    let some (keywordStx, ident) := headTokens env ictx start | continue
    let .atom _ keyword := keywordStx | continue
    unless keyword == "theorem" || keyword == "lemma" do continue
    let .ident _ _ ident _ := ident | continue
    unless declares ident c.name do continue
    let pos := ictx.fileMap.toPosition (keywordStx.getPos?.getD start)
    let hasDocString := (← findDocString? env c.name).isSome
    result := result.push { name := privateToUserName c.name, file, pos, keyword, hasDocString }
  return result

/-!

## E. The linter

-/

/-- The errors of the linter for `library`, whose section of the theorems file lists `names`:
theorems not listed in that section or without a doc-string, and listed names which are not
theorems. -/
def lint (library : Name) (names : Array (Name × Nat)) : CoreM (Array LintError) := do
  let env ← getEnv
  let mut errors := #[]
  -- The names listed in the theorems file, with their lines, and duplicates among them.
  let mut listed : NameMap Nat := {}
  for (name, line) in names do
    if let some first := listed.find? name then
      errors := errors.push <| theoremsFileError line (.duplicate name first)
    listed := listed.insert name line
  -- The theorems of the library and their keywords.
  let mut written : NameMap WrittenTheorem := {}
  for module in env.header.moduleNames, data in env.header.moduleData do
    unless library.isPrefixOf module do continue
    for thm in ← writtenTheorems env module data.constants do
      written := written.insert thm.name thm
  for (name, thm) in written do
    if thm.keyword == "theorem" && !thm.hasDocString then
      errors := errors.push ⟨thm.file, thm.pos, .noDocString name⟩
    match thm.keyword, listed.find? name with
    | "theorem", none => errors := errors.push ⟨thm.file, thm.pos, .notListed library name⟩
    | "lemma", some line =>
      errors := errors.push <| theoremsFileError line (.writtenWithLemma name thm.file thm.pos)
    | _, _ => pure ()
  for (name, line) in listed do
    if written.contains name then continue
    let kind : ErrorKind := match env.getModuleIdxFor? name with
      | none => .notADeclaration name
      | some idx =>
        let module := env.header.moduleNames[idx]!
        if library.isPrefixOf module then .notATheorem name else .wrongLibrary library name module
    errors := errors.push <| theoremsFileError line kind
  return errors

/-!

## F. Tests

These tests run when this file is compiled, so `lake exe theorem_lint` fails to build if one of
them fails. The environment here only imports `Lean`, so `lemma` is not a keyword and the tests of
`headTokens` only cover `theorem`.

-/

/-! ### F.1. The reports of the errors -/

/--
info: Unknown sections (1)
  The sections are `[Physlib]`, `[QuantumInfo]`, `[PhyslibAlpha]`.
  scripts/lint/exemptions/Theorems.txt:1:0  [Mathlib]
-/
#guard_msgs in
#eval IO.println (report #[theoremsFileError 1 (.unknownSection "[Mathlib]")] false)

/--
info: Names listed before the first section (1)
  List each name under the section `[L]` of its library `L`.
  scripts/lint/exemptions/Theorems.txt:1:0  A.b
-/
#guard_msgs in
#eval IO.println (report #[theoremsFileError 1 (.beforeFirstSection "A.b")] false)

/--
info: Lines which are not Lean names (1)
  Each line is a section `[L]`, a fully qualified name, or a comment starting with `--`.
  scripts/lint/exemptions/Theorems.txt:2:0  A b
-/
#guard_msgs in
#eval IO.println (report #[theoremsFileError 2 (.notAName "A b")] false)

/--
info: Names listed twice (1)
  Remove the repeated entries.
  scripts/lint/exemptions/Theorems.txt:5:0  Foo.bar, first listed on line 3
-/
#guard_msgs in
#eval IO.println (report #[theoremsFileError 5 (.duplicate `Foo.bar 3)] false)

/--
info: Theorems without a doc-string (1)
  Add a doc-string `/-- … -/` to each of these theorems.
  Physlib/Foo.lean:12:0  Foo.bar
-/
#guard_msgs in
#eval IO.println (report #[⟨"Physlib/Foo.lean", ⟨12, 0⟩, .noDocString `Foo.bar⟩] false)

/--
info: Theorems not listed in scripts/lint/exemptions/Theorems.txt (1)
  Use `lemma`. Only list a result, under the section of its library, if it is a significant
    result in physics, usually known by name.
  Physlib/Foo.lean:12:0  Foo.bar
-/
#guard_msgs (whitespace := lax) in
#eval IO.println (report #[⟨"Physlib/Foo.lean", ⟨12, 0⟩, .notListed `Physlib `Foo.bar⟩] false)

/--
info: Listed results written with `lemma` (1)
  Use `theorem`, or remove the name from the theorems file.
  scripts/lint/exemptions/Theorems.txt:3:0  Foo.bar, written with `lemma` at Physlib/Foo.lean:12:0
-/
#guard_msgs in
#eval IO.println
  (report #[theoremsFileError 3 (.writtenWithLemma `Foo.bar "Physlib/Foo.lean" ⟨12, 0⟩)] false)

/--
info: Listed names which are not declarations (1)
  Give the fully qualified name of each result.
  scripts/lint/exemptions/Theorems.txt:3:0  Foo.baz
-/
#guard_msgs in
#eval IO.println (report #[theoremsFileError 3 (.notADeclaration `Foo.baz)] false)

/--
info: Names listed under the wrong library (1)
  Move each name to the section of the library declaring it.
  scripts/lint/exemptions/Theorems.txt:3:0  Foo.bar, listed under `[Physlib]` but declared in
    PhyslibAlpha.Foo
-/
#guard_msgs (whitespace := lax) in
#eval IO.println
  (report #[theoremsFileError 3 (.wrongLibrary `Physlib `Foo.bar `PhyslibAlpha.Foo)] false)

/--
info: Listed names which are not theorems (1)
  Only results written with `theorem` can be listed.
  scripts/lint/exemptions/Theorems.txt:3:0  Foo.bar
-/
#guard_msgs in
#eval IO.println (report #[theoremsFileError 3 (.notATheorem `Foo.bar)] false)

-- Errors are grouped by kind, whatever their library, and sorted by location within each group.
/--
info: Theorems without a doc-string (3)
  Add a doc-string `/-- … -/` to each of these theorems.
  Physlib/A.lean:3:2  A.b
  Physlib/B.lean:7:0  B.c
  QuantumInfo/C.lean:1:0  C.d

Listed names which are not theorems (1)
  Only results written with `theorem` can be listed.
  scripts/lint/exemptions/Theorems.txt:4:0  D.e
-/
#guard_msgs in
#eval IO.println (report #[⟨"QuantumInfo/C.lean", ⟨1, 0⟩, .noDocString `C.d⟩,
  ⟨"Physlib/B.lean", ⟨7, 0⟩, .noDocString `B.c⟩, theoremsFileError 4 (.notATheorem `D.e),
  ⟨"Physlib/A.lean", ⟨3, 2⟩, .noDocString `A.b⟩] false)

/-! ### F.2. Parsing the theorems file -/

/-- Prints the names `parseNames` reads from the lines `lines`, or the error it reports. -/
def printParse (lines : Array String) : IO Unit :=
  match parseNames lines with
  | .ok names => IO.println (repr names)
  | .error e => IO.println (report #[e] false)

/-- info: #[(`Physlib, `A.b, 2), (`Physlib, `C.d, 4), (`PhyslibAlpha, `Ud_orthonormal₁, 6)] -/
#guard_msgs in
#eval printParse #["[Physlib]", "A.b", "", "  C.d  ", "[PhyslibAlpha]", "Ud_orthonormal₁"]

/-- info: #[] -/
#guard_msgs in
#eval printParse #[]

/-- info: #[(`Physlib, `A.b, 4)] -/
#guard_msgs in
#eval printParse #["-- A comment before the first section.", "[Physlib]", "  -- A comment.", "A.b"]

/--
info: Names listed before the first section (1)
  List each name under the section `[L]` of its library `L`.
  scripts/lint/exemptions/Theorems.txt:1:0  A.b
-/
#guard_msgs in
#eval printParse #["A.b", "[Physlib]"]

/--
info: Unknown sections (1)
  The sections are `[Physlib]`, `[QuantumInfo]`, `[PhyslibAlpha]`.
  scripts/lint/exemptions/Theorems.txt:1:0  [Mathlib]
-/
#guard_msgs in
#eval printParse #["[Mathlib]", "A.b"]

/--
info: Lines which are not Lean names (1)
  Each line is a section `[L]`, a fully qualified name, or a comment starting with `--`.
  scripts/lint/exemptions/Theorems.txt:2:0  A b
-/
#guard_msgs in
#eval printParse #["[Physlib]", "A b"]

/-! ### F.3. Matching declaration identifiers -/

/-- info: true -/
#guard_msgs in
#eval declares `bar `Foo.bar

/-- info: true -/
#guard_msgs in
#eval declares `Foo.bar `Foo.bar

/-- info: true -/
#guard_msgs in
#eval declares `Bar.baz `Foo.Bar.baz

/-- info: true -/
#guard_msgs in
#eval declares `_root_.bar `bar

/-- info: false -/
#guard_msgs in
#eval declares `_root_.bar `Foo.bar

/-- info: false -/
#guard_msgs in
#eval declares `bar `Foo.baz

/-- info: false -/
#guard_msgs in
#eval declares `Foo.bar `bar

/-- info: true -/
#guard_msgs in
#eval declares `bar ((Name.mkNum `_private.Physlib.Test 0).str "bar")

/-! ### F.4. Reading the keyword of a declaration -/

/-- The keyword and identifier which `headTokens` reads at the start of `source`, in the
current environment. -/
def headTokensOf (source : String) : CoreM (Option (String × Name)) := do
  let ictx := mkInputContext source "<test>"
  return match headTokens (← getEnv) ictx 0 with
    | some (.atom _ keyword, .ident _ _ ident _) => some (keyword, ident)
    | _ => none

/-- info: some ("theorem", `Foo.bar) -/
#guard_msgs in
#eval headTokensOf "theorem Foo.bar : True := trivial"

/-- info: some ("theorem", `bar) -/
#guard_msgs in
#eval headTokensOf "/-- A doc-string. -/\n@[simp] private theorem bar : True := trivial"

/-- info: some ("theorem", `_root_.bar) -/
#guard_msgs in
#eval headTokensOf "protected theorem _root_.bar : True := trivial"

/-- info: some ("def", `bar) -/
#guard_msgs in
#eval headTokensOf "noncomputable def bar : Nat := 0"

end TheoremLint

/-!

## G. The executable

-/

open TheoremLint in
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  Lean.enableInitializersExecution
  let toLint := if args.isEmpty then libraries else (args.map String.toName).toArray
  for library in toLint do
    unless libraries.contains library do
      IO.eprintln s!"Unknown library `{library}`, expected one of {libraries}."
      return 1
  let env ← importModules (loadExts := true) (toLint.map ({ module := · })) {} 0
  let ctx : Core.Context := { fileName := "", options := {}, fileMap := default }
  let listed ← match parseNames (← IO.FS.lines theoremsFile) with
    | .ok listed => pure listed
    | .error e => IO.eprintln (report #[e]); return 1
  let linted := ", ".intercalate (toLint.map toString).toList
  println! "Linting {linted} against {theoremsFile}.\n"
  -- The errors of all the libraries, reported together so that each kind of error is listed once.
  let mut errors := #[]
  for library in toLint do
    let names := listed.filterMap fun (lib, name, line) =>
      if lib == library then some (name, line) else none
    let (libraryErrors, _) ← (lint library names).toIO ctx { env }
    errors := errors ++ libraryErrors
  if errors.isEmpty then
    println! "\x1b[32mThe theorems of {linted} agree with {theoremsFile}.\x1b[0m"
    return 0
  println! report errors
  let noun := if errors.size == 1 then "error" else "errors"
  println! "\n\x1b[1;31m{errors.size} {noun} found.\x1b[0m"
  return 1
