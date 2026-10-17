/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
/-!

# Testing the auxiliary scripts

This file runs and checks the auxiliary scripts, which generate the website data and are otherwise
only run occasionally (e.g. on a version bump):

- `lake exe make_tag`
- `lake exe TODO_to_yml mkFile`
- `lake exe stats mkHTML`
- `lake exe informal mkFile mkDot mkHTML`

Run it from the root of the repository with

  `lake exe auxillary_script_test`

It needs the libraries `Physlib`, `QuantumInfo` and `PhyslibAlpha` to be built.

## Leaving no footprint

The scripts write their output files to paths relative to the working directory
(e.g. `./docs/Stats.html`). Each script is therefore run with a fresh temporary directory as
its working directory, which is deleted afterwards. The source folders are symlinked into it,
since some scripts read the `.lean` files through relative paths. Only the working directory
changes: `lake -d <root>` still uses the repository's lakefile and `.lake` build, so nothing is
rebuilt.

-/

open System

/-!

## A. Running a script

-/

/-- The result of checking one script: a list of error messages, empty if the script passed. -/
abbrev Check := ExceptT (Array String) IO

/-- Fails the check with the given error message. -/
def fail {α} (msg : String) : Check α := throw #[msg]

/-- Fails the check with the given message unless `b` holds. -/
def ensure (b : Bool) (msg : String) : Check Unit := unless b do fail msg

/-- The last `n` lines of a string, indented, used to show the output of a failing script. -/
def tailLines (s : String) (n : Nat := 30) : String :=
  let lines := (s.trimAsciiEnd.toString.splitOn "\n")
  let dropped := lines.length - n
  let lines := lines.drop dropped
  let header := if dropped > 0 then s!"    ... ({dropped} lines omitted)\n" else ""
  header ++ "\n".intercalate (lines.map ("    " ++ ·))

/-- The context in which scripts are run: the root of the repository, and the Lean toolchain
of the repository. The toolchain must be passed explicitly, since `elan` otherwise chooses
the toolchain from the (temporary) working directory. -/
structure Ctx where
  /-- The root of the repository. -/
  root : FilePath
  /-- The contents of `lean-toolchain`. -/
  toolchain : String

/-- Runs `lake exe <exe> <args>` for the repository at `ctx.root`, with working directory `cwd`.
Fails if the script exits with a non-zero exit code or panics. -/
def runLakeExe (ctx : Ctx) (cwd : FilePath) (exe : String) (args : Array String) :
    Check IO.Process.Output := do
  let cmdStr := " ".intercalate ("lake exe" :: exe :: args.toList)
  let out ← IO.Process.output {
    cmd := "lake"
    args := #["-d", ctx.root.toString, "exe", exe] ++ args
    cwd := cwd
    env := #[("ELAN_TOOLCHAIN", some ctx.toolchain)] }
  if out.exitCode ≠ 0 then
    fail s!"`{cmdStr}` exited with code {out.exitCode}.\n  stderr:\n{tailLines out.stderr}\n  \
      stdout:\n{tailLines out.stdout}"
  if (out.stderr.splitOn "PANIC").length > 1 then
    fail s!"`{cmdStr}` panicked.\n  stderr:\n{tailLines out.stderr}"
  return out

/-- The source folders, which some scripts read through paths relative to the working
directory (e.g. `stats` counts the lines of `./Physlib/...`). -/
def sourceDirs : List String := ["Physlib", "PhyslibAlpha", "QuantumInfo"]

/-- Prepares the working directory `cwd` to look like the repository to the scripts: it makes
`docs/`, which `stats` and `informal` expect to exist, and symlinks the source folders.
`IO.FS.removeDirAll` does not follow symlinks, so deleting `cwd` leaves the sources intact. -/
def setUpWorkingDir (ctx : Ctx) (cwd : FilePath) : Check Unit := do
  IO.FS.createDirAll (cwd / "docs")
  for dir in sourceDirs do
    let out ← IO.Process.output {
      cmd := "ln", args := #["-s", (ctx.root / dir).toString, (cwd / dir).toString] }
    if out.exitCode ≠ 0 then
      fail s!"Could not symlink `{dir}` into the temporary directory:\n{tailLines out.stderr}"

/-- Reads the file `dir / path`, failing with a useful message if it was not made. -/
def readOutput (dir : FilePath) (path : String) : Check String := do
  let file := dir / path
  ensure (← file.pathExists) s!"The expected output file `{path}` was not made."
  let content ← IO.FS.readFile file
  ensure (!content.trimAscii.isEmpty) s!"The output file `{path}` is empty."
  return content

/-- Whether `s` contains `sub`. -/
def String.containsStr (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The number of occurrences of `sub` in `s`. -/
def String.countStr (s sub : String) : Nat := (s.splitOn sub).length - 1

/-!

## B. The checks on each script

-/

/-- Checks `lake exe make_tag`: it should print a single non-empty tag in the RFC 4648
Base32 alphabet. -/
def checkMakeTag (ctx : Ctx) (cwd : FilePath) : Check Unit := do
  let out ← runLakeExe ctx cwd "make_tag" #[]
  let tag := out.stdout.trimAscii.toString
  ensure (!tag.isEmpty) "`lake exe make_tag` printed no tag."
  ensure (tag.all fun c => ('A' ≤ c ∧ c ≤ 'Z') ∨ ('2' ≤ c ∧ c ≤ '7'))
    s!"`lake exe make_tag` printed `{tag}`, which is not a Base32 tag (characters `A-Z2-7`)."

/-- Checks `lake exe TODO_to_yml mkFile`: it should make `docs/_data/TODO.yml`, with a
category section and a non-empty list of TODO items each carrying a tag. -/
def checkTODOToYml (ctx : Ctx) (cwd : FilePath) : Check Unit := do
  let out ← runLakeExe ctx cwd "TODO_to_yml" #["mkFile"]
  ensure (out.stdout.containsStr "TODOList file made.")
    "`lake exe TODO_to_yml mkFile` did not report `TODOList file made.`."
  let yml ← readOutput cwd "docs/_data/TODO.yml"
  ensure (yml.startsWith "Category:\n") "`docs/_data/TODO.yml` does not start with `Category:`."
  ensure (yml.containsStr "\nTODOItem:\n") "`docs/_data/TODO.yml` has no `TODOItem:` section."
  let items := yml.countStr "\n  - file: "
  ensure (items > 0) "`docs/_data/TODO.yml` contains no TODO items."
  let tags := yml.countStr "\n    tag: "
  ensure (tags = items)
    s!"`docs/_data/TODO.yml` has {items} TODO items but {tags} tags."

/-- Checks `lake exe stats mkHTML`: it should print the statistics and make `docs/Stats.html`. -/
def checkStats (ctx : Ctx) (cwd : FilePath) : Check Unit := do
  let out ← runLakeExe ctx cwd "stats" #["mkHTML"]
  ensure (out.stdout.containsStr "Number of Files")
    "`lake exe stats mkHTML` did not print the statistics."
  ensure (out.stdout.containsStr "HTML file made.")
    "`lake exe stats mkHTML` did not report `HTML file made.`."
  let html ← readOutput cwd "docs/Stats.html"
  ensure (html.containsStr "<html" && html.containsStr "</html>")
    "`docs/Stats.html` is not a complete HTML document."
  ensure (html.containsStr "Number of Files")
    "`docs/Stats.html` does not contain the statistics."

/-- Checks `lake exe informal mkFile mkDot mkHTML`: it should make the Markdown file, the
DOT file and the HTML page of the informal dependency graph. -/
def checkInformal (ctx : Ctx) (cwd : FilePath) : Check Unit := do
  let out ← runLakeExe ctx cwd "informal" #["mkFile", "mkDot", "mkHTML"]
  for msg in ["Markdown file made.", "DOT file made.", "HTML file made."] do
    ensure (out.stdout.containsStr msg)
      s!"`lake exe informal mkFile mkDot mkHTML` did not report `{msg}`."
  let md ← readOutput cwd "docs/Informal.md"
  ensure (md.containsStr "# Informal definitions and lemmas")
    "`docs/Informal.md` is missing its title."
  ensure (md.containsStr "**Informal ")
    "`docs/Informal.md` lists no informal definitions or lemmas."
  let dot ← readOutput cwd "docs/InformalDot.dot"
  ensure (dot.startsWith "strict digraph G {" && dot.trimAsciiEnd.toString.endsWith "}")
    "`docs/InformalDot.dot` is not a complete `strict digraph G { ... }`."
  ensure (dot.containsStr " -> ") "`docs/InformalDot.dot` contains no dependency edges."
  let html ← readOutput cwd "docs/InformalGraph.html"
  ensure (html.startsWith "---\nlayout: default")
    "`docs/InformalGraph.html` is missing its Jekyll front matter."
  ensure (html.containsStr "InformalDot.dot")
    "`docs/InformalGraph.html` does not load `InformalDot.dot`."

/-!

## C. Main function

-/

/-- The scripts to test, with the command shown to the user. -/
def tests : List (String × (Ctx → FilePath → Check Unit)) := [
  ("lake exe make_tag", checkMakeTag),
  ("lake exe TODO_to_yml mkFile", checkTODOToYml),
  ("lake exe stats mkHTML", checkStats),
  ("lake exe informal mkFile mkDot mkHTML", checkInformal)]

def main (_ : List String) : IO UInt32 := do
  let root ← IO.currentDir
  unless ← (root / "lean-toolchain").pathExists do
    IO.eprintln "Error: run `lake exe auxillary_script_test` from the root of the repository."
    return 1
  let toolchain := (← IO.FS.readFile (root / "lean-toolchain")).trimAscii.toString
  let ctx : Ctx := {root, toolchain}
  let mut failures : Array String := #[]
  for ((name, check), i) in tests.zipIdx 1 do
    println! "\x1b[36m({i}/{tests.length}) {name}\x1b[0m"
    let result ← IO.FS.withTempDir fun dir => (setUpWorkingDir ctx dir *> check ctx dir).run
    match result with
    | .ok () => println! "\x1b[32mPassed.\x1b[0m"
    | .error errs =>
      failures := failures.push name
      for err in errs do
        println! "\x1b[31mError: {err}\x1b[0m"
  if failures.isEmpty then
    println! "\x1b[32mAll auxiliary scripts passed.\x1b[0m"
    return 0
  println! "\x1b[31mFailed: {", ".intercalate failures.toList}.\x1b[0m"
  println! "\x1b[2mIf a script cannot find an `.olean` file, run `lake build Physlib QuantumInfo \
    PhyslibAlpha` first. If an `.olean` file has an incompatible header, it was built by another \
    toolchain: run `lake exe get_cache`.\x1b[0m"
  return 1
