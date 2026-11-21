/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/

def main (args : List String) : IO UInt32 := do

  println! "\x1b[36m(1/7) Style lint \x1b[0m"
  println! "\x1b[2mThis linter is not checked by GitHub but if you have time please fix these errors.\x1b[0m"
  let styleLint ← IO.Process.output {cmd := "lake", args := #["exe", "style_lint"]}
  println! styleLint.stdout

  println! "\x1b[36m(2/7) Building \x1b[0m"
  let build ← IO.Process.output {cmd := "lake", args := #["build"]}
  let mut failed := build.exitCode != 0
  if failed then
    IO.print build.stdout
    IO.eprint build.stderr
    println! "\x1b[31mError: Build failed. Run `lake build` to see the errors.\x1b[0m\n"
  else
    println! "\x1b[32mBuild is successful.\x1b[0m\n"

  println! "\x1b[36m(3/7) File imports \x1b[0m"
  let importCheck ← IO.Process.output {cmd := "lake", args := #["exe", "check_file_imports"]}
  println! importCheck.stdout
  IO.eprint importCheck.stderr
  failed := importCheck.exitCode != 0 || failed

  println! "\x1b[36m(3/7) Illegal Imports\x1b[0m"
  let noAlphaImports ← IO.Process.output {cmd := "lake", args := #["exe", "noAlphaImports"]}
  println! noAlphaImports.stdout
  IO.eprint noAlphaImports.stderr
  failed := noAlphaImports.exitCode != 0 || failed

  println! "\x1b[36m(3/7) Ensuring all PhyslibAlpha modules imported\x1b[0m"
  let alphaFileImports ← IO.Process.output {cmd := "lake", args := #["exe", "alphaFileImports"]}
  println! alphaFileImports.stdout
  IO.eprint alphaFileImports.stderr
  failed := alphaFileImports.exitCode != 0 || failed

  println! "\x1b[36m(3/7) ForMathlib imports and uses\x1b[0m"
  let forMathlibLint ← IO.Process.output {cmd := "lake", args := #["exe", "forMathlib_lint"]}
  println! forMathlibLint.stdout
  IO.eprint forMathlibLint.stderr
  failed := forMathlibLint.exitCode != 0 || failed

  println! "\x1b[36m(4/7) TODO tag duplicates \x1b[0m"
  let todoCheck ← IO.Process.output {cmd := "lake", args := #["exe", "check_dup_tags"]}
  println! todoCheck.stdout
  IO.eprint todoCheck.stderr
  failed := todoCheck.exitCode != 0 || failed

  println! "\x1b[36m(5/7) Pseudo attribute linter \x1b[0m"
  let pseudoCheck ← IO.Process.output {cmd := "lake", args := #["exe", "pseudo_lint"]}
  println! pseudoCheck.stdout
  failed := pseudoCheck.exitCode != 0 || failed
  println! pseudoCheck.stderr

  println! "\x1b[36m(5/7) Theorem and lemma linter \x1b[0m"
  let theoremCheck ← IO.Process.output {cmd := "lake", args := #["exe", "theorem_lint"]}
  println! theoremCheck.stdout
  failed := theoremCheck.exitCode != 0 || failed
  println! theoremCheck.stderr

  println! "\x1b[36m(5/7) API map linter \x1b[0m"
  let apiMapCheck ← IO.Process.output {cmd := "lake", args := #["exe", "api_map_lint"]}
  println! apiMapCheck.stdout
  IO.eprint apiMapCheck.stderr
  failed := apiMapCheck.exitCode != 0 || failed

  if ¬ "--fast" ∈ args then
    println! "\x1b[36m(6/7) Lean linter \x1b[0m"
    println! "\x1b[2mExpect this linter to take a while to run, it can be skipped with
      lake exe lint_all --fast"
    println! "You can manually perform this linter by placing `#lint` at the end of the files you have modified.\x1b[0m"
    let leanCheck ← IO.Process.output {cmd := "lake", args := #["exe", "runPhyslibLinters", "Physlib"]}
    println! leanCheck.stdout
    IO.eprint leanCheck.stderr
    failed := leanCheck.exitCode != 0 || failed

    println! "\x1b[36m(7/7) Transitive imports \x1b[0m"
    println! "\x1b[2mExpect this linter to take a while to run, it can be skipped with
        lake exe lint_all --fast\x1b[0m"
    let redundentImports ← IO.Process.output {cmd := "lake", args := #["exe", "redundant_imports"]}
    println! redundentImports.stdout
    IO.eprint redundentImports.stderr
    failed := redundentImports.exitCode != 0 || failed



  return if failed then 1 else 0
