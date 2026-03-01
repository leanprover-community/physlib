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
  let s1 := "Build completed successfully"
  let s2 := build.stdout
  if ¬ (s2.splitOn s1).length = 2  then
    println! "\x1b[31mError: Build failed. Run `lake build` to see the errors.\x1b[0m\n"
  else
    println! "\x1b[32mBuild is successful.\x1b[0m\n"

  println! "\x1b[36m(3/7) File imports \x1b[0m"
  let importCheck ← IO.Process.output {cmd := "lake", args := #["exe", "check_file_imports"]}
  println! importCheck.stdout

  println! "\x1b[36m(4/7) TODO tag duplicates \x1b[0m"
  let todoCheck ← IO.Process.output {cmd := "lake", args := #["exe", "check_dup_tags"]}
  println! todoCheck.stdout

  println! "\x1b[36m(5/7) Sorry and pseudo attribute linter \x1b[0m"
  let sorryPseudoCheck ← IO.Process.output {cmd := "lake", args := #["exe", "sorry_lint"]}
  println! sorryPseudoCheck.stdout

  if ¬ "--fast" ∈ args then
    println! "\x1b[36m(6/7) Lean linter \x1b[0m"
    println! "\x1b[2mExpect this linter to take a while to run, it can be skipped with
      lake exe lint_all --fast"
    println! "You can manually perform this linter by placing `#lint` at the end of the files you have modified.\x1b[0m"
    let leanCheck ← IO.Process.output {cmd := "lake", args := #["exe", "runPhysLeanLinters", "PhysLean"]}
    println! leanCheck.stdout

    println! "\x1b[36m(7/7) Transitive imports \x1b[0m"
    println! "\x1b[2mExpect this linter to take a while to run, it can be skipped with
        lake exe lint_all --fast\x1b[0m"
    let redundentImports ← IO.Process.output {cmd := "lake", args := #["exe", "redundant_imports"]}
    println! redundentImports.stdout



  pure 0
