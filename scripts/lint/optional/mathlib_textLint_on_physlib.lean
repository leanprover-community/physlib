/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Tactic.Linter.TextBased
import Cli.Basic
/-!

# Text based style linters from Mathlib

This file is a copy of the `./scripts/lint_style.lean` executable from mathlib, adapted
to run text-based style linters from mathlib on Physlib.

That file is copyright Michael Rothgang, and is released under the Apache 2.0 license.
It is authored by Michael Rothgang.

-/

open Cli

/-- Implementation of the `lint_style` command line program. -/
def lintStyleCli (args : Cli.Parsed) : IO UInt32 := do
  let mode : OutputSetting := match (args.hasFlag "update", args.hasFlag "github") with
    | (true, _) => OutputSetting.update
    | (false, true) => OutputSetting.print ErrorFormat.github
    | (false, false) => OutputSetting.print ErrorFormat.humanReadable
  let mut allModules := #[]
  for s in ["Physlib.lean"] do
    allModules := allModules.append ((← IO.FS.lines s).filter (!·.containsSubstr "Batteries")
      |>.map (·.stripPrefix "import "))
  let numberErrorFiles ← lintModules allModules mode
  return min numberErrorFiles 125

/-- Setting up command line options and help text for `lake exe lint_style`. -/
-- so far, no help options or so: perhaps that is fine?
def physlib_lint_style : Cmd := `[Cli|
  lint_style VIA lintStyleCli; ["0.0.1"]
  "Run text-based style linters on every Lean file in Physlib (adapted from mathlib's lint_style).
  Print errors about any unexpected style errors to standard output."

  FLAGS:
    github;     "Print errors in a format suitable for github problem matchers\n\
                 otherwise, produce human-readable output"
    update;     "Print errors solely for the style exceptions file"
]

/-- The entry point to the `lake exe mathlib_textLint_on_physlib` command. -/
def main (args : List String) : IO UInt32 := do physlib_lint_style.validate args
