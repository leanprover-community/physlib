/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/

/-!
# Windows test

A minimal executable reproducing how the Physlib executables (e.g. `lake exe lint_all` and
`lake exe get_cache`) fail to build on Windows machines without a C compiler.

The executable itself does nothing. The failure occurs when building it: Lake links the
`extern_lib`s of every package in the workspace into every executable, and some dependencies
(`leansqlite` and, on Windows, `UnicodeBasic`, both pulled in by `doc-gen4`) compile their
C code with `cc` rather than the `clang` bundled with Lean. Without `cc` on the `PATH` the build
fails with `failed to execute 'cc'`.

Since it imports nothing, building it does not require Mathlib or Physlib to be built, so it
can be used to quickly test fixes. It is run by `.github/workflows/windows-test.yml`.

It can be run from the terminal using `lake exe windows_test`.
-/

def main : IO UInt32 := do
  IO.println "Built and ran a Physlib executable successfully."
  pure 0
