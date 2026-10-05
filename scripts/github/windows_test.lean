/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/

/-!
# Windows test

A minimal executable checking that the Physlib executables (e.g. `lake exe lint_all` and
`lake exe get_cache`) can be built on Windows machines without a C compiler.

The executable itself does nothing; the check is that it builds. Lake links the `extern_lib`s of
every dependency of Physlib into every executable, and some packages compile their C code with
`cc` rather than the `clang` bundled with Lean. For example `leansqlite` and, on Windows,
`UnicodeBasic`, both dependencies of `doc-gen4`. Without `cc` on the `PATH` the build then fails
with `failed to execute 'cc'`. For this reason `doc-gen4` is a dependency of the nested
`docbuild` project rather than of Physlib.

Since it imports nothing, building it does not require Mathlib or Physlib to be built.
It is run by `.github/workflows/windows-test.yml`.

It can be run from the terminal using `lake exe windows_test`.
-/

def main : IO UInt32 := do
  IO.println "Built and ran a Physlib executable successfully."
  pure 0
