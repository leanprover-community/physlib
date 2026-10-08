/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
/-!

# Building executables on Windows without a C compiler

A minimal executable checking that the Physlib executables build on Windows without `cc`.

## i. Overview

This file is a minimal executable checking that the Physlib executables (e.g. `lake exe lint_all`
and `lake exe get_cache`) can be built on Windows machines without a C compiler.

The executable itself does nothing; the check is that it builds. Lake links the `extern_lib`s of
every dependency of Physlib into every executable, and some packages compile their C code with
`cc` rather than the `clang` bundled with Lean. For example `leansqlite` and, on Windows,
`UnicodeBasic`, both dependencies of `doc-gen4`. Without `cc` on the `PATH` the build then fails
with `failed to execute 'cc'`. For this reason `doc-gen4` is a dependency of the nested
`docs/build` project rather than of Physlib.

Since it imports nothing, building it does not require Mathlib or Physlib to be built.
Run it from the root of the repository with

  `lake exe windows_test`

This test is run in CI by `.github/workflows/windows-test.yml`, with `cc` removed from the `PATH`,
and must pass.

## ii. Key results

- `main` is the executable, which prints a message and exits successfully.

## iii. Table of contents

- A. The executable

## iv. References

* https://leanprover.zulipchat.com/#narrow/channel/479953-Physlib/topic/A.20cache.20for.20PhysLib/with/629244227

-/

/-!

## A. The executable

-/

def main (_ : List String) : IO UInt32 := do
  IO.println "\x1b[32mBuilt and ran a Physlib executable successfully.\x1b[0m"
  return 0
