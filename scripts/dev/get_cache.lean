/-
Copyright (c) 2026 Alex Zughaid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Zughaid
-/

import Lean

/-!
# Get cache

Downloads everything needed before a first build, so that `lake build` does
not have to compile from source.

Fetches both halves: Mathlib's prebuilt files (via Mathlib's own
`lake exe cache get`) and Physlib's own (via Lake's built-in `lake cache`,
backed by the project's R2 bucket -- see `lake-cache.toml` and
`docs/cache-setup.md`). Pass `--no-mathlib` to skip getting Mathlib's cache,
and `--no-alpha` to skip PhyslibAlpha's.

It can be run from the terminal using `lake exe get_cache`.

If you have no internet, `lake build` is just fine but will take much longer without this step
first.
-/

def helpText : String :=
"Download everything needed before a first build, so that `lake build` does \
not have to compile from source.

Usage:
  lake exe get_cache                fetch everything needed
  lake exe get_cache --no-mathlib   skip Mathlib, fetch only Physlib's
  lake exe get_cache --no-alpha     skip PhyslibAlpha's cache
"

/-- `println`, then flush stdout immediately. Without this, messages printed
before spawning a subprocess can sit in a buffer and appear out of order (or
not at all until the child exits) whenever stdout is piped rather than a
terminal -- e.g. `lake exe get_cache | tee log.txt`. -/
def say (s : String) : IO Unit := do
  IO.println s
  (← IO.getStdout).flush

/-- Run a subprocess, inheriting stdout/stderr, with optional extra
environment variables. Returns whether it exited successfully. -/
def runStreamed (cmd : String) (args : Array String)
    (env : Array (String × Option String) := #[]) : IO Bool := do
  let child ← IO.Process.spawn { cmd, args, env }
  return (← child.wait) == 0

/-- Whether the `.olean` at `path` was written by a different Lean build than
the one running this program. Every `.olean` starts with the marker `olean` and
a header recording the githash of the Lean that wrote it, and Lean refuses to
load one with any other. A file without the marker is never reported stale, so
a change of header layout makes this miss stale files rather than delete
current ones. -/
def isStaleOlean (path : System.FilePath) : IO Bool := do
  let hash := Lean.githash.toUTF8
  if hash.size == 0 then return false
  let header ← (← IO.FS.Handle.mk path .read).read 128
  unless (header.extract 0 5).toList == "olean".toUTF8.toList do return false
  let found := (List.range (header.size + 1 - hash.size)).any fun i =>
    (header.extract i (i + hash.size)).toList == hash.toList
  return !found

/-- Delete the build folder of every dependency whose `.olean` files were
written by another Lean toolchain, as happens right after a toolchain bump.
Such files can never be loaded again, and the rest are unpacked again from
Mathlib's cache, so nothing is lost; but on Windows they block unpacking it,
as they are read-only hard links into Lake's artifact cache, which cannot be
overwritten. Each folder is renamed before it is deleted: on Windows a file
still open elsewhere lingers after deletion and blocks creating a new one at
its path, and the rename moves it out of the way of the unpacking. Returns
whether every deletion succeeded. -/
def removeStaleDepBuilds : IO Bool := do
  let pkgs : System.FilePath := ".lake" / "packages"
  unless ← pkgs.pathExists do return true
  let mut ok := true
  for pkg in ← pkgs.readDir do
    let build := pkg.path / ".lake" / "build"
    let lib := build / "lib" / "lean"
    unless ← lib.pathExists do continue
    -- Every file is checked, not just one: a build interrupted after a toolchain
    -- bump (e.g. by an editor rebuilding) leaves a mix of stale and current files.
    let oleans := (← lib.walkDir).filter (·.extension == some "olean")
    unless ← oleans.anyM isStaleOlean do continue
    say s!"  removing {build}: built by another Lean toolchain"
    let old := pkg.path / ".lake" / "build-stale"
    try
      if ← old.pathExists then IO.FS.removeDirAll old
      IO.FS.rename build old
      IO.FS.removeDirAll old
    catch e =>
      say s!"  could not remove it: {e}"
      ok := false
  return ok

/-- The options this program understands. Anything else is rejected up
front, rather than silently ignored and treated as "no flags given". -/
def knownFlags : List String := ["--help", "-h", "--no-mathlib", "--no-alpha"]

/-- The current toolchain as a cache-scope path component: `/` and `:` become
`-`, whitespace is dropped (matching the workflow's `tr -d '[:space:]'`). -/
def toolchainTag : IO String := do
  let raw ← IO.FS.readFile "lean-toolchain"
  return raw.foldl (init := "") fun acc c =>
    if c.isWhitespace then acc
    else if c == '/' || c == ':' then acc.push '-'
    else acc.push c

/-- The cache scope for one half of the project. Each half gets its own so the
two CI jobs do not overwrite each other's mappings; the toolchain is a path
component because Lake ignores `--toolchain` for verbatim scopes.
`.github/workflows/publish-cache.yml` builds the same strings. -/
def scopeFor (tc : String) (half : String) : String :=
  s!"physlib-master/{tc}/{half}"

def main (args : List String) : IO UInt32 := do
  if let some bad := args.find? (!knownFlags.contains ·) then
    say s!"Unknown option: {bad} (try --help)"
    return 0

  if args.contains "--help" || args.contains "-h" then
    say helpText
    return 0

  unless ← System.FilePath.pathExists "lakefile.toml" do
    say "Run this from the root of the Physlib repository."
    return 0

  let skipMathlib := args.contains "--no-mathlib"
  let skipAlpha := args.contains "--no-alpha"

  let mut mathlibOk := true
  if !skipMathlib then
    unless ← removeStaleDepBuilds do
      say "  (if a file is in use, a program such as your editor's Lean server may hold it;"
      say "  stop it and run this again)"
    say "Fetching Mathlib's prebuilt files ..."
    mathlibOk ← runStreamed "lake" #["exe", "cache", "get"]
    unless mathlibOk do
      say "  could not fetch Mathlib's cache -- continuing anyway."
      say "  ('lake build' may then have to compile Mathlib, which is slow.)"
    say ""

  let cwd ← IO.currentDir
  let configPath := (cwd / "lake-cache.toml").toString
  let tc ← toolchainTag

  say "Fetching Physlib's prebuilt files ..."
  let ok ← runStreamed "lake" #["cache", "get", s!"--scope={scopeFor tc "physlib"}"]
    #[("LAKE_CONFIG", some configPath)]

  -- Published under its own scope, so it needs its own fetch.
  unless skipAlpha do
    say ""
    say "Fetching PhyslibAlpha's prebuilt files ..."
    unless ← runStreamed "lake" #["cache", "get", s!"--scope={scopeFor tc "alpha"}"]
      #[("LAKE_CONFIG", some configPath)] do
      say "  could not fetch PhyslibAlpha's cache -- continuing anyway."
      say "  ('lake build PhyslibAlpha' would then compile it from source.)"

  -- Repeated here because the failure itself scrolls away above Physlib's output.
  unless mathlibOk do
    say ""
    say "Could not fetch Mathlib's cache (see the errors near the top), so 'lake build'"
    say "would compile Mathlib from source, which takes hours."
    say "If the errors say access denied (os error 5), a program such as your editor's"
    say "Lean server may hold the files; stop it and run this again."
  if ok && mathlibOk then
    say ""
    say "Done. Now run: lake build"
  else if !ok then
    say ""
    say "Could not fetch Physlib's cache. This is not a fatal error -- run 'lake build'"
    say "as usual, it will just take longer, compiling the whole project from source."
  return 0
