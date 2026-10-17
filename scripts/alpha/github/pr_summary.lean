/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Lean
/-!

# PR summary

A script which prints, as Markdown, what a pull-request changes: its files and its declarations.

## i. Overview

`lake exe pr_summary <base> <head>` prints a summary of the changes `head` makes to `base`, for
a reviewer to read before the diff. The [`PRMessage`](../../../.github/workflows/PRMessage.yml)
workflow runs it and posts the result in the comment it leaves on every pull-request, updating
that comment on every push.

**What it runs.** The script runs `git` in the current directory with the following read-only
commands, and nothing else. It writes the summary to standard output and progress messages to
standard error. It does not build, import or run anything from the pull-request: it reads the
diff as text, which is what lets the workflow run it, built from `master`, on pull-requests from
forks.

```
git rev-parse <head>                                the commit the links point into
git merge-base <base> <head>                        the commit the removed lines belong to
git diff --name-status -M       <base>...<head>     which files changed, and how
git diff --numstat --no-renames <base>...<head>     lines added to and removed from each file
git diff --unified=0 -M         <base>...<head>     the changed lines themselves
```

**What it prints.** For a pull-request which adds one lemma to one file:

````markdown
```diff
Found differences:
@@ Physlib.Foo @@
! module modified Physlib.Foo (+3 -0)
+ added lemma Foo.bar
2 differences
```

<a sentence on what the block misses; see `caveat`>
````

The block follows the format of [leaff](https://github.com/alexjbest/leaff): one line per
change, `+` for an addition, `-` for a removal and `!` for a modification, grouped under
`@@ <module> @@` headers, with the most important changes first. A pull-request which writes a
result with `theorem` gets a call-out above the block, since Physlib reserves `theorem` for
named results of the physics literature and `theorem_lint` requires each to be listed in
`scripts/lint/exemptions/Theorems.txt`. Section F.9 shows the whole output for a small diff.

**How it works.** `summarise` is a pure function from the text of the three `git diff` outputs
to the Markdown, and `gitSummary` is the only thing which runs `git`. In between:

1. `parseNameStatus` and `parseNumstat` read which files changed and by how many lines (B).
2. `parseDiff` keeps the added (`+`) and removed (`-`) lines of the diff which start a
   declaration: a line beginning, after its attributes and modifiers, with `lemma`, `def`, … and
   a name (C.1–C.3).
3. `declDiff` pairs the removed with the added declaration lines by name (C.4):

   | the name is on | the lines are | reported as |
   | - | - | - |
   | added lines only | | added |
   | removed lines only | | removed |
   | both | the same | moved |
   | both | different | restated |

4. `diffBlock` lists the changes in the format of leaff, and `theoremCallout` adds the
   call-out (D).

**What it misses.** The scan is textual, so it is a guide and not a proof. It does not see

- a declaration whose keyword and name are on different lines;
- a declaration which does not start at the beginning of its line;
- namespaces: the `foo` of `namespace A` and the `foo` of `namespace B` are one name to it;
- a change to a proof, or to the body of a definition, which is deliberate.

**Running it.** From the root of a clone which has both revisions:

```
lake exe pr_summary                 -- origin/master...HEAD
lake exe pr_summary <base>          -- <base>...HEAD
lake exe pr_summary <base> <head>
```

Some merged pull-requests to try, each of a different shape, given by their merge commit:

```
lake exe pr_summary c3964f48db4b~1 c3964f48db4b   -- #1776: a new file, nine declarations added
lake exe pr_summary 0aeb3dc7e249~1 0aeb3dc7e249   -- #1792: sixteen files renamed, many moves
lake exe pr_summary be0f21e5002d~1 be0f21e5002d   -- #1788: one declaration restated
```

The links always point into `leanprover-community/physlib`, so those made from a commit which is
only in a clone or a fork do not resolve.

## ii. Key results

- `PRSummary.summarise` is the whole summary, as a pure function of the `git diff` outputs.
- `PRSummary.declHeads` decides whether a line of source starts a declaration.
- `PRSummary.declDiff` classifies each declaration as added, removed, moved or restated.
- `PRSummary.diffBlock` lists the changes in the format of leaff.
- `PRSummary.git` is the only function which runs a command.

## iii. Table of contents

- A. Strings, Markdown and links
- B. The files a pull-request changes
  - B.1. Reading `git diff --name-status`
  - B.2. Reading `git diff --numstat`
- C. The declarations a pull-request changes
  - C.1. Stripping attributes and modifiers from a line
  - C.2. The declarations a line starts
  - C.3. The declaration lines of a diff
  - C.4. Classifying the declarations
- D. Rendering the summary
  - D.1. The diff block
  - D.2. The call-out about `theorem`
  - D.3. The summary
- E. Running `git`
- F. Tests
  - F.1. Strings, Markdown and links
  - F.2. Reading `git diff --name-status` and `--numstat`
  - F.3. Stripping attributes and modifiers from a line
  - F.4. The declarations a line starts
  - F.5. The declaration lines of a diff
  - F.6. Classifying the declarations
  - F.7. The diff block
  - F.8. The call-out about `theorem`
  - F.9. The whole summary

## iv. References

* [leaff](https://github.com/alexjbest/leaff), Alex J. Best's diff tool for Lean environments,
  whose output this script imitates: a `diff` block of `+ added`, `- removed` and `!` lines
  under `@@ module @@` headers, most important first. Leaff compares the compiled environments,
  so it sees what this script cannot, such as a changed proof, type or attribute, at the cost of
  building both revisions.
* The `scripts/pr_summary/declarations_diff.sh` script of
  [`mathlib-ci`](https://github.com/leanprover-community/mathlib-ci), whose approach to pairing
  the removed and added declarations this script follows.

-/

namespace PRSummary

/-! ## A. Strings, Markdown and links -/

/-- `s` without its first `n` characters. -/
def dropChars (s : String) (n : Nat) : String := (s.drop n).copy

/-- `s` without surrounding whitespace. -/
def trim (s : String) : String := s.trimAscii.copy

/-- `s` without leading whitespace. -/
def trimStart (s : String) : String := s.trimAsciiStart.copy

/-- `s` without trailing whitespace. -/
def trimEnd (s : String) : String := s.trimAsciiEnd.copy

/-- `n` and `noun`, pluralised unless `n` is one: `1 file`, `2 files`. -/
def plural (n : Nat) (noun : String) : String :=
  if n == 1 then s!"{n} {noun}" else s!"{n} {noun}s"

/-- The non-zero counts of `items` with their labels, as in `2 added, 1 removed`. -/
def tally (items : Array (Nat × String)) : String :=
  ", ".intercalate ((items.filter (·.1 > 0)).map (fun (n, label) => s!"{n} {label}")).toList

/-- `s` as a Markdown code span, or an em dash if `s` is empty. -/
def code (s : String) : String := if s.isEmpty then "—" else s!"`{s}`"

/-- The first `limit` of `lines`, then a line counting the rest. GitHub caps a comment at 65536
characters. -/
def truncate (lines : Array String) (limit : Nat) : Array String :=
  if lines.size ≤ limit then lines
  else lines.take limit ++
    #[s!"… and {plural (lines.size - limit) "further line"}, left out to keep this short."]

/-- The repository the links point into. -/
def repository : String := "leanprover-community/physlib"

/-- The two commits being compared. A removed line is linked in `base`, since it is no longer in
`head`; everything else is linked in `head`. -/
structure Source where
  /-- The commit the removed lines belong to: the merge base of the two revisions. -/
  base : String := ""
  /-- The commit the added lines belong to. -/
  head : String := ""
  deriving Repr, DecidableEq, Inhabited

/-- `text` linked to `file` in `repository`, at line `line` unless that is zero, in `src.head` if
`added` and in `src.base` otherwise. -/
def Source.link (src : Source) (text file : String) (added : Bool) (line : Nat := 0) : String :=
  let commit := if added then src.head else src.base
  let anchor := if line == 0 then "" else s!"#L{line}"
  s!"[{text}](https://github.com/{repository}/blob/{commit}/{file}{anchor})"

/-! ## B. The files a pull-request changes -/

/-- How a file changed, as `git diff --name-status` reports it. -/
inductive FileStatus where
  | added
  | removed
  | modified
  /-- Renamed from `oldPath`. -/
  | renamed (oldPath : String)
  /-- Copied from `oldPath`. -/
  | copied (oldPath : String)
  deriving Repr, DecidableEq, Inhabited

/-- The order in which the statuses are reported, as in leaff: additions, removals, then
modifications. -/
def FileStatus.rank : FileStatus → Nat
  | .added => 0
  | .removed => 1
  | .renamed .. => 2
  | .copied .. => 3
  | .modified => 4

/-- A file the pull-request changes. -/
structure FileChange where
  /-- The path after the change, or, for a removed file, before it. -/
  path : String
  status : FileStatus
  /-- Lines added; `none` for a binary file. -/
  insertions : Option Nat := none
  /-- Lines removed; `none` for a binary file. -/
  deletions : Option Nat := none
  deriving Repr, DecidableEq, Inhabited

/-- Files are reported by status, then by path. -/
def FileChange.lt (c d : FileChange) : Bool :=
  c.status.rank < d.status.rank || c.status.rank == d.status.rank && c.path < d.path

/-- The paths the diff may give for lines of the file: its path, and, if it was renamed or
copied, its old path. -/
def FileChange.paths (c : FileChange) : List String :=
  match c.status with
  | .renamed oldPath | .copied oldPath => [c.path, oldPath]
  | _ => [c.path]

/-! ### B.1. Reading `git diff --name-status`

Each line is a status letter and a path, separated by a tab; a rename or a copy has the old and
the new path, and its letter carries a similarity score, as in `R100`:

```
A	Physlib/New.lean
M	Physlib/Changed.lean
R098	Physlib/Old.lean	Physlib/Renamed.lean
```
-/

/-- The file change one line records, or `none` for a line which is not one. -/
def parseNameStatusLine (line : String) : Option FileChange :=
  match (line.splitOn "\t").map trim with
  | [status, path] =>
    match status.front with
    | 'A' => some { path, status := .added }
    | 'D' => some { path, status := .removed }
    -- `T` is a change of file type, reported as a modification.
    | 'M' | 'T' => some { path, status := .modified }
    | _ => none
  | [status, oldPath, path] =>
    match status.front with
    | 'R' => some { path, status := .renamed oldPath }
    | 'C' => some { path, status := .copied oldPath }
    | _ => none
  | _ => none

/-- The file changes recorded by the lines of `git diff --name-status`. -/
def parseNameStatus (lines : Array String) : Array FileChange :=
  lines.filterMap parseNameStatusLine

/-! ### B.2. Reading `git diff --numstat`

Each line is the lines added, the lines removed and the path, separated by tabs; both counts
are `-` for a binary file:

```
40	0	Physlib/New.lean
-	-	docs/figure.png
```
-/

/-- The path and the two counts one line records, or `none` for a line which is not one. -/
def parseNumstatLine (line : String) : Option (String × Option Nat × Option Nat) :=
  match (line.splitOn "\t").map trim with
  | [insertions, deletions, path] => some (path, insertions.toNat?, deletions.toNat?)
  | _ => none

/-- The counts recorded by the lines of `git diff --numstat`. -/
def parseNumstat (lines : Array String) : Array (String × Option Nat × Option Nat) :=
  lines.filterMap parseNumstatLine

/-- `changes` with the counts of `counts` filled in by path. The counts come from a diff made
with `--no-renames`, in which a renamed file is counted under its new path. -/
def withLineCounts (changes : Array FileChange)
    (counts : Array (String × Option Nat × Option Nat)) : Array FileChange :=
  changes.map fun c =>
    match counts.find? (·.1 == c.path) with
    | some (_, insertions, deletions) => { c with insertions, deletions }
    | none => c

/-! ## C. The declarations a pull-request changes -/

/-! ### C.1. Stripping attributes and modifiers from a line

A declaration keyword may be preceded by attributes and modifiers, as in
`@[simp] protected lemma foo`, or by `open Foo in` or `set_option … in`. `normalise` removes
them, so that the keyword is at the start of the line.
-/

/-- The modifiers which may precede a declaration keyword. -/
def modifiers : Array String :=
  #["private", "protected", "public", "noncomputable", "nonrec", "partial", "unsafe", "scoped",
    "local"]

/-- The brackets which open a group. -/
def openBrackets : List Char := ['(', '[', '{', '⟨', '⦃']

/-- The brackets which close a group. -/
def closeBrackets : List Char := [')', ']', '}', '⟩', '⦄']

/-- `cs` after the bracket which closes the group `depth` brackets deep, or `none` if the group
is not closed in `cs`. -/
def afterCloseBracket (cs : List Char) (depth : Nat) : Option (List Char) :=
  match cs with
  | [] => none
  | c :: rest =>
    if openBrackets.contains c then afterCloseBracket rest (depth + 1)
    else if closeBrackets.contains c then
      if depth ≤ 1 then some rest else afterCloseBracket rest (depth - 1)
    else afterCloseBracket rest depth

/-- `s` without its leading bracketed group, if it starts with a group which is closed. -/
def dropBalanced? (s : String) : Option String :=
  match s.toList with
  | c :: rest =>
    if openBrackets.contains c then (afterCloseBracket rest 1).map String.ofList else none
  | [] => none

/-- `s` without its leading `@[…]`, if it has one. -/
def dropAttribute? (s : String) : Option String :=
  if s.startsWith "@[" then dropBalanced? (dropChars s 1) else none

/-- `s` without its leading modifier, if it has one. -/
def dropModifier? (s : String) : Option String :=
  modifiers.findSome? fun m =>
    if s.startsWith (m ++ " ") then some (dropChars s (m.length + 1)) else none

/-- `s` without its leading `open … in` or `set_option … in`, if it has one. -/
def dropScopePrefix? (s : String) : Option String :=
  if s.startsWith "open " || s.startsWith "set_option " then
    match s.splitOn " in " with
    | _ :: rest@(_ :: _) => some (" in ".intercalate rest)
    | _ => none
  else none

/-- `s` with every leading attribute, modifier and `… in` prefix removed. -/
def normalise (s : String) : String := Id.run do
  let mut s := trimEnd s
  -- Each step shortens `s`, so the loop ends before the bound.
  for _ in [0:s.length] do
    match dropAttribute? s <|> dropModifier? s <|> dropScopePrefix? s with
    | some t => s := trimStart t
    | none => break
  return s

/-! ### C.2. The declarations a line starts

A line starts a declaration if it is not indented and, once normalised, begins with one of the
keywords below followed by a name. The name is the first token after the keyword, except that

- `class inductive` is two words;
- `alias ⟨a, b⟩ := c` declares `a` and `b`, with `_` for a direction left unnamed;
- `instance` may put its priority before its name, and may have no name at all, in which case
  the declaration is recorded by its signature.
-/

/-- The keywords which start a declaration. `remark`, `informal_definition` and
`informal_lemma` are Physlib's own. -/
def declKeywords : Array String :=
  #["theorem", "lemma", "def", "abbrev", "instance", "structure", "class", "inductive",
    "alias", "opaque", "axiom", "remark", "informal_definition", "informal_lemma"]

/-- The characters which end a name. -/
def nameStop : List Char :=
  [' ', '\t', '(', ')', '[', ']', '{', '}', '⟨', '⟩', '⦃', '⦄', ':', '=', ',', '"']

/-- The leading token of `s`: its characters up to the first in `nameStop`. -/
def firstToken (s : String) : String := (s.takeWhile fun c => !nameStop.contains c).copy

/-- Whether `s` starts like a name: with a letter, an underscore or a non-ASCII character, as in
`ψ_eq`. A `⟨` or `{` starts a signature instead. -/
def isIdentifier (s : String) : Bool :=
  !s.isEmpty && (s.front.isAlpha || s.front == '_' || s.front.val > 127)

/-- `s` up to its first `:=` outside brackets: the `:=` of `(priority := 100)` is not the one
which starts the body. -/
def beforeAssignment (s : String) : String := Id.run do
  let cs := s.toList
  let mut depth := 0
  let mut out : Array Char := #[]
  for (c, i) in cs.zipIdx do
    if openBrackets.contains c then depth := depth + 1
    else if closeBrackets.contains c then depth := depth - 1
    else if depth == 0 && c == ':' && cs[i + 1]? == some '=' then break
    out := out.push c
  return String.ofList out.toList

/-- The signature in `s`, the part of a line after its keyword: what precedes the body, with a
trailing `where` dropped. -/
def signature (s : String) : String :=
  let s := trimEnd (beforeAssignment s)
  trimEnd (((s.dropSuffix? " where").map (·.copy)).getD s)

/-- A declaration a line starts. -/
structure DeclHead where
  keyword : String
  /-- The name, or, for an anonymous `instance`, the signature. -/
  name : String
  /-- Whether `name` is a signature rather than a name. -/
  anonymous : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- `h` as the report shows it: `lemma foo`, or `instance : Foo X`. -/
def DeclHead.display (h : DeclHead) : String := s!"{h.keyword} {h.name}"

/-- The keyword `line` starts with and the rest of the line, or `none`. -/
def splitKeyword? (line : String) : Option (String × String) := do
  let keyword ← declKeywords.find? fun k => line.startsWith (k ++ " ")
  let rest := trimStart (dropChars line (keyword.length + 1))
  if keyword == "class" && rest.startsWith "inductive " then
    return ("class inductive", trimStart (dropChars rest 10))
  return (keyword, rest)

/-- The declaration `keyword` followed by `rest` starts, if `rest` starts with a name. -/
def namedHead (keyword rest : String) : Array DeclHead :=
  let name := firstToken rest
  if isIdentifier name then #[{ keyword, name }] else #[]

/-- The declarations `alias ⟨a, b⟩ := c` starts, given the `⟨a, b⟩ := c`. -/
def aliasHeads (rest : String) : Array DeclHead :=
  let inner := ((dropChars rest 1).splitOn "⟩").headD ""
  (inner.splitOn ",").toArray.filterMap fun name =>
    let name := trim name
    if isIdentifier name && name != "_" then some { keyword := "alias", name } else none

/-- The declaration `instance` followed by `rest` starts: named, after an optional
`(priority := …)`, or else anonymous and recorded by its signature. -/
def instanceHead (rest : String) : Array DeclHead :=
  let rest := if rest.startsWith "(priority" then trimStart ((dropBalanced? rest).getD rest)
    else rest
  let name := firstToken rest
  if isIdentifier name then #[{ keyword := "instance", name }]
  else #[{ keyword := "instance", name := signature rest, anonymous := true }]

/-- The declarations the line `line` starts: none, one, or two for `alias ⟨a, b⟩`. -/
def declHeads (line : String) : Array DeclHead :=
  if line.isEmpty || line.front.isWhitespace then #[] else
  match splitKeyword? (normalise line) with
  | none => #[]
  | some ("alias", rest) =>
    if rest.startsWith "⟨" then aliasHeads rest else namedHead "alias" rest
  | some ("instance", rest) => instanceHead rest
  | some (keyword, rest) => namedHead keyword rest

/-! ### C.3. The declaration lines of a diff

`git diff --unified=0` lists, for each file, a header naming the file on both sides and then
hunks, each headed by the line numbers it starts at on both sides, followed by its removed
(`-`) and added (`+`) lines:

```
diff --git a/Physlib/A.lean b/Physlib/A.lean
--- a/Physlib/A.lean
+++ b/Physlib/A.lean
@@ -10,0 +11,2 @@
+lemma foo : True := trivial
+
```
-/

/-- A line of one revision of one file. -/
structure Location where
  file : String
  /-- Counted from one. -/
  line : Nat
  /-- Whether the line is in the head revision (`+`) rather than the base revision (`-`). -/
  added : Bool
  deriving Repr, DecidableEq, Inhabited

/-- A line of the diff which starts a declaration. -/
structure DeclLine where
  loc : Location
  decl : DeclHead
  /-- The line without its `+` or `-`; two equal texts mean the declaration moved. -/
  text : String
  deriving Repr, DecidableEq, Inhabited

/-- The path a `--- ` or `+++ ` header gives, without its `a/` or `b/`. -/
def diffPath (s : String) : String :=
  let s := trim s
  if s.startsWith "a/" || s.startsWith "b/" then dropChars s 2 else s

/-- The base and head line numbers a hunk header `@@ -<base>[,n] +<head>[,m] @@` starts at. -/
def parseHunkHeader (line : String) : Option (Nat × Nat) :=
  if !line.startsWith "@@ " then none else
  match (line.splitOn " ").drop 1 with
  | base :: head :: _ =>
    match ((dropChars base 1).splitOn ",").head?.bind String.toNat?,
        ((dropChars head 1).splitOn ",").head?.bind String.toNat? with
    | some base, some head => some (base, head)
    | _, _ => none
  | _ => none

/-- The declaration lines of the output of `git diff --unified=0`. -/
def parseDiff (lines : Array String) : Array DeclLine := Id.run do
  let mut removedFile := ""
  let mut addedFile := ""
  let mut removedLine := 0
  let mut addedLine := 0
  let mut inHunk := false
  let mut result : Array DeclLine := #[]
  for line in lines do
    if line.startsWith "diff --git " then
      inHunk := false
    else if let some (base, head) := parseHunkHeader line then
      inHunk := true
      removedLine := base
      addedLine := head
    -- File headers only occur outside hunks: inside one, a removed Lean comment `-- a/Foo`
    -- also reads `--- a/Foo`.
    else if !inHunk && line.startsWith "--- " then
      removedFile := diffPath (dropChars line 4)
    else if !inHunk && line.startsWith "+++ " then
      addedFile := diffPath (dropChars line 4)
    else if line.startsWith "+" || line.startsWith "-" then
      let added := line.startsWith "+"
      let text := trimEnd (dropChars line 1)
      let loc : Location :=
        { file := if added then addedFile else removedFile
          line := if added then addedLine else removedLine
          added }
      for decl in declHeads text do
        result := result.push { loc, decl, text }
      if added then addedLine := addedLine + 1 else removedLine := removedLine + 1
    else if line.startsWith " " then
      -- A context line, present only if the diff was made with context.
      removedLine := removedLine + 1
      addedLine := addedLine + 1
  return result

/-! ### C.4. Classifying the declarations -/

/-- How a declaration changed. -/
inductive DeclChange where
  | added (loc : Location)
  /-- Its line changed; it is now at `loc`. -/
  | restated (loc : Location)
  /-- Its line is unchanged but is now elsewhere, possibly in another file. -/
  | moved (old new : Location)
  | removed (loc : Location)
  deriving Repr, DecidableEq, Inhabited

/-- The order in which the changes are reported, as in leaff: additions, removals, then
modifications. -/
def DeclChange.rank : DeclChange → Nat
  | .added .. => 0
  | .removed .. => 1
  | .restated .. => 2
  | .moved .. => 3

/-- Whether the head revision has a statement the base did not: an added or a restated one. -/
def DeclChange.isNew : DeclChange → Bool
  | .added .. | .restated .. => true
  | .moved .. | .removed .. => false

/-- Where to read the declaration now, or, if it is gone, where it was. -/
def DeclChange.target : DeclChange → Location
  | .added loc | .restated loc | .removed loc => loc
  | .moved _ new => new

/-- A declaration and how it changed. -/
structure DeclDiff where
  decl : DeclHead
  change : DeclChange
  deriving Repr, DecidableEq, Inhabited

/-- Declarations are reported by change, then keyword, then name. -/
def DeclDiff.lt (c d : DeclDiff) : Bool :=
  c.change.rank < d.change.rank || c.change.rank == d.change.rank &&
    (c.decl.keyword < d.decl.keyword || c.decl.keyword == d.decl.keyword &&
      c.decl.name < d.decl.name)

/-- The declaration as a code span linked to the line to read it on. -/
def DeclDiff.link (src : Source) (d : DeclDiff) : String :=
  let target := d.change.target
  src.link (code d.decl.display) target.file target.added target.line

/-- The declaration lines grouped by name and classified: a name only on added lines was
added, only on removed lines was removed, on both with the same texts was moved, and on both
with different texts was restated. Namespaces are not considered. -/
def declDiff (lines : Array DeclLine) : Array DeclDiff := Id.run do
  -- Names in order of first appearance, so the output does not depend on a hash map.
  let mut names : Array String := #[]
  for l in lines do
    unless names.contains l.decl.name do names := names.push l.decl.name
  let mut result : Array DeclDiff := #[]
  for name in names do
    let group := lines.filter (·.decl.name == name)
    let added := group.filter (·.loc.added)
    let removed := group.filter (!·.loc.added)
    if removed.isEmpty then
      result := result ++ added.map fun l => { decl := l.decl, change := .added l.loc }
    else if added.isEmpty then
      result := result ++ removed.map fun l => { decl := l.decl, change := .removed l.loc }
    else if (added.map (·.text)).qsort (· < ·) == (removed.map (·.text)).qsort (· < ·) then
      result := result ++ (removed.zip added).map fun (r, a) =>
        { decl := a.decl, change := .moved r.loc a.loc }
    else
      result := result.push { decl := added[0]!.decl, change := .restated added[0]!.loc }
  return result

/-! ## D. Rendering the summary -/

/-! ### D.1. The diff block

The changes are listed as in [leaff](https://github.com/alexjbest/leaff): one line per change,
starting with `+` for an addition, `-` for a removal and `!` for a modification, which GitHub
colours inside a `diff` block; grouped under `@@ <module> @@` headers; and with the most
important changes first. A `.lean` file is named by its module, `Physlib/Foo/Bar.lean` as
`Physlib.Foo.Bar`, and any other file by its path.
-/

/-- The module of a `.lean` file, or the path of any other file. -/
def moduleOf (path : String) : String :=
  match path.dropSuffix? ".lean" with
  | some stem => stem.copy.replace "/" "."
  | none => path

/-- `module` for a `.lean` file, `file` otherwise. -/
def kindOf (path : String) : String := if path.endsWith ".lean" then "module" else "file"

/-- `(+12 -3)`, or `(binary)`. -/
def lineCounts (c : FileChange) : String :=
  match c.insertions, c.deletions with
  | some insertions, some deletions => s!"(+{insertions} -{deletions})"
  | _, _ => "(binary)"

/-- The line of the block for a file change. -/
def FileChange.line (c : FileChange) : String :=
  let kind := kindOf c.path
  let name := moduleOf c.path
  match c.status with
  | .added => s!"+ {kind} added {name} {lineCounts c}"
  | .removed => s!"- {kind} removed {name} {lineCounts c}"
  | .modified => s!"! {kind} modified {name} {lineCounts c}"
  | .renamed oldPath => s!"! {kind} renamed {moduleOf oldPath} → {name} {lineCounts c}"
  | .copied oldPath => s!"+ {kind} copied {moduleOf oldPath} → {name} {lineCounts c}"

/-- The line of the block for a declaration change. -/
def DeclDiff.line (d : DeclDiff) : String :=
  match d.change with
  | .added _ => s!"+ added {d.decl.display}"
  | .removed _ => s!"- removed {d.decl.display}"
  | .restated _ => s!"! statement changed for {d.decl.display}"
  | .moved old new =>
    if old.file == new.file then s!"! moved {d.decl.display} within {kindOf new.file}"
    else s!"! moved {d.decl.display} from {moduleOf old.file} to {moduleOf new.file}"

/-- The block: each file in order of status then path, under a header, followed by the
changes to its declarations in order of importance; at most `limit` lines; then the number of
changes. A moved declaration is listed under the file it is now in. -/
def diffBlock (files : Array FileChange) (decls : Array DeclDiff) (limit : Nat := 300) :
    String := Id.run do
  if files.isEmpty && decls.isEmpty then return "No differences found."
  let mut lines : Array String := #[]
  let mut listed : Array DeclDiff := #[]
  for c in files.qsort FileChange.lt do
    lines := lines.push s!"@@ {moduleOf c.path} @@"
    lines := lines.push c.line
    for d in (decls.filter (c.paths.contains ·.change.target.file)).qsort DeclDiff.lt do
      lines := lines.push d.line
      listed := listed.push d
  -- Every declaration line of the diff is in a changed file, so this is empty; it is here so
  -- that the count below is right even if `git` says otherwise.
  for d in (decls.filter (!listed.contains ·)).qsort DeclDiff.lt do
    lines := lines.push s!"@@ {moduleOf d.change.target.file} @@"
    lines := lines.push d.line
  let count := plural (files.size + decls.size) "difference"
  return "\n".intercalate (#["Found differences:"] ++ truncate lines limit ++ #[count]).toList

/-! ### D.2. The call-out about `theorem`

Physlib reserves `theorem` for results which are significant in the physics literature and
writes every other result with `lemma`. Each `theorem` must have a doc-string and be listed in
the theorems file; `lake exe theorem_lint` checks both. A pull-request which writes one is asking
the reviewer to agree the result deserves it, which is worth saying before the block.
-/

/-- The file listing every result written with `theorem`. -/
def theoremsFile : String := "scripts/lint/exemptions/Theorems.txt"

/-- The declarations written with `theorem` which are new or restated. -/
def newTheorems (decls : Array DeclDiff) : Array DeclDiff :=
  decls.filter fun d => d.decl.keyword == "theorem" && d.change.isNew

/-- The call-out, or the empty string if the pull-request writes no `theorem`. It also says
whether the pull-request changes the theorems file. -/
def theoremCallout (src : Source) (files : Array FileChange) (decls : Array DeclDiff) : String :=
  let theorems := (newTheorems decls).qsort DeclDiff.lt
  if theorems.isEmpty then "" else
  let names := ", ".intercalate (theorems.map (·.link src)).toList
  let listed := if files.any (·.path == theoremsFile) then "which this PR also changes"
    else "**which this PR does not change**"
  -- Markdown joins the lines of a block quote into one paragraph.
  "\n".intercalate [
    "> [!IMPORTANT]",
    s!"> This PR writes {plural theorems.size "result"} with `theorem`:",
    s!"> {names}.",
    ">",
    "> `theorem` is reserved for the results which are significant in the physics literature,",
    "> usually known by name; every other result is a `lemma`. Each one needs a doc-string and",
    s!"> a line under the section of its library in `{theoremsFile}`,",
    s!"> {listed}.",
    "> `lake exe theorem_lint` checks both."]

/-! ### D.3. The summary -/

/-- The closing sentence, so a reader knows how far to trust the block. -/
def caveat : String :=
  "The declarations are found by reading the diff as text, without regard for namespaces, so a \
  declaration whose keyword and name are on different lines is missed, and two declarations of \
  the same name in different namespaces are listed as one. A change to a proof, or to the body \
  of a definition, does not appear. See `scripts/alpha/github/pr_summary.lean`."

/-- The call-out, if any, then the block in a `diff` fence, then the caveat. -/
def render (src : Source) (files : Array FileChange) (decls : Array DeclDiff) : String :=
  let parts := #[theoremCallout src files decls, s!"```diff\n{diffBlock files decls}\n```", caveat]
  "\n\n".intercalate (parts.filter (!·.isEmpty)).toList

/-- The whole summary, from the lines of the three `git diff` outputs. This is the entire
behaviour of the script except for running `git`; F.9 tests it on a small diff. -/
def summarise (src : Source) (nameStatus numstat diff : Array String) : String :=
  render src
    (withLineCounts (parseNameStatus nameStatus) (parseNumstat numstat))
    (declDiff (parseDiff diff))

/-! ## E. Running `git`

This is the only section with side effects. `git` runs the command it is given and reads its
output; `gitSummary` runs the five commands listed in the overview; `main` prints.
-/

/-- The standard output of `git args`, run in the current directory. Throws if `git` fails. -/
def git (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd := "git", args }
  if out.exitCode ≠ 0 then
    throw <| IO.userError s!"`git {" ".intercalate args.toList}` exited with code \
      {out.exitCode}:\n{out.stderr.trimAscii}"
  return out.stdout

/-- The output of `git args` as lines, without the final empty one. -/
def gitLines (args : Array String) : IO (Array String) := do
  let out := trimEnd (← git args)
  return if out.isEmpty then #[] else (out.splitOn "\n").toArray

/-- The commit `revision` names. A link must use a commit: a link to `HEAD` would follow the
branch rather than point at what was summarised. -/
def commitOf (revision : String) : IO String :=
  return trimEnd (← git #["rev-parse", revision])

/-- The commit which `git diff base...head` compares `head` with: the merge base of the two, or
`base` itself if they have none. -/
def mergeBase (base head : String) : IO String := do
  try return trimEnd (← git #["merge-base", base, head])
  catch _ => commitOf base

/-- The summary of the changes `head` makes to `base`. `-M` makes `git` report a renamed file as
renamed rather than as removed and added, so its declarations are not all reported as moved. -/
def gitSummary (base head : String) : IO String := do
  let range := s!"{base}...{head}"
  let src : Source := { base := ← mergeBase base head, head := ← commitOf head }
  return summarise src
    (← gitLines #["diff", "--name-status", "-M", range])
    (← gitLines #["diff", "--numstat", "--no-renames", range])
    (← gitLines #["diff", "--unified=0", "-M", range])

/-- The revisions from the arguments: `origin/master` and `HEAD` unless given. -/
def revisions : List String → Except String (String × String)
  | [] => .ok ("origin/master", "HEAD")
  | [base] => .ok (base, "HEAD")
  | [base, head] => .ok (base, head)
  | args => .error s!"Expected at most two revisions, got {args.length}."

/-! ## F. Tests

These run when the file is compiled, so `lake build pr_summary` fails if one fails. The links in
the expected outputs are shortened by `shortLinks`, and `testSource` stands in for two commits.
-/

/-- Two stand-in commits. -/
def testSource : Source := { base := "bsha", head := "hsha" }

/-- `s` with `https://github.com/<repository>/blob/` shortened to `…/`. -/
def shortLinks (s : String) : String :=
  "…/".intercalate (s.splitOn s!"https://github.com/{repository}/blob/")

/-! ### F.1. Strings, Markdown and links -/

/-- info: [`A.lean`](https://github.com/leanprover-community/physlib/blob/hsha/A.lean#L12) -/
#guard_msgs in
#eval IO.println (testSource.link (code "A.lean") "A.lean" true 12)

-- A removed line is linked in the base revision, and a file at no line in particular.
/-- info: [`A.lean`](https://github.com/leanprover-community/physlib/blob/bsha/A.lean) -/
#guard_msgs in
#eval IO.println (testSource.link (code "A.lean") "A.lean" false)

/-- info: [`A.lean`](…/hsha/A.lean#L12) -/
#guard_msgs in
#eval IO.println (shortLinks (testSource.link (code "A.lean") "A.lean" true 12))

/-- info: "1 file, 2 files" -/
#guard_msgs in
#eval s!"{plural 1 "file"}, {plural 2 "file"}"

/-- info: "2 added, 1 removed" -/
#guard_msgs in
#eval tally #[(2, "added"), (0, "moved"), (1, "removed")]

/-- info: #["a", "… and 2 further lines, left out to keep this short."] -/
#guard_msgs in
#eval truncate #["a", "b", "c"] 1

/-! ### F.2. Reading `git diff --name-status` and `--numstat` -/

/--
info: #[{ path := "Physlib/A.lean", status := PRSummary.FileStatus.added,
          insertions := none, deletions := none },
        { path := "Physlib/B.lean", status := PRSummary.FileStatus.modified,
          insertions := none, deletions := none },
        { path := "Physlib/C.lean", status := PRSummary.FileStatus.removed,
          insertions := none, deletions := none },
        { path := "Physlib/E.lean", status := PRSummary.FileStatus.renamed "Physlib/D.lean",
          insertions := none, deletions := none }]
-/
#guard_msgs (whitespace := lax) in
#eval IO.println (repr (parseNameStatus #["A\tPhyslib/A.lean", "M\tPhyslib/B.lean",
  "D\tPhyslib/C.lean", "R098\tPhyslib/D.lean\tPhyslib/E.lean"]))

/-- info: #[] -/
#guard_msgs in
#eval IO.println (repr (parseNameStatus #["", "not a status line"]))

/-- info: #[("Physlib/A.lean", some 40, some 0), ("Physlib/B.lean", none, none)] -/
#guard_msgs in
#eval IO.println (repr (parseNumstat #["40\t0\tPhyslib/A.lean", "-\t-\tPhyslib/B.lean"]))

/--
info: #[{ path := "Physlib/A.lean", status := PRSummary.FileStatus.added,
          insertions := some 40, deletions := some 0 }]
-/
#guard_msgs (whitespace := lax) in
#eval IO.println (repr (withLineCounts (parseNameStatus #["A\tPhyslib/A.lean"])
  (parseNumstat #["40\t0\tPhyslib/A.lean"])))

/-! ### F.3. Stripping attributes and modifiers from a line -/

/-- info: "lemma foo : True := trivial" -/
#guard_msgs in
#eval normalise "@[simp] lemma foo : True := trivial"

/-- info: "lemma foo : True := trivial" -/
#guard_msgs in
#eval normalise "@[simp, nolint docBlame] private lemma foo : True := trivial  "

/-- info: "def foo : Nat := 0" -/
#guard_msgs in
#eval normalise "@[simp] noncomputable def foo : Nat := 0"

/-- info: "instance : Foo X := bar" -/
#guard_msgs in
#eval normalise "local instance : Foo X := bar"

/-- info: "lemma foo : True := trivial" -/
#guard_msgs in
#eval normalise "set_option maxHeartbeats 400000 in lemma foo : True := trivial"

/-- info: "lemma foo : True := trivial" -/
#guard_msgs in
#eval normalise "open Finset in lemma foo : True := trivial"

-- An attribute which is not closed on the line is left alone.
/-- info: "@[simp, nolint" -/
#guard_msgs in
#eval normalise "@[simp, nolint"

/-! ### F.4. The declarations a line starts -/

/-- The declarations `line` starts. -/
def printHeads (line : String) : IO Unit := IO.println (repr (declHeads line))

/-- info: #[{ keyword := "lemma", name := "foo", anonymous := false }] -/
#guard_msgs in
#eval printHeads "lemma foo : True := trivial"

/-- info: #[{ keyword := "theorem", name := "Foo.bar", anonymous := false }] -/
#guard_msgs in
#eval printHeads "@[simp] protected theorem Foo.bar (x : X) : P x := by simp"

/-- info: #[{ keyword := "def", name := "ψ_eq", anonymous := false }] -/
#guard_msgs in
#eval printHeads "noncomputable def ψ_eq : Nat := 0"

/-- info: #[{ keyword := "structure", name := "Foo", anonymous := false }] -/
#guard_msgs in
#eval printHeads "structure Foo extends Bar where"

/-- info: #[{ keyword := "class inductive", name := "Foo", anonymous := false }] -/
#guard_msgs in
#eval printHeads "class inductive Foo (n : Nat) : Type where"

/-- info: #[{ keyword := "instance", name := "instFoo", anonymous := false }] -/
#guard_msgs in
#eval printHeads "instance instFoo : Foo X := ⟨bar⟩"

-- A priority does not hide the name of an `instance`, and its `:=` does not end the signature.
/-- info: #[{ keyword := "instance", name := "instInhabited", anonymous := false }] -/
#guard_msgs in
#eval printHeads "instance (priority := 100) instInhabited : Inhabited U where"

/-- info: #[{ keyword := "instance", name := ": Foo X", anonymous := true }] -/
#guard_msgs in
#eval printHeads "instance : Foo X := ⟨bar⟩"

/-- info: #[{ keyword := "instance", name := "{A : Type*} [Semigroup A] : IsAlternative A",
  anonymous := true }] -/
#guard_msgs (whitespace := lax) in
#eval printHeads "instance (priority := 100) {A : Type*} [Semigroup A] : IsAlternative A where"

/-- info: #[{ keyword := "alias", name := "foo_of_bar", anonymous := false },
  { keyword := "alias", name := "bar_of_foo", anonymous := false }] -/
#guard_msgs (whitespace := lax) in
#eval printHeads "alias ⟨foo_of_bar, bar_of_foo⟩ := foo_iff_bar"

/-- info: #[{ keyword := "alias", name := "foo_of_bar", anonymous := false }] -/
#guard_msgs in
#eval printHeads "alias ⟨foo_of_bar, _⟩ := foo_iff_bar"

/-- info: #[{ keyword := "alias", name := "foo'", anonymous := false }] -/
#guard_msgs in
#eval printHeads "alias foo' := foo"

/-- info: #[{ keyword := "informal_lemma", name := "foo", anonymous := false }] -/
#guard_msgs in
#eval printHeads "informal_lemma foo where"

-- Indented lines, lines which start no declaration, and keywords which are only the start of
-- an identifier are all passed over.
/-- info: #[] -/
#guard_msgs in
#eval printHeads "  lemma foo : True := trivial"

/-- info: #[] -/
#guard_msgs in
#eval printHeads "  exact foo"

/-- info: #[] -/
#guard_msgs in
#eval printHeads "definitely_not_a_declaration"

/-- info: #[] -/
#guard_msgs in
#eval printHeads ""

/-! ### F.5. The declaration lines of a diff -/

/-- info: some (10, 11) -/
#guard_msgs in
#eval parseHunkHeader "@@ -10,0 +11,2 @@"

-- A count left out means one line.
/-- info: some (3, 3) -/
#guard_msgs in
#eval parseHunkHeader "@@ -3 +3 @@ namespace Foo"

/-- info: none -/
#guard_msgs in
#eval parseHunkHeader "+lemma foo : True := trivial"

/-- A diff which adds a lemma to one file and renames a definition in another. Its last hunk
removes the Lean comment `-- a/Physlib/Z.lean`, which reads as a `---` header but is not one. -/
def exampleDiff : Array String :=
  #["diff --git a/Physlib/A.lean b/Physlib/A.lean",
    "--- a/Physlib/A.lean",
    "+++ b/Physlib/A.lean",
    "@@ -10,0 +11,2 @@",
    "+lemma foo_eq_bar : foo = bar := rfl",
    "+  -- an indented line is not a declaration",
    "diff --git a/Physlib/B.lean b/Physlib/B.lean",
    "--- a/Physlib/B.lean",
    "+++ b/Physlib/B.lean",
    "@@ -3 +3 @@",
    "-def oldName : Nat := 0",
    "+def newName : Nat := 0",
    "@@ -20,2 +20,0 @@",
    "--- a/Physlib/Z.lean",
    "-def afterAComment : Nat := 0"]

/--
info: #[{ loc := { file := "Physlib/A.lean", line := 11, added := true },
          decl := { keyword := "lemma", name := "foo_eq_bar", anonymous := false },
          text := "lemma foo_eq_bar : foo = bar := rfl" },
        { loc := { file := "Physlib/B.lean", line := 3, added := false },
          decl := { keyword := "def", name := "oldName", anonymous := false },
          text := "def oldName : Nat := 0" },
        { loc := { file := "Physlib/B.lean", line := 3, added := true },
          decl := { keyword := "def", name := "newName", anonymous := false },
          text := "def newName : Nat := 0" },
        { loc := { file := "Physlib/B.lean", line := 21, added := false },
          decl := { keyword := "def", name := "afterAComment", anonymous := false },
          text := "def afterAComment : Nat := 0" }]
-/
#guard_msgs (whitespace := lax) in
#eval IO.println (repr (parseDiff exampleDiff))

/-! ### F.6. Classifying the declarations -/

/-- The declaration line `text` at line `n` of `file`, added if `added`. -/
def mkLine (file : String) (n : Nat) (added : Bool) (text : String) : DeclLine :=
  { loc := { file, line := n, added }, decl := (declHeads text)[0]!, text }

/-- The classification of `lines`, as the block would show it. -/
def printDeclDiff (lines : Array DeclLine) : IO Unit := do
  for d in (declDiff lines).qsort DeclDiff.lt do IO.println d.line

/--
info: + added lemma foo
- removed def bar
-/
#guard_msgs in
#eval printDeclDiff #[
  mkLine "Physlib/A.lean" 3 true "lemma foo : True := trivial",
  mkLine "Physlib/B.lean" 7 false "def bar : Nat := 0"]

-- The same line removed from one file and added to another: moved.
/-- info: ! moved lemma foo from Physlib.B to Physlib.A -/
#guard_msgs in
#eval printDeclDiff #[
  mkLine "Physlib/B.lean" 7 false "lemma foo : True := trivial",
  mkLine "Physlib/A.lean" 3 true "lemma foo : True := trivial"]

-- The same name on two different lines: restated.
/-- info: ! statement changed for lemma foo -/
#guard_msgs in
#eval printDeclDiff #[
  mkLine "Physlib/A.lean" 3 false "lemma foo : True := trivial",
  mkLine "Physlib/A.lean" 3 true "lemma foo (n : Nat) : n = n := rfl"]

-- An attribute is part of the line, so gaining one is a restatement.
/-- info: ! statement changed for lemma foo -/
#guard_msgs in
#eval printDeclDiff #[
  mkLine "Physlib/A.lean" 3 false "lemma foo : True := trivial",
  mkLine "Physlib/A.lean" 3 true "@[simp] lemma foo : True := trivial"]

-- A `lemma` which became a `theorem` keeps its name: restated, not removed and added.
/-- info: ! statement changed for theorem foo -/
#guard_msgs in
#eval printDeclDiff #[
  mkLine "Physlib/A.lean" 3 false "lemma foo : True := trivial",
  mkLine "Physlib/A.lean" 3 true "theorem foo : True := trivial"]

-- A move within one file.
/-- info: ! moved lemma foo within module -/
#guard_msgs in
#eval printDeclDiff #[
  mkLine "Physlib/A.lean" 3 false "lemma foo : True := trivial",
  mkLine "Physlib/A.lean" 9 true "lemma foo : True := trivial"]

/-! ### F.7. The diff block -/

/-- info: "Physlib.Foo.Bar" -/
#guard_msgs in
#eval moduleOf "Physlib/Foo/Bar.lean"

/-- info: "scripts/README.md" -/
#guard_msgs in
#eval moduleOf "scripts/README.md"

-- Files are listed by status then path, each followed by its declarations with additions
-- first; a declaration which moved is listed under the module it is now in.
/--
info: Found differences:
@@ Physlib.A @@
+ module added Physlib.A (+40 -0)
+ added lemma foo
! moved def baz from Physlib.B to Physlib.A
@@ Physlib.C @@
- module removed Physlib.C (+0 -9)
@@ Physlib.B @@
! module modified Physlib.B (+2 -1)
- removed def bar
! statement changed for lemma qux
@@ docs/figure.png @@
! file modified docs/figure.png (binary)
8 differences
-/
#guard_msgs in
#eval IO.println (diffBlock #[
  { path := "Physlib/C.lean", status := .removed, insertions := some 0, deletions := some 9 },
  { path := "Physlib/B.lean", status := .modified, insertions := some 2, deletions := some 1 },
  { path := "docs/figure.png", status := .modified },
  { path := "Physlib/A.lean", status := .added, insertions := some 40, deletions := some 0 }]
  (declDiff #[
    mkLine "Physlib/A.lean" 3 true "lemma foo : True := trivial",
    mkLine "Physlib/B.lean" 7 false "def bar : Nat := 0",
    mkLine "Physlib/B.lean" 2 false "def baz : Nat := 0",
    mkLine "Physlib/A.lean" 9 true "def baz : Nat := 0",
    mkLine "Physlib/B.lean" 12 false "lemma qux : True := trivial",
    mkLine "Physlib/B.lean" 12 true "lemma qux : 1 = 1 := rfl"]))

-- A renamed file is headed by its new module, and a change inside it, which the diff gives
-- under either path, is listed with it.
/--
info: Found differences:
@@ Physlib.New @@
! module renamed Physlib.Old → Physlib.New (+1 -1)
- removed lemma gone
2 differences
-/
#guard_msgs in
#eval IO.println (diffBlock
  #[{ path := "Physlib/New.lean", status := .renamed "Physlib/Old.lean",
      insertions := some 1, deletions := some 1 }]
  (declDiff #[mkLine "Physlib/Old.lean" 3 false "lemma gone : True := trivial"]))

/-- info: No differences found. -/
#guard_msgs in
#eval IO.println (diffBlock #[] #[])

-- At most `limit` lines are listed; the rest are counted.
/--
info: Found differences:
@@ Physlib.A @@
… and 2 further lines, left out to keep this short.
2 differences
-/
#guard_msgs in
#eval IO.println (diffBlock (limit := 1)
  #[{ path := "Physlib/A.lean", status := .modified, insertions := some 1, deletions := some 0 }]
  (declDiff #[mkLine "Physlib/A.lean" 3 true "lemma foo : True := trivial"]))

/-! ### F.8. The call-out about `theorem` -/

/-- A pull-request which adds a `theorem` and a `lemma`, and moves a `theorem`. -/
def exampleTheorems : Array DeclDiff :=
  declDiff #[
    mkLine "A.lean" 3 true "theorem foo : True := trivial",
    mkLine "A.lean" 9 true "lemma bar : True := trivial",
    mkLine "B.lean" 2 false "theorem baz : True := trivial",
    mkLine "A.lean" 20 true "theorem baz : True := trivial"]

-- Only the new `theorem` is called out: `bar` is a `lemma`, and `baz` only moved.
/-- info: theorem foo -/
#guard_msgs in
#eval IO.println ("\n".intercalate ((newTheorems exampleTheorems).toList.map (·.decl.display)))

/--
info: > [!IMPORTANT]
> This PR writes 1 result with `theorem`:
> [`theorem foo`](…/hsha/A.lean#L3).
>
> `theorem` is reserved for the results which are significant in the physics literature,
> usually known by name; every other result is a `lemma`. Each one needs a doc-string and
> a line under the section of its library in `scripts/lint/exemptions/Theorems.txt`,
> **which this PR does not change**.
> `lake exe theorem_lint` checks both.
-/
#guard_msgs in
#eval IO.println (shortLinks (theoremCallout testSource #[] exampleTheorems))

-- A pull-request which also changes the theorems file is told so rather than warned.
/-- info: true -/
#guard_msgs in
#eval ((theoremCallout testSource #[{ path := theoremsFile, status := .modified }]
  exampleTheorems).splitOn "which this PR also changes").length == 2

/-- info: "" -/
#guard_msgs in
#eval theoremCallout testSource #[] (declDiff #[mkLine "A.lean" 3 true "lemma bar : True := rfl"])

/-! ### F.9. The whole summary

The output of `git` for a pull-request which adds a `theorem` to one file and a `lemma` to a
new file, fed through `summarise`. This is the whole comment, apart from the links being
shortened.
-/

/--
info: > [!IMPORTANT]
> This PR writes 1 result with `theorem`:
> [`theorem Foo.gauss_law`](…/hsha/Physlib/Foo.lean#L12).
>
> `theorem` is reserved for the results which are significant in the physics literature,
> usually known by name; every other result is a `lemma`. Each one needs a doc-string and
> a line under the section of its library in `scripts/lint/exemptions/Theorems.txt`,
> **which this PR does not change**.
> `lake exe theorem_lint` checks both.

```diff
Found differences:
@@ Physlib.Bar @@
+ module added Physlib.Bar (+20 -0)
+ added lemma Bar.baz
@@ Physlib.Foo @@
! module modified Physlib.Foo (+3 -0)
+ added theorem Foo.gauss_law
4 differences
```

The declarations are found by reading the diff as text, without regard for namespaces, so a
declaration whose keyword and name are on different lines is missed, and two declarations of
the same name in different namespaces are listed as one. A change to a proof, or to the body
of a definition, does not appear. See `scripts/alpha/github/pr_summary.lean`.
-/
#guard_msgs (whitespace := lax) in
#eval IO.println (shortLinks (summarise testSource
  #["M\tPhyslib/Foo.lean",
    "A\tPhyslib/Bar.lean"]
  #["3\t0\tPhyslib/Foo.lean",
    "20\t0\tPhyslib/Bar.lean"]
  #["diff --git a/Physlib/Foo.lean b/Physlib/Foo.lean",
    "--- a/Physlib/Foo.lean",
    "+++ b/Physlib/Foo.lean",
    "@@ -11,0 +12,3 @@ namespace Foo",
    "+theorem Foo.gauss_law : flux = charge := by",
    "+  simp",
    "+",
    "diff --git a/Physlib/Bar.lean b/Physlib/Bar.lean",
    "new file mode 100644",
    "--- /dev/null",
    "+++ b/Physlib/Bar.lean",
    "@@ -0,0 +1,20 @@",
    "+import Physlib.Foo",
    "+",
    "+namespace Bar",
    "+",
    "+/-- A lemma. -/",
    "+lemma Bar.baz : True := trivial",
    "+",
    "+end Bar"]))

/-- info: Except.ok ("origin/master", "HEAD") -/
#guard_msgs in
#eval revisions []

/-- info: Except.ok ("abc", "def") -/
#guard_msgs in
#eval revisions ["abc", "def"]

/-- info: Except.error "Expected at most two revisions, got 3." -/
#guard_msgs in
#eval revisions ["a", "b", "c"]

end PRSummary

open PRSummary in
/-- Reads the revisions from the arguments, prints the summary to standard output and anything
else to standard error. Exits with `1` on a bad argument or a `git` error. -/
def main (args : List String) : IO UInt32 := do
  let (base, head) ← match revisions args with
    | .ok revs => pure revs
    | .error e =>
      IO.eprintln s!"{e}\nUsage: lake exe pr_summary [<base> [<head>]]"
      return 1
  IO.eprintln s!"Summarising `git diff {base}...{head}`."
  try
    IO.println (← gitSummary base head)
  catch e =>
    IO.eprintln s!"Could not summarise the pull-request: {e}"
    return 1
  return 0
