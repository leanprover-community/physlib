/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Lean
/-!

# PR summary

A script which prints, as Markdown, what a pull-request changes: its files, their namespaces and
their declarations.

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
git diff --numstat -M -z        <base>...<head>     lines added to and removed from each file
git diff --unified=0 -M         <base>...<head>     the changed lines themselves
git show <commit>:<path>                            each changed `.lean` file, for its namespaces
```

**What it prints.** For a pull-request which adds one lemma to one file:

````markdown
```diff
Found differences:
@@ Physlib.Foo @@
! module modified Physlib.Foo (+3 -0)
  namespaces Foo
+ added lemma Foo.bar
2 differences
```

<a sentence on what the block misses; see `caveat`>
````

The block follows the format of [leaff](https://github.com/alexjbest/leaff): one line per
change, `+` for an addition, `-` for a removal and `!` for a modification, grouped under
`@@ <module> @@` headers, with the most important changes first. Under each `.lean` file are
the namespaces it opens, uncoloured, and any it gains (`+ namespace added`) or loses
(`- namespace removed`). A pull-request which writes a
result with `theorem` gets a call-out above the block, since Physlib reserves `theorem` for
named results of the physics literature and `theorem_lint` requires each to be listed in
`scripts/lint/exemptions/Theorems.txt`. Section G shows the whole output for four small
pull-requests.

**How it works.** `summarise` is a pure function from the text of the three `git diff` outputs
and of the changed `.lean` files to the Markdown, and `gitSummary` is the only thing which runs
`git`. In between:

1. `parseNameStatus` and `parseNumstat` read which files changed and by how many lines (B).
   Both diffs use `-M`, so a renamed file is counted against its old self.
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

4. `namespacesOf` reads the namespaces each file opens, in both revisions (D).
5. `diffBlock` lists the changes in the format of leaff, and `theoremCallout` adds the
   call-out (E).

**What it misses.** The scan is textual, so it is a guide and not a proof. It does not see

- a declaration whose keyword and name are on different lines;
- a declaration which does not start at the beginning of its line;
- namespaces, for declarations: the `foo` of `namespace A` and the `foo` of `namespace B` are one
  name to it, even though the namespaces of each file are listed;
- a `namespace`, `section` or `end` which does not start its line, or which sits inside a
  comment;
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
- `PRSummary.namespacesOf` reads the namespaces a `.lean` file opens.
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
- D. The namespaces a pull-request touches
- E. Rendering the summary
  - E.1. The diff block
  - E.2. The call-out about `theorem`
  - E.3. The summary
- F. Running `git`
- G. Tests
  - G.1. A theorem, and a lemma in a new file
  - G.2. A renamed file, a removed file, and declarations moving between them
  - G.3. A theorem, with the theorems file changed
  - G.4. Nothing changed

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
  /-- The namespaces a `.lean` file opens, in the order it opens them: in the head revision,
  or, for a removed file, in the base revision. -/
  namespaces : Array String := #[]
  /-- The namespaces the head revision of the file opens and its base revision does not. -/
  addedNamespaces : Array String := #[]
  /-- The namespaces the base revision of the file opens and its head revision does not. -/
  removedNamespaces : Array String := #[]
  deriving Repr, DecidableEq, Inhabited

/-- Files are reported by status, then by path. -/
def FileChange.lt (c d : FileChange) : Bool :=
  c.status.rank < d.status.rank || c.status.rank == d.status.rank && c.path < d.path

/-- The path of the file in the base revision: its old path if it was renamed or copied. -/
def FileChange.oldPath (c : FileChange) : String :=
  match c.status with
  | .renamed oldPath | .copied oldPath => oldPath
  | _ => c.path

/-- The paths the diff may give for lines of the file: its path, and, if it was renamed or
copied, its old path. -/
def FileChange.paths (c : FileChange) : List String :=
  if c.oldPath == c.path then [c.path] else [c.path, c.oldPath]

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

The output is read with `-z`, which ends every field with a NUL rather than a line with a
newline. A file is one field: the lines added, the lines removed and the path, separated by
tabs, with both counts `-` for a binary file. A renamed file is three fields: the two counts
followed by an empty path, then the old path, then the new one. Shown one field to a line:

```
40	0	Physlib/New.lean
-	-	docs/figure.png
2	1
Physlib/Old.lean
Physlib/Renamed.lean
```

The diff is made with `-M`, as `git diff --name-status` is, so a renamed file is counted against
its old self: a file which is only renamed is `+0 -0`. Without `-M` it would be counted as a
removed file and an added one, and looked up by its new path alone it would read as every line
added and none removed.
-/

/-- The new path and the two counts of each file in the fields of `git diff --numstat -z`. -/
def parseNumstat (fields : Array String) : Array (String × Option Nat × Option Nat) := Id.run do
  let mut result : Array (String × Option Nat × Option Nat) := #[]
  let mut i := 0
  -- Each step moves past at least one field, so the loop ends before the bound.
  for _ in [0:fields.size] do
    if h : i < fields.size then
      match fields[i].splitOn "\t" with
      | [insertions, deletions, path] =>
        if path.isEmpty then
          -- A rename: the old path and then the new path are the next two fields.
          if h' : i + 2 < fields.size then
            result := result.push (fields[i + 2], insertions.toNat?, deletions.toNat?)
          i := i + 3
        else
          result := result.push (path, insertions.toNat?, deletions.toNat?)
          i := i + 1
      | _ => i := i + 1
  return result

/-- `changes` with the counts of `counts` filled in by path. -/
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

/-! ## D. The namespaces a pull-request touches

The diff shows only the lines which changed, so the namespaces of a file are read from the file
itself, in both revisions. A `.lean` file opens a namespace with `namespace A.B`, and closes it,
or a `section`, with `end`. The scopes are tracked as a stack, so that `namespace A` and then
`namespace B` open `A.B`. Commands start at the beginning of their line, and an indented `end`,
which closes a `match` or a `do`, is skipped.
-/

/-- A file as one revision has it. -/
structure FileContents where
  path : String
  /-- Whether this is the head revision (`true`) or the base revision (`false`). -/
  added : Bool
  lines : Array String
  deriving Repr, DecidableEq, Inhabited

/-- The namespaces the lines of a `.lean` file open, in the order they first open them. -/
def namespacesOf (lines : Array String) : Array String := Id.run do
  -- The open scopes, innermost first: the components of a namespace, or `[]` for a section or
  -- a `mutual` block, both of which `end` also closes.
  let mut scopes : List (List String) := []
  let mut result : Array String := #[]
  for line in lines do
    if line.startsWith " " || line.startsWith "\t" then continue
    match ((normalise line).splitOn " ").filter (!·.isEmpty) with
    | "namespace" :: name :: _ =>
      scopes := name.splitOn "." :: scopes
      let full := ".".intercalate scopes.reverse.flatten
      unless result.contains full do result := result.push full
    | "section" :: _ | "mutual" :: _ => scopes := [] :: scopes
    | "end" :: _ => scopes := scopes.tail
    | _ => pure ()
  return result

/-- `changes` with the namespaces of each file filled in from `contents`, and, for a file in
both revisions, the namespaces it gained and lost. -/
def withNamespaces (changes : Array FileChange) (contents : Array FileContents) :
    Array FileChange :=
  changes.map fun c =>
    let head := (contents.find? fun f => f.added && f.path == c.path).map (namespacesOf ·.lines)
    let base := (contents.find? fun f => !f.added && f.path == c.oldPath).map
      (namespacesOf ·.lines)
    match head, base with
    | some h, some b =>
      { c with namespaces := h, addedNamespaces := h.filter (!b.contains ·),
               removedNamespaces := b.filter (!h.contains ·) }
    | some h, none | none, some h => { c with namespaces := h }
    | none, none => c

/-! ## E. Rendering the summary -/

/-! ### E.1. The diff block

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

/-- The block: each file in order of status then path, under a header, followed by its
namespaces, the namespaces it gained and lost, and the changes to its declarations in order of
importance; at most `limit` lines; then the number of
changes. A moved declaration is listed under the file it is now in. -/
def diffBlock (files : Array FileChange) (decls : Array DeclDiff) (limit : Nat := 300) :
    String := Id.run do
  if files.isEmpty && decls.isEmpty then return "No differences found."
  let mut lines : Array String := #[]
  let mut listed : Array DeclDiff := #[]
  for c in files.qsort FileChange.lt do
    lines := lines.push s!"@@ {moduleOf c.path} @@"
    lines := lines.push c.line
    -- A line starting with a space is left uncoloured inside a `diff` block.
    unless c.namespaces.isEmpty do
      lines := lines.push s!"  namespaces {", ".intercalate c.namespaces.toList}"
    lines := lines ++ c.addedNamespaces.map (s!"+ namespace added {·}")
    lines := lines ++ c.removedNamespaces.map (s!"- namespace removed {·}")
    for d in (decls.filter (c.paths.contains ·.change.target.file)).qsort DeclDiff.lt do
      lines := lines.push d.line
      listed := listed.push d
  -- Every declaration line of the diff is in a changed file, so this is empty; it is here so
  -- that the count below is right even if `git` says otherwise.
  for d in (decls.filter (!listed.contains ·)).qsort DeclDiff.lt do
    lines := lines.push s!"@@ {moduleOf d.change.target.file} @@"
    lines := lines.push d.line
  let namespaceChanges := files.foldl
    (fun n c => n + c.addedNamespaces.size + c.removedNamespaces.size) 0
  let count := plural (files.size + namespaceChanges + decls.size) "difference"
  return "\n".intercalate (#["Found differences:"] ++ truncate lines limit ++ #[count]).toList

/-! ### E.2. The call-out about `theorem`

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

/-! ### E.3. The summary -/

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

/-- The whole summary, from the lines of `git diff --name-status` and `git diff --unified=0`,
the fields of `git diff --numstat -z`, and the changed `.lean` files in each revision. This is
the entire behaviour of the script except for running `git`, and is what G tests. -/
def summarise (src : Source) (nameStatus numstat diff : Array String)
    (contents : Array FileContents) : String :=
  render src
    (withNamespaces (withLineCounts (parseNameStatus nameStatus) (parseNumstat numstat))
      contents)
    (declDiff (parseDiff diff))

/-! ## F. Running `git`

This is the only section with side effects. `git` runs the command it is given and reads its
output; `gitSummary` runs the commands listed in the overview; `main` prints.
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

/-- The NUL-terminated fields of the output of `git args`, run with `-z`. -/
def gitFields (args : Array String) : IO (Array String) := do
  return ((← git args).splitOn "\x00").toArray.filter (!·.isEmpty)

/-- The changed `.lean` files of `nameStatus` in each revision they are in: the head revision of
every file but a removed one, and the base revision, at its old path, of every file but an added
one. -/
def gitContents (src : Source) (nameStatus : Array String) : IO (Array FileContents) := do
  let mut result : Array FileContents := #[]
  for c in parseNameStatus nameStatus do
    unless c.path.endsWith ".lean" do continue
    unless c.status == .removed do
      let lines ← gitLines #["show", s!"{src.head}:{c.path}"]
      result := result.push { path := c.path, added := true, lines }
    unless c.status == .added do
      let lines ← gitLines #["show", s!"{src.base}:{c.oldPath}"]
      result := result.push { path := c.oldPath, added := false, lines }
  return result

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
renamed rather than as removed and added, so its declarations are not all reported as moved and
its lines are counted against its old self. -/
def gitSummary (base head : String) : IO String := do
  let range := s!"{base}...{head}"
  let src : Source := { base := ← mergeBase base head, head := ← commitOf head }
  let nameStatus ← gitLines #["diff", "--name-status", "-M", range]
  return summarise src nameStatus
    (← gitFields #["diff", "--numstat", "-M", "-z", range])
    (← gitLines #["diff", "--unified=0", "-M", range])
    (← gitContents src nameStatus)

/-- The revisions from the arguments: `origin/master` and `HEAD` unless given. -/
def revisions : List String → Except String (String × String)
  | [] => .ok ("origin/master", "HEAD")
  | [base] => .ok (base, "HEAD")
  | [base, head] => .ok (base, head)
  | args => .error s!"Expected at most two revisions, got {args.length}."

/-! ## G. Tests

These test `summarise`, the whole behaviour of the script apart from running `git`, on the
output `git` gives for four small pull-requests. They run when the file is compiled, so
`lake build pr_summary` fails if one fails. The links in the expected outputs are shortened by
`shortLinks`, and `testSource` stands in for the two commits.
-/

/-- Two stand-in commits. -/
def testSource : Source := { base := "bsha", head := "hsha" }

/-- `s` with `https://github.com/<repository>/blob/` shortened to `…/`. -/
def shortLinks (s : String) : String :=
  "…/".intercalate (s.splitOn s!"https://github.com/{repository}/blob/")

/-! ### G.1. A theorem, and a lemma in a new file

The whole comment: the call-out about `theorem`, the block, and the caveat.
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
+ module added Physlib.Bar (+8 -0)
  namespaces Bar
+ added lemma Bar.baz
@@ Physlib.Foo @@
! module modified Physlib.Foo (+3 -0)
  namespaces Foo
+ added theorem Foo.gauss_law
4 differences
```

The declarations are found by reading the diff as text, without regard for namespaces, so a
declaration whose keyword and name are on different lines is missed, and two declarations of the
same name in different namespaces are listed as one. A change to a proof, or to the body of a
definition, does not appear. See `scripts/alpha/github/pr_summary.lean`.
-/
#guard_msgs (whitespace := lax) in
#eval IO.println (shortLinks (summarise testSource
  #["M\tPhyslib/Foo.lean",
    "A\tPhyslib/Bar.lean"]
  #["3\t0\tPhyslib/Foo.lean",
    "8\t0\tPhyslib/Bar.lean"]
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
    "@@ -0,0 +1,8 @@",
    "+import Physlib.Foo",
    "+",
    "+namespace Bar",
    "+",
    "+/-- A lemma. -/",
    "+lemma Bar.baz : True := trivial",
    "+",
    "+end Bar"]
  #[{ path := "Physlib/Foo.lean", added := false, lines := #["namespace Foo", "end Foo"] },
    { path := "Physlib/Foo.lean", added := true, lines := #["namespace Foo", "end Foo"] },
    { path := "Physlib/Bar.lean", added := true,
      lines := #["import Physlib.Foo", "namespace Bar", "end Bar"] }]))

/-! ### G.2. A renamed file, a removed file, and declarations moving between them

The renamed file is counted against its old self, so it reads `+3 -1` rather than every line
added. Its namespaces are read from both revisions. The declarations show a restatement, an
addition behind an attribute and a modifier, a removal, and a move from the removed file.
-/

/--
info: ```diff
Found differences:
@@ Physlib.Gone @@
- module removed Physlib.Gone (+0 -2)
  namespaces Gone
- removed def baz
@@ Physlib.New @@
! module renamed Physlib.Old → Physlib.New (+3 -1)
  namespaces Foo, Foo.Bar
+ namespace added Foo.Bar
+ added lemma quux
! statement changed for lemma foo
! moved lemma qux from Physlib.Gone to Physlib.New
@@ docs/figure.png @@
! file modified docs/figure.png (binary)
8 differences
```

The declarations are found by reading the diff as text, without regard for namespaces, so a
declaration whose keyword and name are on different lines is missed, and two declarations of the
same name in different namespaces are listed as one. A change to a proof, or to the body of a
definition, does not appear. See `scripts/alpha/github/pr_summary.lean`.
-/
#guard_msgs (whitespace := lax) in
#eval IO.println (shortLinks (summarise testSource
  #["R090\tPhyslib/Old.lean\tPhyslib/New.lean",
    "D\tPhyslib/Gone.lean",
    "M\tdocs/figure.png"]
  #["3\t1\t", "Physlib/Old.lean", "Physlib/New.lean",
    "0\t2\tPhyslib/Gone.lean",
    "-\t-\tdocs/figure.png"]
  #["diff --git a/Physlib/Old.lean b/Physlib/New.lean",
    "similarity index 90%",
    "rename from Physlib/Old.lean",
    "rename to Physlib/New.lean",
    "--- a/Physlib/Old.lean",
    "+++ b/Physlib/New.lean",
    "@@ -3 +3,3 @@",
    "-lemma foo : 1 = 1 := rfl",
    "+lemma foo : (1 : ℕ) = 1 := rfl",
    "+@[simp] private lemma quux : True := trivial",
    "+lemma qux : True := trivial",
    "diff --git a/Physlib/Gone.lean b/Physlib/Gone.lean",
    "deleted file mode 100644",
    "--- a/Physlib/Gone.lean",
    "+++ /dev/null",
    "@@ -1,2 +0,0 @@",
    "-def baz : Nat := 0",
    "-lemma qux : True := trivial"]
  #[{ path := "Physlib/Old.lean", added := false,
      lines := #["namespace Foo", "lemma foo : 1 = 1 := rfl", "end Foo"] },
    { path := "Physlib/New.lean", added := true,
      lines := #["namespace Foo", "noncomputable section", "namespace Bar",
        "lemma foo : (1 : ℕ) = 1 := rfl", "end Bar", "end", "end Foo"] },
    { path := "Physlib/Gone.lean", added := false,
      lines := #["namespace Gone", "def baz : Nat := 0", "  match x with", "  end", "end Gone"] }]))

/-! ### G.3. A theorem, with the theorems file changed

The call-out says the theorems file is changed rather than warning that it is not.
-/

/--
info: > [!IMPORTANT]
> This PR writes 1 result with `theorem`:
> [`theorem gauss_law`](…/hsha/Physlib/Foo.lean#L5).
>
> `theorem` is reserved for the results which are significant in the physics literature,
> usually known by name; every other result is a `lemma`. Each one needs a doc-string and
> a line under the section of its library in `scripts/lint/exemptions/Theorems.txt`,
> which this PR also changes.
> `lake exe theorem_lint` checks both.

```diff
Found differences:
@@ Physlib.Foo @@
! module modified Physlib.Foo (+1 -0)
+ added theorem gauss_law
@@ scripts/lint/exemptions/Theorems.txt @@
! file modified scripts/lint/exemptions/Theorems.txt (+1 -0)
3 differences
```

The declarations are found by reading the diff as text, without regard for namespaces, so a
declaration whose keyword and name are on different lines is missed, and two declarations of the
same name in different namespaces are listed as one. A change to a proof, or to the body of a
definition, does not appear. See `scripts/alpha/github/pr_summary.lean`.
-/
#guard_msgs (whitespace := lax) in
#eval IO.println (shortLinks (summarise testSource
  #["M\tPhyslib/Foo.lean",
    "M\tscripts/lint/exemptions/Theorems.txt"]
  #["1\t0\tPhyslib/Foo.lean",
    "1\t0\tscripts/lint/exemptions/Theorems.txt"]
  #["diff --git a/Physlib/Foo.lean b/Physlib/Foo.lean",
    "--- a/Physlib/Foo.lean",
    "+++ b/Physlib/Foo.lean",
    "@@ -4,0 +5 @@",
    "+theorem gauss_law : flux = charge := rfl",
    "diff --git a/scripts/lint/exemptions/Theorems.txt b/scripts/lint/exemptions/Theorems.txt",
    "--- a/scripts/lint/exemptions/Theorems.txt",
    "+++ b/scripts/lint/exemptions/Theorems.txt",
    "@@ -2,0 +3 @@",
    "+Foo.gauss_law"]
  #[]))

/-! ### G.4. Nothing changed -/

/--
info: ```diff
No differences found.
```

The declarations are found by reading the diff as text, without regard for namespaces, so a
declaration whose keyword and name are on different lines is missed, and two declarations of the
same name in different namespaces are listed as one. A change to a proof, or to the body of a
definition, does not appear. See `scripts/alpha/github/pr_summary.lean`.
-/
#guard_msgs (whitespace := lax) in
#eval IO.println (shortLinks (summarise testSource #[] #[] #[] #[]))

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
