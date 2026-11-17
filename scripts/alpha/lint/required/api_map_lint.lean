/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
/-!

# API map linter

Checks the structure, citations and Lean references of every `API-map.md` in the repository.

## i. Overview

An API map is a prose document, described in `docs/API_MAP_GUIDE.md`:

- a `# ` title;
- a single-paragraph `## Abstract` (or `## Abstract (Alpha)`) with no citations;
- a `## Content` and/or a `## Content (Alpha)` section discussing the physics, with Lean
  citations `[n]`, `[TODO]` markers and text citations `{n}` in the prose;
- a numbered `## Lean References` list of the Lean declarations the prose cites;
- optionally, and directly after it, a numbered `## References` list of the literature and other
  API maps the prose cites (the text references).

This executable checks that each map has that shape, that citations and references correspond,
that links appear only in `## References`, and that every cited declaration really is in the file
it is attributed to.

Everything in this file is built around a single structure, `APIMapData`, whose fields are the
parts of an API map: its headers, its abstract, its content, and its Lean and text references.
`APIMapData.read` reads a map from its file, reporting anything the structure cannot hold (text
before the first section, unreadable reference entries); every other check is a definition on
`APIMapData`.

Run it from the repository root with `lake exe api_map_lint`; pass `--verbose` to also see the
notes (instance claims and Lean names in the prose), and `--repo <path>` to lint another checkout.
It exits non-zero on any error. It does not need a Lean environment built to perform its checks.

## ii. Key results

- `APIMapData` is an API map, with its parts as fields.
- `APIMapData.read` reads a map from the repository.
- `APIMapData.leanCitations` and `APIMapData.textCitations` give the citations in its prose.
- `APIMapData.checkHeadings`, `APIMapData.checkProse`, `APIMapData.checkCitations` and
  `APIMapData.checkDeclarations` check a map.
- `APIMapData.lint` lints a map, returning its errors, its notes and its counts.
- `main` lints every map in the repository and exits non-zero on any error.

## iii. Table of contents

- A. The API map
- B. String helpers
- C. Reading a map
  - C.1. Reference entries
  - C.2. Sections and paragraphs
  - C.3. Finding and reading files
- D. Citations
- E. Declarations
- F. Linting
  - F.1. Counts and reports
  - F.2. Checking the headings and the prose
  - F.3. Checking the references and citations
  - F.4. Linting a map
- G. Main function

## iv. References

- `docs/API_MAP_GUIDE.md`, the guide to writing API maps, which this linter enforces.

-/

/-!

## A. The API map

-/

namespace APIMapData

/-- One entry of `## Lean References`: its number, its Lean file and the declarations it claims. -/
structure LeanReference where
  number : Nat
  file : String
  claims : List String

/-- One entry of `## References`: its number and its text, which cites the literature or another
API map. -/
structure TextReference where
  number : Nat
  text : String

end APIMapData

/-- An API map: an `API-map.md` file, as described in `docs/API_MAP_GUIDE.md`, read into its
parts. Each prose section is given by its paragraphs, each folded onto one line, and is empty
when the map lacks it. -/
structure APIMapData where
  /-- The repository-relative path of the file. -/
  path : String
  /-- The `# ` headings; a well-formed map has exactly one, its title. -/
  titles : Array String
  /-- The `##` headings, in order. -/
  headers : List String
  /-- The paragraphs of `## Abstract`. -/
  abstract : Array String
  /-- The paragraphs of `## Abstract (Alpha)`. -/
  abstractAlpha : Array String
  /-- The paragraphs of `## Content`. -/
  content : Array String
  /-- The paragraphs of `## Content (Alpha)`. -/
  contentAlpha : Array String
  /-- The entries of `## Lean References`. -/
  referencesLean : Array APIMapData.LeanReference
  /-- The entries of `## References`. -/
  referencesText : Array APIMapData.TextReference

namespace APIMapData

/-!

## B. String helpers

-/

/-- `s` with leading and trailing whitespace removed. -/
private def trim (s : String) : String := s.trimAscii.toString

/-- Whether `needle` occurs in `haystack`. -/
private def containsStr (haystack needle : String) : Bool :=
  needle != "" && (haystack.splitOn needle).length > 1

/-- Whether `c` is a word character in the sense of a regular expression's `\w`: an ASCII letter
or digit, the underscore, or any non-ASCII character that is not whitespace. -/
private def isWordChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || (c.toNat > 127 && !c.isWhitespace)

/-- The whitespace-separated words of `s`. -/
private def words (s : String) : List String :=
  let (done, current) := s.toList.foldl (fun (done, current) c =>
    if c.isWhitespace then
      (if current.isEmpty then done else done ++ [String.ofList current], [])
    else (done, current ++ [c])) ([], [])
  if current.isEmpty then done else done ++ [String.ofList current]

/-- `s` in single quotes, for error messages. -/
private def quote (s : String) : String := "'" ++ s ++ "'"

/-!

## C. Reading a map

### C.1. Reference entries

-/

/-- The number and the rest of a line opening a numbered entry `n. rest`. -/
private def numbered (line : String) : Option (Nat × String) :=
  let cs := line.toList
  let digits := cs.takeWhile Char.isDigit
  match cs.drop digits.length with
  | '.' :: c :: rest =>
    if !digits.isEmpty && c.isWhitespace then
      some ((String.ofList digits).toNat!, trim (String.ofList rest))
    else none
  | _ => none

/-- Reads an entry `n. File.lean — `a`, `b``. -/
def LeanReference.ofLine? (line : String) : Option LeanReference := do
  let (number, rest) ← numbered line
  let word := String.ofList (rest.toList.takeWhile (!·.isWhitespace))
  let after := String.ofList (rest.toList.drop word.length)
  -- A dash may be attached to the file name.
  let (file, after) ←
    if word.endsWith ".lean" then some (word, after)
    else if word.endsWith ".lean—" || word.endsWith ".lean-" then
      some (String.ofList word.toList.dropLast, String.ofList [word.toList.getLast!] ++ after)
    else none
  guard (file.length > ".lean".length)
  match (trim after).toList with
  | [] => some { number, file, claims := [] }
  | dash :: claims =>
    if dash == '—' || dash == '-' then
      some { number, file, claims := backticked (String.ofList claims) }
    else none
where
  /-- The backtick-delimited spans of `s`. -/
  backticked (s : String) : List String :=
    let rec odd : List String → List String
      | _ :: p :: q :: rest => p :: odd (q :: rest)
      | _ => []
    (odd (s.splitOn "`")).filter (· != "")

/-- Reads an entry `n. text`. -/
def TextReference.ofLine? (line : String) : Option TextReference := do
  let (number, text) ← numbered line
  guard (text != "")
  return { number, text }

/-- The paths of API maps named in a text reference. -/
def TextReference.mapPaths (reference : TextReference) : List String :=
  (words reference.text).filterMap fun word =>
    match word.splitOn "/API-map.md" with
    | before :: _ :: _ => if before != "" then some (before ++ "/API-map.md") else none
    | _ => none

/-!

### C.2. Sections and paragraphs

-/

/-- Reads an API map from its text. Returns the map, together with the problems found that the
map cannot hold: text between the title and the first section, and reference entries that cannot
be read. -/
def parse (path text : String) : APIMapData × Array String := Id.run do
  /- Split the lines into the `# ` titles, the lines before the first `##` section, and the
  `##` sections, ignoring headings inside fenced code blocks. -/
  let mut titles : Array String := #[]
  let mut preamble : Array String := #[]
  let mut sections : Array (String × Array String) := #[]
  let mut fenced := false
  for line in text.splitOn "\n" do
    if isFence line then fenced := !fenced
    if !fenced then
      if let some heading := headingText "##" line then
        sections := sections.push (heading, #[])
        continue
      if let some title := headingText "#" line then
        titles := titles.push title
        continue
    if sections.isEmpty then preamble := preamble.push line
    else sections := sections.modify (sections.size - 1) fun (h, ls) => (h, ls.push line)
  /- The lines of the last section with a given heading. -/
  let linesOf (heading : String) : Array String :=
    ((sections.toList.filter (·.1 == heading)).getLast?.map (·.2)).getD #[]
  let (referencesLean, unreadableLean) := (entries (linesOf "Lean References")).foldl
    (fun (refs, bad) line => match LeanReference.ofLine? line with
      | some ref => (refs.push ref, bad)
      | none => (refs, bad.push line)) (#[], #[])
  let (referencesText, unreadableText) := (entries (linesOf "References")).foldl
    (fun (refs, bad) line => match TextReference.ofLine? line with
      | some ref => (refs.push ref, bad)
      | none => (refs, bad.push line)) (#[], #[])
  let map : APIMapData :=
    { path, titles, headers := sections.toList.map (·.1)
      abstract := paragraphs (linesOf "Abstract")
      abstractAlpha := paragraphs (linesOf "Abstract (Alpha)")
      content := paragraphs (linesOf "Content")
      contentAlpha := paragraphs (linesOf "Content (Alpha)")
      referencesLean, referencesText }
  let mut problems : Array String := #[]
  if preamble.any (trim · != "") then
    problems := problems.push
      "STRUCTURE: text between the title and the first section; it belongs in `## Abstract`"
  problems := problems ++ unreadableLean.map (s!"REFERENCES: unreadable entry: {quote ·}") ++
    unreadableText.map (s!"LITERATURE: unreadable entry: {quote ·}")
  return (map, problems)
where
  /-- If `line` is `marker`, at least one whitespace character, and then non-blank text, that
  text with surrounding whitespace removed. -/
  headingText (marker line : String) : Option String :=
    if line.startsWith marker then
      let rest := String.ofList (line.toList.drop marker.length)
      match rest.toList with
      | c :: _ => if c.isWhitespace && trim rest != "" then some (trim rest) else none
      | [] => none
    else none
  /-- Whether `line` opens or closes a code fence. -/
  isFence (line : String) : Bool :=
    let start := String.ofList (line.toList.dropWhile Char.isWhitespace)
    start.startsWith "```" || start.startsWith "~~~"
  /-- Whether `line` is a subheading: three or more `#` followed by whitespace. -/
  isSubheading (line : String) : Bool :=
    let hashes := (line.toList.takeWhile (· == '#')).length
    hashes ≥ 3 && match line.toList.drop hashes with
      | c :: _ => c.isWhitespace
      | [] => false
  /-- The blank-line-separated paragraphs of some lines, each folded onto one line.
  Subheadings close a paragraph and are not paragraphs themselves. -/
  paragraphs (lines : Array String) : Array String := Id.run do
    let mut out : Array String := #[]
    let mut current : Array String := #[]
    for line in lines do
      if trim line == "" || isSubheading line then
        unless current.isEmpty do
          out := out.push (" ".intercalate current.toList)
          current := #[]
      else current := current.push (trim line)
    unless current.isEmpty do out := out.push (" ".intercalate current.toList)
    return out
  /-- The entries of a reference list, with wrapped continuation lines folded back on. -/
  entries (lines : Array String) : Array String := Id.run do
    let mut folded : Array String := #[]
    for line in lines do
      let line := trim line
      if line == "" || line == "*None yet.*" then continue
      if !folded.isEmpty && (numbered line).isNone then
        folded := folded.modify (folded.size - 1) (· ++ " " ++ line)
      else folded := folded.push line
    return folded

/-!

### C.3. Finding and reading files

-/

/-- Reads the API map at the repository-relative `path`, together with the problems found that
the map cannot hold. -/
def read (repo : System.FilePath) (path : String) : IO (APIMapData × Array String) := do
  return parse path (← IO.FS.readFile (repo / path))

/-- The repository-relative paths of the files called `name` under `relative`, skipping hidden
directories such as `.lake` and `.git`. -/
partial def findPaths (repo : System.FilePath) (name : String) (relative : String := "") :
    IO (Array String) := do
  let mut found : Array String := #[]
  let directory := if relative == "" then repo else repo / relative
  for entry in ← directory.readDir do
    let child := if relative == "" then entry.fileName else relative ++ "/" ++ entry.fileName
    if ← entry.path.isDir then
      unless entry.fileName.startsWith "." do
        found := found ++ (← findPaths repo name child)
    else if entry.fileName == name then
      found := found.push child
  return found

/-- Whether `path` is an existing file. -/
def isFile (path : System.FilePath) : IO Bool := do
  return (← path.pathExists) && !(← path.isDir)

/-!

## D. Citations

-/

/-- The prose sections of a map, with their headings, in order: the abstract, the alpha abstract,
the content and the alpha content. -/
def proseSections (map : APIMapData) : List (String × Array String) :=
  [("Abstract", map.abstract), ("Abstract (Alpha)", map.abstractAlpha),
    ("Content", map.content), ("Content (Alpha)", map.contentAlpha)]

/-- Whether a map is alpha, that is, has not yet been through the stringent review. -/
def isAlpha (map : APIMapData) : Bool :=
  map.headers.contains "Abstract (Alpha)" && !map.headers.contains "Abstract"

/-- A piece of prose: a character of text, or a citation. -/
inductive Piece
  | text (c : Char)
  | lean (n : Nat)
  | todo
  | textCitation (n : Nat)

/-- A paragraph split into text and the citations `[n]`, `[TODO]` and `{n}`. -/
partial def pieces (paragraph : String) : List Piece :=
  go paragraph.toList
where
  /-- Splits a list of characters into pieces. -/
  go : List Char → List Piece
    | [] => []
    | c :: rest =>
      let isDigits (cs : List Char) := !cs.isEmpty && cs.all Char.isDigit
      let close := if c == '[' then some ']' else if c == '{' then some '}' else none
      match close with
      | none => .text c :: go rest
      | some close =>
        let inner := rest.takeWhile (· != close)
        let after := rest.drop (inner.length + 1)
        if inner.length == rest.length then .text c :: go rest
        else if c == '[' && isDigits inner then .lean (String.ofList inner).toNat! :: go after
        else if c == '[' && inner == "TODO".toList then .todo :: go after
        else if c == '{' && isDigits inner then
          .textCitation (String.ofList inner).toNat! :: go after
        else .text c :: go rest

/-- A run of adjacent Lean citations, which closes one claim of the prose: the reference numbers
cited, and whether the run contains `[TODO]`. -/
structure LeanCitation where
  numbers : List Nat
  todo : Bool

/-- The Lean citations of a paragraph, one per run of adjacent citations. Text citations may sit
inside a run; a run made only of text citations is not a claim. -/
def leanCitationsOf (paragraph : String) : Array LeanCitation := Id.run do
  let mut runs : Array LeanCitation := #[]
  /- The run being read: its numbers, whether it has `[TODO]`, and whether it has a Lean
  citation at all. -/
  let mut current : Option (List Nat × Bool × Bool) := none
  for piece in pieces paragraph do
    let (numbers, todo, lean) := current.getD ([], false, false)
    match piece with
    | .text c =>
      unless c.isWhitespace do
        if current.isSome && lean then runs := runs.push { numbers, todo }
        current := none
    | .lean n => current := some (numbers ++ [n], todo, true)
    | .todo => current := some (numbers, true, true)
    | .textCitation _ => current := some (numbers, todo, lean)
  if let some (numbers, todo, true) := current then runs := runs.push { numbers, todo }
  return runs

/-- The text citations `{n}` of a paragraph. -/
def textCitationsOf (paragraph : String) : List Nat :=
  (pieces paragraph).filterMap fun
    | .textCitation n => some n
    | _ => none

/-- The Lean citations in the prose of a map, one per claim. -/
def leanCitations (map : APIMapData) : Array LeanCitation :=
  map.proseSections.toArray.flatMap fun (_, paras) => paras.flatMap leanCitationsOf

/-- The text citations in the prose of a map. -/
def textCitations (map : APIMapData) : List Nat :=
  map.proseSections.flatMap fun (_, paras) => paras.toList.flatMap textCitationsOf

/-- The numbers of the Lean references, in order. -/
def leanNumbers (map : APIMapData) : List Nat := map.referencesLean.toList.map (·.number)

/-- The numbers of the text references, in order. -/
def textNumbers (map : APIMapData) : List Nat := map.referencesText.toList.map (·.number)

/-!

## E. Declarations

-/

/-- What a claim in a Lean reference names: a declaration, a notation, or an instance. -/
inductive ClaimKind
  | name
  | notation
  | inst
deriving BEq

/-- What a claim names, and the token to look for in the source. -/
def LeanReference.classifyClaim (claim : String) : ClaimKind × String :=
  let claim := trim claim
  if claim.startsWith "notation " then (.notation, trim (String.ofList (claim.toList.drop 9)))
  else match claim.splitOn " : " with
    | name :: _ :: _ => (.name, trim name)
    | _ =>
      if isIdentifier claim then (.name, claim)
      else if !claim.toList.contains ' ' then (.notation, claim)
      else (.inst, claim)
where
  /-- Whether `c` may start an identifier, beyond the ASCII letters. -/
  inIdentifierRange (c : Char) : Bool :=
    let n := c.toNat
    (0xC0 ≤ n && n ≤ 0x24F) || (0x370 ≤ n && n ≤ 0x3FF) || (0x2100 ≤ n && n ≤ 0x214F)
  /-- Whether `s` is a (possibly dotted) identifier. -/
  isIdentifier (s : String) : Bool :=
    match s.toList with
    | c :: rest => (c.isAlpha || c == '_' || inIdentifierRange c) &&
        rest.all (fun d => isWordChar d || d == '\'' || d == '.')
    | [] => false

/-- Whether the token of a claim is present in the source. A notation is present when each of its
fragments is; a name is present verbatim, or as its last component on word boundaries. -/
def LeanReference.claimIsPresent (source : String) (kind : ClaimKind) (token : String) : Bool :=
  if kind == .notation then
    let fragments := (words (token.map fun c => if c == '·' || c == '⬝' then ' ' else c))
    fragments.all (containsStr source ·)
  else containsStr source token || containsWord source ((token.splitOn ".").getLast!)
where
  /-- Whether `word` occurs in `source` with a word boundary on either side, as the regular
  expression `\bword\b` would find it. -/
  containsWord (source word : String) : Bool := Id.run do
    match word.toList.head?, word.toList.getLast? with
    | some first, some last =>
      let parts := source.splitOn word
      let isWord (c : Option Char) : Bool := (c.map isWordChar).getD false
      for i in [0:parts.length - 1] do
        /- The occurrence sits between `parts[i]` and `parts[i+1]`; an empty part means it
        touches the neighbouring occurrence, or the start or end of the source. -/
        let before := match parts[i]!.toList.getLast? with
          | some c => some c
          | none => if i == 0 then none else some last
        let after := match parts[i + 1]!.toList.head? with
          | some c => some c
          | none => if i + 2 == parts.length then none else some first
        if isWord before != isWordChar first && isWordChar last != isWord after then
          return true
      return false
    | _, _ => return false

/-!

## F. Linting

### F.1. Counts and reports

-/

/-- The counts reported for a map. -/
structure Counts where
  claims : Nat := 0
  done : Nat := 0
  todo : Nat := 0
  checked : Nat := 0
  namesOk : Nat := 0
  missingFile : Nat := 0
  missingName : Nat := 0
  needLean : Nat := 0
  leanInProse : Nat := 0

/-- The sum of two counts. -/
def Counts.add (a b : Counts) : Counts where
  claims := a.claims + b.claims
  done := a.done + b.done
  todo := a.todo + b.todo
  checked := a.checked + b.checked
  namesOk := a.namesOk + b.namesOk
  missingFile := a.missingFile + b.missingFile
  missingName := a.missingName + b.missingName
  needLean := a.needLean + b.needLean
  leanInProse := a.leanInProse + b.leanInProse

/-- The outcome of a check: the errors, which fail the run, the notes, which are shown only with
`--verbose`, and the counts. -/
structure Report where
  errors : Array String := #[]
  notes : Array String := #[]
  counts : Counts := {}

/-- Two reports, one after the other. -/
def Report.append (a b : Report) : Report where
  errors := a.errors ++ b.errors
  notes := a.notes ++ b.notes
  counts := a.counts.add b.counts

/-- A report with only errors. -/
def Report.ofErrors (errors : Array String) : Report := { errors }

/-!

### F.2. Checking the headings and the prose

-/

/-- The rank of each header in the required order, or `none` for an unknown header. -/
def headerRank : String → Option Nat
  | "Abstract" | "Abstract (Alpha)" => some 0
  | "Content" => some 1
  | "Content (Alpha)" => some 2
  | "Lean References" => some 3
  | "References" => some 4
  | _ => none

/-- Problems with the title and the headers of a map: exactly one title, only known headers, each
once, an abstract, some content and the Lean references, in the required order. -/
def checkHeadings (map : APIMapData) : Array String := Id.run do
  let mut problems : Array String := #[]
  if map.titles.isEmpty then problems := problems.push "STRUCTURE: no `# Title` heading"
  else if map.titles.size > 1 then
    problems := problems.push "STRUCTURE: more than one `# ` heading"
  let names := map.headers
  for name in names do
    if (headerRank name).isNone then
      problems := problems.push s!"STRUCTURE: unknown section `## {name}`"
  for name in names.eraseDups do
    if names.count name > 1 then
      problems := problems.push s!"STRUCTURE: section `## {name}` appears more than once"
  let abstracts := names.filter (["Abstract", "Abstract (Alpha)"].contains ·)
  if abstracts.isEmpty then
    problems := problems.push "STRUCTURE: missing section `## Abstract` (or `## Abstract (Alpha)`)"
  else if abstracts.length > 1 then
    problems := problems.push
      "STRUCTURE: only one of `## Abstract` and `## Abstract (Alpha)` is allowed"
  unless names.any (["Content", "Content (Alpha)"].contains ·) do
    problems := problems.push "STRUCTURE: missing section `## Content` (or `## Content (Alpha)`)"
  unless names.contains "Lean References" do
    problems := problems.push "STRUCTURE: missing section `## Lean References`"
  let ranks := names.filterMap headerRank
  unless ranks.mergeSort (· ≤ ·) == ranks do
    problems := problems.push ("STRUCTURE: sections must come in the order `## Abstract`, " ++
      "`## Content`, `## Content (Alpha)`, `## Lean References`, `## References`")
  return problems

/-- Problems with the prose of a map: an abstract must be a single paragraph without citations, a
content section must not be empty, and neither may contain links, `[planned]` or grouped
citations. -/
partial def checkProse (map : APIMapData) : Array String := Id.run do
  let mut problems : Array String := #[]
  for (heading, paras) in map.proseSections do
    unless map.headers.contains heading do continue
    if heading.startsWith "Abstract" then
      if paras.size != 1 then
        problems := problems.push
          s!"STRUCTURE: `## {heading}` must be a single paragraph (found {paras.size})"
      for p in paras do
        if (pieces p).any (fun | .text _ => false | _ => true) then
          problems := problems.push s!"STRUCTURE: `## {heading}` must not contain citations"
    else if paras.isEmpty then
      problems := problems.push s!"STRUCTURE: `## {heading}` is empty"
    for p in paras do
      let (links, remaining) := markdownLinks p.toList
      for link in links do
        problems := problems.push (s!"LINK: `## {heading}` contains the markdown link " ++
          s!"{quote link}; cite it as `\{n}` from `## References`")
      if ["http://", "https://", "www."].any (containsStr (String.ofList remaining) ·) then
        problems := problems.push
          s!"LINK: `## {heading}` contains a raw link; cite it as `\{n}` from `## References`"
      if containsStr p "[planned]" then
        problems := problems.push
          s!"CITATION: `[planned]` in `## {heading}`; the marker is now `[TODO]`"
      for grouped in groupedCitations p.toList do
        problems := problems.push (s!"CITATION: {quote grouped} in `## {heading}`; give each " ++
          "citation its own bracket, e.g. `[1][2]` or `{1}{2}`")
  return problems
where
  /-- The markdown links `[text](target)` of some characters, and the characters with them
  removed. -/
  markdownLinks : List Char → List String × List Char
    | [] => ([], [])
    | '[' :: rest =>
      let label := rest.takeWhile (· != ']')
      match rest.drop label.length with
      | ']' :: '(' :: tail =>
        let target := tail.takeWhile (· != ')')
        if target.length < tail.length then
          let (links, remaining) := markdownLinks (tail.drop (target.length + 1))
          (String.ofList ('[' :: label ++ [']', '('] ++ target ++ [')']) :: links, remaining)
        else
          let (links, remaining) := markdownLinks rest
          (links, '[' :: remaining)
      | _ =>
        let (links, remaining) := markdownLinks rest
        (links, '[' :: remaining)
    | c :: rest =>
      let (links, remaining) := markdownLinks rest
      (links, c :: remaining)
  /-- The grouped citations `[1, 2]` and `{1, 2}` of some characters, which should be `[1][2]`
  and `{1}{2}`. -/
  groupedCitations : List Char → List String
    | [] => []
    | c :: rest =>
      let isGroup (inner : List Char) : Bool := match inner with
        | d :: _ => d.isDigit && inner.contains ',' &&
            inner.all (fun e => e.isDigit || e == ',' || e.isWhitespace)
        | [] => false
      let close := if c == '[' then some ']' else if c == '{' then some '}' else none
      match close with
      | some close =>
        let inner := rest.takeWhile (· != close)
        if inner.length < rest.length && isGroup inner then
          String.ofList (c :: inner ++ [close]) :: groupedCitations (rest.drop (inner.length + 1))
        else groupedCitations rest
      | none => groupedCitations rest

/-!

### F.3. Checking the references and citations

-/

/-- Problems with the numbering of a reference list, which must run 1, 2, …, n. -/
def checkNumbering (label : String) (numbers : List Nat) : Array String := Id.run do
  let mut problems : Array String := #[]
  for number in numbers.eraseDups do
    if numbers.count number > 1 then
      problems := problems.push s!"{label}: duplicate entry [{number}]"
  for (number, position) in numbers.zip (List.range' 1 numbers.length) do
    if number != position then
      problems := problems.push s!"{label}: entry [{number}] is in position {position}"
      break
  return problems

/-- Problems with the text references of a map: the API maps they name must exist. -/
def checkMapPaths (map : APIMapData) (repo : System.FilePath) : IO (Array String) := do
  let mut errors : Array String := #[]
  for reference in map.referencesText do
    for mapPath in reference.mapPaths do
      unless ← isFile (repo / mapPath) do
        errors := errors.push s!"literature\{{reference.number}} MISSING API MAP: {mapPath}"
  return errors

/-- Checks the citations in the prose of a map: every citation resolves, and every reference is
cited. Also counts the claims, and notes Lean names left in the content. -/
def checkCitations (map : APIMapData) : Report := Id.run do
  let leanNumbers := map.leanNumbers
  let textNumbers := map.textNumbers
  let mut errors : Array String := #[]
  let mut notes : Array String := #[]
  let mut leanInProse := 0
  for (heading, paras) in map.proseSections do
    for (p, index) in paras.toList.zip (List.range paras.size) do
      let place := s!"{heading}, paragraph {index + 1}"
      for citation in leanCitationsOf p do
        for number in citation.numbers do
          unless leanNumbers.contains number do
            errors := errors.push s!"[{place}] DANGLING CITATION: [{number}]"
      for number in textCitationsOf p do
        unless textNumbers.contains number do
          errors := errors.push s!"[{place}] DANGLING LITERATURE CITATION: \{{number}}"
      if heading.startsWith "Content" && ((p.splitOn "`").drop 1).dropLast.any (· != "") then
        leanInProse := leanInProse + 1
        notes := notes.push s!"[{place}] STYLE: Lean names belong in the references, not the prose"
  let citations := map.leanCitations
  let cited := citations.toList.flatMap (·.numbers)
  for number in leanNumbers do
    unless cited.contains number do
      errors := errors.push s!"REFERENCES: entry [{number}] is never cited"
  let citedText := map.textCitations
  for number in textNumbers.eraseDups.mergeSort (· ≤ ·) do
    unless citedText.contains number do
      errors := errors.push s!"LITERATURE: entry \{{number}} is never cited"
  let todo := (citations.filter (·.todo)).size
  let counts : Counts :=
    { claims := citations.size, todo, done := citations.size - todo, leanInProse }
  return { errors, notes, counts }

/-- Checks the Lean references of a map: each file exists and contains the declarations claimed
of it. -/
def checkDeclarations (map : APIMapData) (repo : System.FilePath) : IO Report := do
  let mut report : Report := {}
  for reference in map.referencesLean do
    let path := repo / reference.file
    unless ← isFile path do
      report := report.append
        { errors := #[s!"ref[{reference.number}] MISSING FILE: {reference.file}"]
          counts := { missingFile := 1 } }
      continue
    report := report.append { counts := { checked := 1 } }
    let source ← IO.FS.readFile path
    if reference.claims.isEmpty then
      report := report.append (.ofErrors
        #[s!"ref[{reference.number}] NO DECLARATIONS listed for {reference.file}"])
    for claim in reference.claims do
      let (kind, token) := LeanReference.classifyClaim claim
      if kind == .inst then
        let note :=
          s!"ref[{reference.number}] NEEDS LEAN ENVIRONMENT: {quote claim} in {reference.file}"
        report := report.append { notes := #[note], counts := { needLean := 1 } }
      else if LeanReference.claimIsPresent source kind token then
        report := report.append { counts := { namesOk := 1 } }
      else
        let label := if kind == .name then "NAME" else "NOTATION"
        let error := s!"ref[{reference.number}] MISSING {label}: {quote token} in {reference.file}"
        report := report.append { errors := #[error], counts := { missingName := 1 } }
  return report

/-!

### F.4. Linting a map

-/

/-- Lints a map: its headings and prose, its reference lists, its citations and its
declarations. -/
def lint (map : APIMapData) (repo : System.FilePath) : IO Report := do
  let structural := map.checkHeadings ++ map.checkProse ++
    checkNumbering "REFERENCES" map.leanNumbers ++ checkNumbering "LITERATURE" map.textNumbers ++
    (← map.checkMapPaths repo)
  return (Report.ofErrors structural).append map.checkCitations |>.append
    (← map.checkDeclarations repo)

end APIMapData

/-!

## G. Main function

-/

/-- Lints every API map in the repository. -/
def main (args : List String) : IO UInt32 := do
  let verbose := args.contains "--verbose"
  let repo : System.FilePath := match args.dropWhile (· != "--repo") with
    | _ :: path :: _ => System.FilePath.mk path
    | _ => System.FilePath.mk "."
  let paths := (← APIMapData.findPaths repo "API-map.md").qsort (· < ·)
  let stale := (← APIMapData.findPaths repo "API-map.yaml").qsort (· < ·)
  if paths.isEmpty then
    IO.eprintln s!"no API-map.md files under {repo}"
    return 1
  let mut total : APIMapData.Counts := {}
  let mut failed := false
  for path in paths do
    let (map, readProblems) ← APIMapData.read repo path
    let report := (APIMapData.Report.ofErrors readProblems).append (← map.lint repo)
    let counts := report.counts
    total := total.add counts
    failed := failed || !report.errors.isEmpty
    IO.println (s!"[{if report.errors.isEmpty then "ok" else "FAIL"}] {map.path} " ++
      s!"({counts.done} done, {counts.todo} TODO, {counts.namesOk} names ok, " ++
      s!"{counts.needLean} need-Lean)")
    for problem in report.errors ++ (if verbose then report.notes else #[]) do
      IO.println s!"  {problem}"
  for path in stale do
    failed := true
    IO.println s!"[FAIL] {path}: API maps are now `API-map.md`"
  IO.println "\n=== SUMMARY ==="
  IO.println (s!"files={paths.size} claims={total.claims} done={total.done} " ++
    s!"todo={total.todo} files_checked={total.checked} names_ok={total.namesOk} " ++
    s!"MISSING_FILE={total.missingFile} MISSING_NAME={total.missingName} " ++
    s!"need_Lean_env={total.needLean} lean_names_in_prose={total.leanInProse}")
  return if failed then 1 else 0
