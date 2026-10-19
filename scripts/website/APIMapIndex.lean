/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
/-!

# API map index

Gathers every `API-map.md` in the library into the website's data file `docs/_data/APIMap.yml`.

## i. Overview

This executable gathers every `API-map.md` in the library into a single
YAML data file, `docs/_data/APIMap.yml`, for the website to render. It follows
the pattern of `scripts/website/TODO_to_yml.lean`, which builds
`docs/_data/TODO.yml` for the website's TODO list: the YAML is printed to
standard output, and passing `mkFile` writes the file.

The output carries, for each map in sorted path order: the map path, its
module context, a GitHub link, and the map's title, abstract, claims, Lean
references and literature references, together with per-map and total
completion counts.

An API map is a prose document, described in `docs/API_MAP_GUIDE.md`: a title,
a single-paragraph `## Abstract` (or `## Abstract (Alpha)`), `## Content` and/or
`## Content (Alpha)`, `## Lean References` (a numbered list of
`file — names` entries) and `## References` (a numbered list of literature and
other API maps). The content prose points at the Lean references with `[n]`
citations, marks what is not yet formalized with `[TODO]`, and points at the
literature with `{n}` citations, which do not affect the claims. Each run of
citations closes a claim: the prose since the previous run. The parser below
reads exactly that shape; lines outside it are ignored rather than raising
errors. Each claim's `location` is reconstructed from the entries it cites, so
the data file keeps the `file (names)` form the website already renders.

## ii. Key results

- `APIMapData` is the content of one API map.
- `claimsOf` splits a content paragraph into its claims.
- `parseAPIMap` reads one `API-map.md`.
- `indexYAML` renders the parsed maps as the YAML data file.

## iii. Table of contents

- A. The data of an API map
- B. Parsing
- C. Creating the YAML file
- D. Main function

## iv. References

- `docs/API_MAP_GUIDE.md`, the guide to writing API maps.

-/

/-!

## A. The data of an API map

-/

/-- One entry of the `## Lean References` list: the number it is cited by,
the Lean file, and the declarations claimed to be in it. -/
structure APIMapReference where
  index : Nat
  file : String
  declarations : List String
deriving Inhabited

/-- One claim of the content: the prose closed by a run of citations.
`citations` are the reference numbers in that run, and `alpha` records whether
the claim sits in `## Content (Alpha)`. -/
structure APIMapRequirement where
  description : String := ""
  done : Bool := false
  citations : List Nat := []
  alpha : Bool := false

/-- The contents of one `API-map.md` file. -/
structure APIMapData where
  path : System.FilePath
  title : String := ""
  overview : String := ""
  alpha : Bool := false
  requirements : List APIMapRequirement := []
  declarations : List APIMapReference := []
  references : List String := []

/-- The number of claims of a map that are done. -/
def APIMapData.doneCount (map : APIMapData) : Nat :=
  (map.requirements.filter (fun requirement => requirement.done)).length

/-- The number of claims of a map. -/
def APIMapData.totalCount (map : APIMapData) : Nat :=
  map.requirements.length

/-- The dotted module context of a map, e.g. `Physlib.SpaceAndTime.Time`. -/
def APIMapData.moduleContext (map : APIMapData) : String :=
  ((map.path.parent.getD map.path).toString.replace "/" ".")

/-- The link to a map on GitHub. -/
def APIMapData.githubLink (map : APIMapData) : String :=
  -- This follows Lean.Name.toGitHubLink in Physlib.Meta.Basic, pointing at
  -- the repository-relative API-map path instead of a declaration.
  s!"https://github.com/leanprover-community/physlib/blob/master/{map.path}"

/-- The `file (names)` form of a requirement's location, built from the
entries it cites, or `N/A` when it cites none. -/
def APIMapData.locationOf (map : APIMapData) (requirement : APIMapRequirement) : String :=
  let groups := requirement.citations.filterMap (fun index =>
    (map.declarations.find? (fun reference => reference.index == index)).map
      (fun reference =>
        if reference.declarations.isEmpty then reference.file
        else reference.file ++ " (" ++ String.intercalate ", " reference.declarations ++ ")"))
  if groups.isEmpty then "N/A" else String.intercalate "; " groups

/-!

## B. Parsing

-/

/-- `value` with leading and trailing whitespace removed. -/
def trim (value : String) : String := value.trimAscii.toString

/-- The text between the first pair of `delimiter`s, and the remainder after
the closing one. -/
private def spanBetween (value : String) (delimiter : String) : Option (String × String) := do
  let afterOpen ← (value.splitOn delimiter)[1]?
  let rest := String.intercalate delimiter ((value.splitOn delimiter).drop 2)
  pure (afterOpen, rest)

/-- Every backtick-delimited span of a line, in order. -/
partial def backtickedSpans (value : String) : List String :=
  match spanBetween value "`" with
  | some (span, rest) => trim span :: backtickedSpans rest
  | none => []

/-- A piece of content prose: plain text, or one citation `[n, m]` or
`[TODO]`. -/
inductive ProseToken
  | text (value : String)
  | cite (numbers : List Nat) (todo : Bool)

/-- Reads the inside of a pair of square brackets as a citation, if it is one. -/
def citationOf (inner : String) : Option ProseToken :=
  if inner == "TODO" then some (.cite [] true)
  else
    let parts := (inner.splitOn ",").map trim
    let numbers := parts.filterMap String.toNat?
    if numbers.length == parts.length then some (.cite numbers false) else none

/-- Splits a paragraph into text and citations. Square brackets that are not
citations, such as the text of a markdown link, stay in the text. -/
def tokenize (paragraph : String) : List ProseToken :=
  match paragraph.splitOn "[" with
  | [] => []
  | first :: rest =>
    .text first :: rest.flatMap (fun part =>
      match part.splitOn "]" with
      | inner :: after@(_ :: _) =>
        match citationOf inner with
        | some cite => [cite, .text (String.intercalate "]" after)]
        | none => [.text ("[" ++ part)]
      | _ => [.text ("[" ++ part)])

/-- Removes the literature citations `{n}` from a paragraph. -/
def removeLiterature (paragraph : String) : String :=
  match paragraph.splitOn "{" with
  | [] => ""
  | first :: rest =>
    first ++ String.join (rest.map (fun part =>
      match part.splitOn "}" with
      | inner :: after@(_ :: _) =>
        if (trim inner).toNat?.isSome then String.intercalate "}" after else "{" ++ part
      | _ => "{" ++ part))

/-- Removes the literature citations `{n}` from a paragraph, together with the
space a citation leaves before a following full stop or comma. -/
def stripLiterature (paragraph : String) : String :=
  ((removeLiterature paragraph).replace " ." ".").replace " ," ","

/-- The claims of a content paragraph. Each run of adjacent citations closes a
claim, whose description is the prose since the previous run; a run is done
unless it contains `[TODO]`. Prose after the last run cites nothing and is
not a claim. -/
def claimsOf (alpha : Bool) (paragraph : String) : List APIMapRequirement := Id.run do
  let close (prose : String) (numbers : List Nat) (todo : Bool) : APIMapRequirement :=
    { description := trim prose, done := !todo, citations := numbers, alpha := alpha }
  let mut claims : List APIMapRequirement := []
  let mut prose := ""
  let mut run : Option (List Nat × Bool) := none
  for token in tokenize (stripLiterature paragraph) do
    match token, run with
    | .text value, some (numbers, todo) =>
      if trim value != "" then
        claims := claims ++ [close prose numbers todo]
        prose := value
        run := none
    | .text value, none => prose := prose ++ value
    | .cite numbers todo, some (earlier, wasTodo) =>
      run := some (earlier ++ numbers, wasTodo || todo)
    | .cite numbers todo, none => run := some (numbers, todo)
  if let some (numbers, todo) := run then
    claims := claims ++ [close prose numbers todo]
  return claims

/-- Reads a `## Lean References` entry, `n. File.lean — `a`, `b``. -/
def declarationEntry (line : String) : Option APIMapReference := do
  let trimmed := trim line
  let (number, rest) ← match trimmed.splitOn ". " with
    | number :: rest => pure (number, String.intercalate ". " rest)
    | [] => none
  let index ← (trim number).toNat?
  match rest.splitOn " — " with
  | [] => none
  | file :: names =>
    /- An entry wrapped immediately after its dash leaves the dash on the
    file; its declarations arrive on the continuation line. -/
    let file := trim file
    let file := if file.endsWith "—" then trim (file.dropEnd 1).toString else file
    let declarations := backtickedSpans (String.intercalate " — " names)
    pure { index := index, file := file, declarations := declarations }

/-- The section a line belongs to. -/
inductive Section
  | preamble
  | abstract
  | content (alpha : Bool)
  | references
  | literature
  | unknown
deriving BEq

/-- The section a `##` heading opens. -/
def sectionOf (heading : String) : Section :=
  match heading with
  | "Abstract" | "Abstract (Alpha)" => .abstract
  | "Content" => .content false
  | "Content (Alpha)" => .content true
  | "Lean References" => .references
  | "References" => .literature
  | _ => .unknown

/-- Reads one `API-map.md`. The parser is line-based and graceful: fields it
cannot read are left at their defaults instead of raising errors. -/
def parseAPIMap (path : System.FilePath) : IO APIMapData := do
  let lines := (← IO.FS.readFile path).splitOn "\n"
  let mut map : APIMapData := { path }
  let mut current := Section.preamble
  let mut paragraph : List String := []
  let mut abstractParagraphs : List String := []
  let mut contentParagraphs : List (Bool × String) := []
  for line in lines ++ [""] do
    let trimmed := trim line
    /- A blank line, a heading, or the end of the file closes the paragraph
    under construction. -/
    if trimmed == "" || trimmed.startsWith "#" then
      if !paragraph.isEmpty then
        let text := String.intercalate " " paragraph.reverse
        match current with
        | .abstract => abstractParagraphs := abstractParagraphs ++ [text]
        | .content alpha => contentParagraphs := contentParagraphs ++ [(alpha, text)]
        | _ => pure ()
      paragraph := []
    if trimmed.startsWith "# " && map.title == "" then
      map := { map with title := trim (trimmed.drop 2).toString }
    else if trimmed.startsWith "## " then
      let heading := trim (trimmed.drop 3).toString
      current := sectionOf heading
      if heading == "Abstract (Alpha)" then map := { map with alpha := true }
    else if trimmed == "" || trimmed.startsWith "#" then
      pure ()
    else
      match current with
      | .abstract | .content _ => paragraph := trimmed :: paragraph
      | .references =>
        /- A long entry may be wrapped over several lines; a line that does not
        open a new numbered entry continues the previous one. -/
        match declarationEntry trimmed, map.declarations.reverse with
        | some reference, _ =>
          map := { map with declarations := map.declarations ++ [reference] }
        | none, last :: earlier =>
          let continued := { last with
            declarations := last.declarations ++ backtickedSpans trimmed }
          map := { map with declarations := earlier.reverse ++ [continued] }
        | none, [] => pure ()
      | .literature =>
        /- As for the Lean references, a line that does not open a new numbered
        entry continues the previous one. -/
        match trimmed.splitOn ". ", map.references.reverse with
        | number :: rest, _ =>
          if (trim number).toNat?.isSome then
            map := { map with references := map.references ++ [String.intercalate ". " rest] }
          else if let last :: earlier := map.references.reverse then
            map := { map with references := earlier.reverse ++ [last ++ " " ++ trimmed] }
        | [], _ => pure ()
      | .preamble | .unknown => pure ()
  map := { map with
    overview := String.intercalate "\n\n" abstractParagraphs
    requirements := contentParagraphs.flatMap (fun (alpha, text) => claimsOf alpha text) }
  return map

/-- The paths of every `API-map.md` under `directory`. -/
partial def findAPIMaps (directory : System.FilePath) : IO (List System.FilePath) := do
  let mut paths := []
  for entry in ← directory.readDir do
    if ← entry.path.isDir then
      paths := paths ++ (← findAPIMaps entry.path)
    else if entry.fileName == "API-map.md" then
      paths := entry.path :: paths
  return paths

/-!

## C. Creating the YAML file

-/

/-- A double-quoted YAML scalar. -/
def yamlQuote (value : String) : String :=
  "\"" ++ ((value.replace "\\" "\\\\").replace "\"" "\\\"").replace "\n" " " ++ "\""

/-- A key with a list of quoted strings, or `[]` when empty. -/
def yamlStringList (key : String) (indent : String) (items : List String) : String :=
  if items.isEmpty then s!"{indent}{key}: []"
  else s!"{indent}{key}:" ++
    String.join (items.map (fun item => s!"\n{indent}  - {yamlQuote item}"))

/-- A key with a quoted scalar, or a `|` block when the value is multi-line.
Block content is indented two spaces past `indent`. -/
def yamlScalarOrBlock (key : String) (indent : String) (value : String) : String :=
  let valueLines := value.splitOn "\n"
  if valueLines.length ≤ 1 then s!"{indent}{key}: {yamlQuote value}"
  else s!"{indent}{key}: |" ++
    String.join (valueLines.map (fun valueLine =>
      if valueLine == "" then "\n" else s!"\n{indent}  {valueLine}"))

/-- A Lean reference as a YAML list item. -/
def APIMapReference.toYAML (reference : APIMapReference) : String :=
  s!"      - index: {reference.index}\n" ++
  s!"        file: {yamlQuote reference.file}\n" ++
  yamlStringList "declarations" "        " reference.declarations

/-- A claim of a map as a YAML list item, with its location. -/
def APIMapData.requirementYAML (map : APIMapData) (requirement : APIMapRequirement) : String :=
  yamlScalarOrBlock "- description" "      " requirement.description ++ "\n" ++
  s!"        done: {requirement.done}\n" ++
  s!"        location: {yamlQuote (map.locationOf requirement)}\n" ++
  s!"        citations: [{String.intercalate ", " (requirement.citations.map toString)}]\n" ++
  s!"        alpha: {requirement.alpha}"

/-- A map as a YAML list item. -/
def APIMapData.toYAML (map : APIMapData) : String :=
  let requirementsPart :=
    if map.requirements.isEmpty then "    requirements: []"
    else "    requirements:\n" ++
      String.intercalate "\n" (map.requirements.map (map.requirementYAML ·))
  let declarationsPart :=
    if map.declarations.isEmpty then "    leanDeclarations: []"
    else "    leanDeclarations:\n" ++
      String.intercalate "\n" (map.declarations.map APIMapReference.toYAML)
  s!"  - path: {yamlQuote map.path.toString}\n" ++
  s!"    module: {yamlQuote map.moduleContext}\n" ++
  s!"    githubLink: {yamlQuote map.githubLink}\n" ++
  s!"    title: {yamlQuote map.title}\n" ++
  s!"    alpha: {map.alpha}\n" ++
  yamlStringList "references" "    " map.references ++ "\n" ++
  s!"    done: {map.doneCount}\n" ++
  s!"    total: {map.totalCount}\n" ++
  yamlScalarOrBlock "overview" "    " map.overview ++ "\n" ++
  requirementsPart ++ "\n" ++
  declarationsPart

/-- The YAML data file for all the maps: the totals, then each map. -/
def indexYAML (maps : List APIMapData) : String :=
  let done := maps.foldl (fun count map => count + map.doneCount) 0
  let total := maps.foldl (fun count map => count + map.totalCount) 0
  s!"Total:\n  maps: {maps.length}\n  requirements: {total}\n  done: {done}\n" ++
  "APIMap:\n\n" ++
  String.intercalate "\n\n" (maps.map APIMapData.toYAML) ++ "\n"

/-!

## D. Main function

-/

/-- Prints the YAML data file, and writes it when passed `mkFile`. -/
def main (args : List String) : IO UInt32 := do
  let mut paths : List System.FilePath := []
  for root in ["Physlib", "PhyslibAlpha", "QuantumInfo"] do
    let rootPath : System.FilePath := { toString := root }
    if ← rootPath.pathExists then
      paths := paths ++ (← findAPIMaps rootPath)
  let sorted := paths.mergeSort (fun a b => a.toString ≤ b.toString)
  let maps ← sorted.mapM parseAPIMap
  let ymlString := indexYAML maps
  IO.println ymlString
  let fileOut : System.FilePath := { toString := "./docs/_data/APIMap.yml" }
  if "mkFile" ∈ args then
    IO.println s!"APIMap file made for {maps.length} map(s)."
    let dir : System.FilePath := { toString := "./docs/_data" }
    if !(← System.FilePath.pathExists dir) then
      IO.FS.createDirAll dir
    IO.FS.writeFile fileOut ymlString
  pure 0
