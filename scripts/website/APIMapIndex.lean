/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
/-!
# API map index

This executable gathers every `API-map.md` in the library into a single
YAML data file, `docs/_data/APIMap.yml`, for the website to render. It follows
the pattern of `scripts/website/TODO_to_yml.lean`, which builds
`docs/_data/TODO.yml` for the website's TODO list: the YAML is printed to
standard output, and passing `mkFile` writes the file.

The output carries, for each map in sorted path order: the map path, its
module context, a GitHub link, and the map's title, overview, parent APIs,
further reading, requirements and Lean declarations, together with per-map and
total completion counts.

An API map is a prose document, described in `docs/API_MAP_GUIDE.md`: a title,
an overview, `## Built on`, `## Requirements` (one paragraph per requirement,
each closing with `[n]` citations or `[planned]`), `## Further reading`, and
`## Lean declarations` (a numbered list of `file — names` entries). The parser
below reads exactly that shape; lines outside it are ignored rather than
raising errors. Each requirement's `location` is reconstructed from the
entries it cites, so the data file keeps the `file (names)` form the website
already renders.
-/

/-- One entry of the `## Lean declarations` list: the number it is cited by,
the Lean file, and the declarations claimed to be in it. -/
structure APIMapReference where
  index : Nat
  file : String
  declarations : List String
deriving Inhabited

/-- One requirement paragraph. `citations` are the reference numbers closing
the paragraph; a planned requirement has none. -/
structure APIMapRequirement where
  description : String := ""
  done : Bool := false
  citations : List Nat := []

/-- The contents of one `API-map.md` file. -/
structure APIMapData where
  path : System.FilePath
  title : String := ""
  overview : String := ""
  parentAPIs : List String := []
  references : List String := []
  requirements : List APIMapRequirement := []
  declarations : List APIMapReference := []

def APIMapData.doneCount (map : APIMapData) : Nat :=
  (map.requirements.filter (fun requirement => requirement.done)).length

def APIMapData.totalCount (map : APIMapData) : Nat :=
  map.requirements.length

/-- The dotted module context of a map, e.g. `Physlib.SpaceAndTime.Time`. -/
def APIMapData.moduleContext (map : APIMapData) : String :=
  ((map.path.parent.getD map.path).toString.replace "/" ".")

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

## Parsing

-/

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

/-- Peels the `[n]` citations and the `[planned]` marker off the end of a
paragraph, innermost last. -/
partial def peelCitations (text : String) (acc : List Nat) (planned : Bool) :
    String × List Nat × Bool :=
  let trimmed := trim text
  if trimmed.endsWith "]" then
    let parts : List String := (trimmed.dropEnd 1).toString.splitOn "["
    if parts.length ≤ 1 then (trimmed, acc, planned)
    else
      match parts.getLast? with
      | none => (trimmed, acc, planned)
      | some inner =>
        let head := String.intercalate "[" parts.dropLast
        if inner == "planned" then peelCitations head acc true
        else
          let numbers := (inner.splitOn ",").filterMap (fun part => (trim part).toNat?)
          if numbers.isEmpty then (trimmed, acc, planned)
          else peelCitations head (numbers ++ acc) planned
  else (trimmed, acc, planned)

/-- Reads the closing citations of a requirement paragraph: the prose with
them removed, the numbers cited, and whether it is marked `[planned]`. A
planned requirement may still cite the informal declarations standing in for
it, so being cited and being done are not the same thing. -/
def splitCitations (paragraph : String) : String × List Nat × Bool :=
  peelCitations paragraph [] false

/-- Reads a `## Built on` entry, `- Name — path`, as the `Name (path)` form
used by the data file. -/
def parentEntry (line : String) : String :=
  let body := trim ((trim line).dropPrefix "- ").toString
  match body.splitOn " — " with
  | [name, path] => trim name ++ " (" ++ (backtickedSpans path).headD (trim path) ++ ")"
  | _ => (backtickedSpans body).headD body

/-- Reads a `## Lean declarations` entry, `n. File.lean — `a`, `b``. -/
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
  | overview
  | builtOn
  | requirements
  | furtherReading
  | declarations
  | unknown
deriving BEq

def sectionOf (heading : String) : Section :=
  match heading with
  | "Built on" => .builtOn
  | "Requirements" => .requirements
  | "Further reading" => .furtherReading
  | "Lean declarations" => .declarations
  | _ => .unknown

/-- Reads one `API-map.md`. The parser is line-based and graceful: fields it
cannot read are left at their defaults instead of raising errors. -/
def parseAPIMap (path : System.FilePath) : IO APIMapData := do
  let lines := (← IO.FS.readFile path).splitOn "\n"
  let mut map : APIMapData := { path }
  let mut current := Section.overview
  let mut paragraph : List String := []
  let mut overviewParagraphs : List String := []
  let mut requirementParagraphs : List String := []
  /- Closes the paragraph under construction, if any. -/
  let closeParagraph (paragraph : List String) : Option String :=
    if paragraph.isEmpty then none
    else some (String.intercalate " " paragraph.reverse)
  for line in lines do
    let trimmed := trim line
    if trimmed.startsWith "# " && map.title == "" then
      map := { map with title := trim (trimmed.drop 2).toString }
      continue
    if trimmed.startsWith "## " then
      if let some text := closeParagraph paragraph then
        if current == .overview then overviewParagraphs := text :: overviewParagraphs
        else if current == .requirements then requirementParagraphs := text :: requirementParagraphs
      paragraph := []
      current := sectionOf (trim (trimmed.drop 3).toString)
      continue
    if trimmed == "" then
      if let some text := closeParagraph paragraph then
        if current == .overview then overviewParagraphs := text :: overviewParagraphs
        else if current == .requirements then requirementParagraphs := text :: requirementParagraphs
      paragraph := []
      continue
    match current with
    | .overview | .requirements => paragraph := trimmed :: paragraph
    | .builtOn =>
      if trimmed.startsWith "- " then
        map := { map with parentAPIs := map.parentAPIs ++ [parentEntry trimmed] }
    | .furtherReading =>
      if trimmed.startsWith "- " then
        map := { map with references := map.references ++
          [trim ((trimmed.dropPrefix "- ").toString)] }
    | .declarations =>
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
    | .unknown => pure ()
  if let some text := closeParagraph paragraph then
    if current == .overview then overviewParagraphs := text :: overviewParagraphs
    else if current == .requirements then requirementParagraphs := text :: requirementParagraphs
  map := { map with overview := String.intercalate "\n\n" overviewParagraphs.reverse }
  for text in requirementParagraphs.reverse do
    let (description, citations, planned) := splitCitations text
    map := { map with requirements := map.requirements ++
      [{ description := description, done := !planned, citations := citations }] }
  return map

partial def findAPIMaps (directory : System.FilePath) : IO (List System.FilePath) := do
  let mut paths := []
  for entry in ← directory.readDir do
    if ← entry.path.isDir then
      paths := paths ++ (← findAPIMaps entry.path)
    else if entry.fileName == "API-map.md" then
      paths := entry.path :: paths
  return paths

/-!

## Creating the YAML file

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

def APIMapReference.toYAML (reference : APIMapReference) : String :=
  s!"      - index: {reference.index}\n" ++
  s!"        file: {yamlQuote reference.file}\n" ++
  yamlStringList "declarations" "        " reference.declarations

def APIMapData.requirementYAML (map : APIMapData) (requirement : APIMapRequirement) : String :=
  yamlScalarOrBlock "- description" "      " requirement.description ++ "\n" ++
  s!"        done: {requirement.done}\n" ++
  s!"        location: {yamlQuote (map.locationOf requirement)}\n" ++
  s!"        citations: [{String.intercalate ", " (requirement.citations.map toString)}]"

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
  s!"    done: {map.doneCount}\n" ++
  s!"    total: {map.totalCount}\n" ++
  yamlScalarOrBlock "overview" "    " map.overview ++ "\n" ++
  yamlStringList "parentAPIs" "    " map.parentAPIs ++ "\n" ++
  yamlStringList "references" "    " map.references ++ "\n" ++
  requirementsPart ++ "\n" ++
  declarationsPart

def indexYAML (maps : List APIMapData) : String :=
  let done := maps.foldl (fun count map => count + map.doneCount) 0
  let total := maps.foldl (fun count map => count + map.totalCount) 0
  s!"Total:\n  maps: {maps.length}\n  requirements: {total}\n  done: {done}\n" ++
  "APIMap:\n\n" ++
  String.intercalate "\n\n" (maps.map APIMapData.toYAML) ++ "\n"

/-!

## Main function

-/

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
