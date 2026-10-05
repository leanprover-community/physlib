/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
/-!
# API map index

This executable gathers every `API-map.yaml` in the library into a single
YAML data file, `docs/_data/APIMap.yml`, for the website to render. It follows
the pattern of `scripts/website/TODO_to_yml.lean`, which builds
`docs/_data/TODO.yml` for the website's TODO list: the YAML is printed to
standard output, and passing `mkFile` writes the file.

The output carries, for each map in sorted path order: the map path, its
module context, a GitHub link, and the map's `version`, `Title`, `Overview`,
`ParentAPIs`, `References`, and `Requirements` fields, together with per-map
and total completion counts.

The project has no YAML parser dependency. The parser below reads the API-map
schema checked by `scripts/lint/required/api_map_linter.py`: the six top-level keys and the
`description`/`done`/`location` fields of each requirement, with inline
scalars, multi-line plain scalars, and `|`/`>` block scalars. Lines outside
the schema are ignored rather than raising errors.
-/

/-- One entry of a map's `Requirements` list. -/
structure APIMapRequirement where
  description : String := ""
  done : Bool := false
  location : String := ""

/-- The contents of one `API-map.yaml` file. -/
structure APIMapData where
  path : System.FilePath
  version : String := ""
  title : String := ""
  overview : String := ""
  parentAPIs : List String := []
  references : List String := []
  requirements : List APIMapRequirement := []

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

/-!

## Parsing

-/

def stripQuotes (value : String) : String :=
  ((value.trimAscii.toString.dropPrefix "\"").toString.dropSuffix "\"").toString

/-- The scalar value of a line after its `key:` prefix. -/
def afterKey (line : String) (key : String) : String :=
  (line.drop key.length).toString.trimAscii.toString

def leadingSpaces (line : String) : Nat :=
  (line.toList.takeWhile (· == ' ')).length

/-- `some fold?` when the scalar value opens a block: `|` literal (`fold?` is
`false`) or `>` folded (`fold?` is `true`), with optional chomping indicator. -/
def blockMarker (value : String) : Option Bool :=
  if value == "|" || value == "|-" || value == "|+" then some false
  else if value == ">" || value == ">-" || value == ">+" then some true
  else none

/-- Assembles collected block-scalar lines: dedent to the minimum indent,
drop trailing blank lines, and for a folded block join into one line. -/
def finishBlock (rawLines : List String) (fold : Bool) : String :=
  let nonEmpty := rawLines.filter (fun line => line.trimAscii.toString != "")
  if nonEmpty.isEmpty then ""
  else if fold then
    String.intercalate " " (nonEmpty.map (fun line => line.trimAscii.toString))
  else
    let minIndent := nonEmpty.foldl (fun acc line => min acc (leadingSpaces line)) (leadingSpaces (nonEmpty.headD ""))
    let dedented := rawLines.map (fun line =>
      if line.trimAscii.toString == "" then "" else (line.drop minIndent).toString)
    String.intercalate "\n" (dedented.reverse.dropWhile (· == "")).reverse

/-- The block scalar currently being collected, if any. -/
inductive BlockTarget
  | overview
  | reqDescription
  | reqLocation
deriving BEq

/-- The top-level list section the parser is inside, if any. -/
inductive ListTarget
  | parentAPIs
  | references
  | requirements
  | none
deriving BEq

/-- Reads one `API-map.yaml`. The parser is line-based and graceful: fields it
cannot read are left at their defaults instead of raising errors. -/
def parseAPIMap (path : System.FilePath) : IO APIMapData := do
  let lines := (← IO.FS.readFile path).splitOn "\n"
  let mut map : APIMapData := { path }
  let mut listMode := ListTarget.none
  let mut blockTarget : Option BlockTarget := none
  let mut blockFold := false
  let mut blockPlain := false
  let mut blockAcc : List String := []
  let mut currentReq : APIMapRequirement := {}
  let mut hasReq := false
  for line in lines do
    let trimmed := line.trimAscii.toString
    let indent := leadingSpaces line
    /- Collect or close an open block or multi-line plain scalar. -/
    if let some target := blockTarget then
      let closes := (indent == 0 && trimmed != "") ||
        (target != BlockTarget.overview &&
          (trimmed.startsWith "done:" || trimmed.startsWith "location:" ||
           trimmed.startsWith "description:" || trimmed.startsWith "- "))
      if !closes then
        if !(blockPlain && trimmed.startsWith "#") then
          blockAcc := blockAcc ++ [line]
        continue
      let content := finishBlock blockAcc blockFold
      match target with
      | .overview => map := { map with overview := content }
      | .reqDescription => currentReq := { currentReq with description := content }
      | .reqLocation => currentReq := { currentReq with location := content }
      blockTarget := none
      blockAcc := []
    if trimmed == "" then continue
    /- Top-level keys. -/
    if indent == 0 then
      listMode := ListTarget.none
      if trimmed.startsWith "version:" then
        map := { map with version := stripQuotes (afterKey trimmed "version:") }
      else if trimmed.startsWith "Title:" then
        map := { map with title := stripQuotes (afterKey trimmed "Title:") }
      else if trimmed.startsWith "Overview:" then
        let value := afterKey trimmed "Overview:"
        if let some fold := blockMarker value then
          blockTarget := some .overview
          blockFold := fold
          blockPlain := false
          blockAcc := []
        else if value != "" then
          map := { map with overview := stripQuotes value }
      else if trimmed.startsWith "ParentAPIs:" then
        if afterKey trimmed "ParentAPIs:" != "[]" then listMode := ListTarget.parentAPIs
      else if trimmed.startsWith "References:" then
        if afterKey trimmed "References:" != "[]" then listMode := ListTarget.references
      else if trimmed.startsWith "Requirements:" then
        listMode := ListTarget.requirements
      continue
    /- Indented lines, interpreted by the enclosing list section. -/
    if listMode == ListTarget.parentAPIs then
      if trimmed.startsWith "- " then
        map := { map with parentAPIs := map.parentAPIs ++ [stripQuotes (afterKey trimmed "- ")] }
    else if listMode == ListTarget.references then
      if trimmed.startsWith "- " then
        map := { map with references := map.references ++ [stripQuotes (afterKey trimmed "- ")] }
    else if listMode == ListTarget.requirements then
      let mut keyLine := trimmed
      if trimmed.startsWith "- " then
        if hasReq then
          map := { map with requirements := map.requirements ++ [currentReq] }
        currentReq := {}
        hasReq := true
        keyLine := afterKey trimmed "- "
      if keyLine.startsWith "description:" then
        let value := afterKey keyLine "description:"
        blockTarget := some .reqDescription
        if let some fold := blockMarker value then
          blockFold := fold
          blockPlain := false
          blockAcc := []
        else
          /- Inline value, possibly continued on more-indented plain lines. -/
          blockFold := true
          blockPlain := true
          blockAcc := if value == "" then [] else [stripQuotes value]
      else if keyLine.startsWith "done:" then
        currentReq := { currentReq with done := afterKey keyLine "done:" == "true" }
      else if keyLine.startsWith "location:" then
        let value := afterKey keyLine "location:"
        /- Locations are one logical line; fold either form onto one line. -/
        blockTarget := some .reqLocation
        blockFold := true
        if blockMarker value |>.isSome then
          blockPlain := false
          blockAcc := []
        else
          blockPlain := true
          blockAcc := if value == "" then [] else [stripQuotes value]
  /- End of file: close any open block and pending requirement. -/
  if let some target := blockTarget then
    let content := finishBlock blockAcc blockFold
    match target with
    | .overview => map := { map with overview := content }
    | .reqDescription => currentReq := { currentReq with description := content }
    | .reqLocation => currentReq := { currentReq with location := content }
  if hasReq then
    map := { map with requirements := map.requirements ++ [currentReq] }
  return map

partial def findAPIMaps (directory : System.FilePath) : IO (List System.FilePath) := do
  let mut paths := []
  for entry in ← directory.readDir do
    if ← entry.path.isDir then
      paths := paths ++ (← findAPIMaps entry.path)
    else if entry.fileName == "API-map.yaml" then
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

def APIMapRequirement.toYAML (requirement : APIMapRequirement) : String :=
  yamlScalarOrBlock "- description" "      " requirement.description ++ "\n" ++
  s!"        done: {requirement.done}\n" ++
  s!"        location: {yamlQuote requirement.location}"

def APIMapData.toYAML (map : APIMapData) : String :=
  let requirementsPart :=
    if map.requirements.isEmpty then "    requirements: []"
    else "    requirements:\n" ++
      String.intercalate "\n" (map.requirements.map APIMapRequirement.toYAML)
  s!"  - path: {yamlQuote map.path.toString}\n" ++
  s!"    module: {yamlQuote map.moduleContext}\n" ++
  s!"    githubLink: {yamlQuote map.githubLink}\n" ++
  s!"    version: {yamlQuote map.version}\n" ++
  s!"    title: {yamlQuote map.title}\n" ++
  s!"    done: {map.doneCount}\n" ++
  s!"    total: {map.totalCount}\n" ++
  yamlScalarOrBlock "overview" "    " map.overview ++ "\n" ++
  yamlStringList "parentAPIs" "    " map.parentAPIs ++ "\n" ++
  yamlStringList "references" "    " map.references ++ "\n" ++
  requirementsPart

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
