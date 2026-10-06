# Writing good API maps

An `API-map.yaml` file records what an API is meant to contain, what has been
built, and where each piece lives in the Lean source. It is the human-readable
contract for an API directory: a reader can see the intended scope, tell done
work from planned work, and jump straight to the declaration that realizes each
requirement.

## When to write one

Write an `API-map.yaml` for any API that groups a coherent body of definitions
and results, for example `Time`, `Space`, the Lorentz group, or the quantum
operators. If a directory holds an API worth documenting as a unit, it gets a
map. Requirements that are planned but not yet formalized still belong in the
map, marked as not done, so the map doubles as the API's roadmap.

## File location

One `API-map.yaml` sits in the top directory of the API it describes:

    Physlib/SpaceAndTime/Time/API-map.yaml
    Physlib/Relativity/LorentzGroup/API-map.yaml
    Physlib/QuantumMechanics/HilbertSpaces/SpaceD/API-map.yaml

The map's own path is the API's directory; the `location` field of each
requirement then points at the specific `.lean` files under (or near) it.

## Schema

Every map has these six top-level keys:

- `version`: the schema version, currently `v0.1`.
- `Title`: the API's name, e.g. `Time`, `"Lorentz Group"`.
- `Overview`: a short prose description of the API. Use a YAML block scalar
  (`Overview: |`) for multi-line text.
- `ParentAPIs`: a list of the APIs this one builds on, each a string naming
  the API and its directory, e.g. `"Space (Physlib/SpaceAndTime/Space)"`. Use
  `[]` if there are none.
- `References`: a list of external references (papers, notes). Use `[]` if
  there are none.
- `Requirements`: a list of requirement entries.

Each entry in `Requirements` has exactly three keys:

- `description`: one sentence stating what the API should contain. Present
  tense for done work ("The API contains..."), "shall" for planned work.
- `done`: `true` if formalized, `false` if planned.
- `location`: where the result lives (see below); `N/A` when `done: false`.

Minimal shape:

    version: v0.1
    Title: Time
    Overview: |
        One or more lines describing the API.
    ParentAPIs:
      - "Space (Physlib/SpaceAndTime/Space)"
    References: []
    Requirements:
      - description: "The key data structure `Time` is defined."
        done: true
        location: "Physlib/SpaceAndTime/Time/Basic.lean (Time)"

## Writing a good `location`

The `location` is the load-bearing field. Its job is to let a reader (and the
linter) find the exact declarations that realize the requirement. The grammar
is: one or more file groups, each a file path followed by a parenthesized,
comma-separated list of names.

    Physlib/SpaceAndTime/Time/InnerProductSpace.lean (AddCommGroup Time, toRealCLM)

Rules:

- **Use the exact repo-relative file path**, ending in `.lean`.
- **List the actual declaration names**, comma-separated, inside `(...)`. Use
  the names as they appear in the source (`deriv_smul`, `Time.deriv`,
  `RigidBody.mass`).
- **Instance types** name a class applied to arguments rather than a single
  declaration: `AddCommGroup Time`, `Module ℝ Time`,
  `InnerProductSpace ℝ (Space d)`. These are fine and expected; write the type
  exactly. (The grep-tier linter cannot verify instance types and reports them
  as needing the Lean environment, rather than passing or failing them, so keep
  them precise.)
- **Typed declarations** may include the signature after a colon, e.g.
  `slice : Space d.succ ≃L[ℝ] ℝ × Space d`. The name before ` : ` is what gets
  checked, so keep it correct.
- **Notations** are written with the `notation ` prefix, e.g. `notation ∂ₜ`,
  `notation 𝐱`. A bare glyph with no spaces (e.g. `⨯ₑ₃`) is also read as a
  notation.

### Multiple files: the `;` form

When one requirement is realized across several files, separate the file groups
with a semicolon:

    Physlib/SpaceAndTime/Space/Module.lean (Norm, InnerProductSpace ℝ (Space d)); Physlib/SpaceAndTime/Space/Basic.lean (Dist, MetricSpace)

Each `;`-separated group is `FILE (names...)` on its own. A long list may be
written as a YAML block scalar to keep lines readable:

    location: |
      Physlib/QuantumMechanics/Operators/Position.lean (positionCLM, notation 𝐱); Physlib/QuantumMechanics/Operators/Momentum.lean (momentumCLM, notation 𝐩)

### Unimplemented requirements

For a requirement that is planned but not yet formalized, set:

    done: false
    location: N/A

Do not point `location` at a file that does not yet contain the result. `N/A`
with `done: false` is the correct way to record scope that is still open.

## YAML quoting pitfall: the colon

A colon-space (`: `) inside an unquoted scalar starts a new YAML mapping and
breaks the parse. This bites descriptions and locations that contain a colon:

    # BROKEN — the ": " inside the parentheses is read as a key/value split
    - description: Instance as a Lie group (blocked: needs Cartan's theorem)

Quote the whole value:

    - description: "Instance as a Lie group (blocked: needs Cartan's theorem)"

When in doubt, wrap `description` and `location` values in double quotes. This
also protects leading special characters and inline `#`. Signatures that
contain a colon (`slice : Space d.succ ≃L[ℝ] ℝ × Space d`) are safe inside the
`(...)` of a quoted `location`, but the surrounding value must be quoted.

## Run the linter before opening a PR

The linter checks the schema (the six top-level keys and each requirement's
three keys) and, for every done requirement with a real location, that the named
file exists and each plain declaration and notation is present in it.

Run it from the repository root, exactly as CI does. The linter needs PyYAML,
which CI installs with pip before this step; locally, `pip install PyYAML` once
if you do not have it.

    python scripts/lint/required/api_map_linter.py --repo .
    python scripts/lint/required/api_map_linter.py --repo . --verbose

A clean run reports every file as `ok` and no `MISSING_FILE` or `MISSING_NAME`
in the summary. `need_Lean_env` counts instance-type claims grep cannot verify;
that is expected and not a failure. The linter exits non-zero on any real
failure (unparsable YAML, missing schema key, missing file, or a named
declaration that is not in the file it points to). Run it until green before
opening a PR.

## The generated site index

`lake exe api_map_index` gathers every `API-map.yaml` into a single YAML data
file, `docs/_data/APIMap.yml`, in the same way `TODO_to_yml` builds
`docs/_data/TODO.yml` for the website's TODO list. The file records each map's
path, module context, title, overview, parents, references, and requirements,
with per-map and total completion counts, and the website repository renders
it. A plain run prints the YAML to standard output; passing `mkFile` writes
the file.
