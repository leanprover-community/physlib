# Writing good API maps

An `API-map.md` file records what an API is meant to contain, what has been
built, and where each piece lives in the Lean source. It is the human-readable
contract for an API directory: a reader can see the intended scope, tell done
work from planned work, and jump straight to the declarations that realize
each requirement.

A map is a prose document. The body explains the API in words, as you would
explain it to a colleague who does not yet know the Lean names; the Lean
declarations are collected at the end, and the prose points at them with
numbered citations — `[1]`, `[2]` — in the manner of a paper's bibliography.
A requirement with no citation yet is marked `[planned]`.

The format used to be a YAML file, `API-map.yaml`, in which each requirement
was a `description`/`done`/`location` triple. Nothing about that is lost: the
paragraph is the description, a citation means done, and the reference entry
is the location. What is gained is that the file now reads as a document
rather than as a data structure, and that the Lean names live in one place
instead of being scattered through the text.

## When to write one

Write an `API-map.md` for any API that groups a coherent body of definitions
and results, for example `Time`, `Space`, the Lorentz group, or the quantum
operators. If a directory holds an API worth documenting as a unit, it gets a
map. Requirements that are planned but not yet formalized still belong in the
map, marked `[planned]`, so the map doubles as the API's roadmap.

## File location

One `API-map.md` sits in the top directory of the API it describes:

    Physlib/SpaceAndTime/Time/API-map.md
    Physlib/Relativity/LorentzGroup/API-map.md
    Physlib/QuantumMechanics/HilbertSpaces/SpaceD/API-map.md

The map's own path is the API's directory; the reference entries at the end
then point at the specific `.lean` files under (or near) it.

## The shape of a map

    # Time

    An instant of time is modelled by a single real number, together with an
    arbitrary but fixed choice of unit and orientation.

    Instants form an affine space over the reals: any two of them determine an
    elapsed time, and none is canonically zero.

    ## Built on

    - Space — `Physlib/SpaceAndTime/Space`

    ## Requirements

    The key data structure is defined: a structure with a single real field,
    representing an instant of time. [1]

    Instants carry an affine structure over the reals, with real-valued
    translations and real-valued elapsed times between them. [2]

    Time will carry an action of the translation group. [planned]

    ## Further reading

    - Lean Zulip, #Physlib > Space vs EuclideanSpace: https://...

    ## Lean declarations

    1. Physlib/SpaceAndTime/Time/Basic.lean — `Time`
    2. Physlib/SpaceAndTime/Time/Basic.lean — `VAdd ℝ Time`, `VSub ℝ Time`,
       `AddTorsor ℝ Time`, `vadd_val`, `vsub_eq_val`

The pieces, in order:

- **The title** is a single `# ` heading on the first line: the API's name,
  e.g. `# Time`, `# Lorentz group`.
- **The overview** is the prose between the title and the first section: one
  or more paragraphs describing what the API is for and how it hangs
  together. This is the part a reader meeting the API for the first time
  reads, so write it for them.
- **`## Built on`** lists the APIs this one depends on, one per line, as
  `- Name — `path``. Omit the section if there are none.
- **`## Requirements`** is the body: one paragraph per requirement (see
  below). Required.
- **`## Further reading`** lists external references — papers, books, Zulip
  threads — one per line. Omit the section if there are none.
- **`## Lean declarations`** is the numbered reference list, and must come
  last. Required; write `*None yet.*` if the API is all roadmap so far.

No other `##` sections are allowed, and the sections come in this order.

## Writing a requirement

A requirement is one paragraph of prose, closed by its citations:

    Instants carry an affine structure over the reals, with real-valued
    translations of instants and real-valued elapsed times between them. [2]

Rules:

- **One paragraph, one requirement.** Paragraphs are separated by a blank
  line. Keep a requirement to a sentence or two; if it needs three, it is
  probably two requirements.
- **Every paragraph ends in citations or `[planned]`.** A paragraph with
  citations alone is done work; `[planned]` is scope that is still open, and
  is the only correct way to record it. Do not cite a file that does not yet
  contain the result.
- **A planned requirement may still cite**, with `[planned]` last, when
  something partial already stands in for it — most often an informal
  statement awaiting formalization. It still counts as planned: the marker,
  not the citation, is what says whether a requirement is done.
- **Write done work in the present tense** ("Instants carry an affine
  structure...") and planned work in the future ("Time will carry an action of
  the translation group.").
- **Keep Lean names out of the prose.** Say "the time derivative of a function
  of time", not "`Time.deriv`"; the citation says which declaration that is.
  Mathematical notation that is ordinary prose (ℝ, `d`-dimensional) is fine.
  The linter counts backticked names in requirement prose and reports the
  total; it does not fail on them, because the occasional name really is the
  clearest wording — but a map with many of them has not been written as
  prose.
- **Cite several references when a requirement spans several files**, by
  writing the citations one after another: `[3][4]`. Each reference entry
  covers exactly one file.
- Do not write "The API contains...". Everything in the file is what the API
  contains; say what the thing *is* instead.

## Writing a reference entry

Each entry of `## Lean declarations` is one file and the declarations in it
that the citing requirement is about:

    7. Physlib/SpaceAndTime/Time/Derivatives.lean — `Time.deriv`, `notation ∂ₜ`,
       `deriv_smul`, `deriv_const`

Rules:

- **Numbered from 1, in order**, with no gaps. Every entry must be cited by
  some requirement, and every citation must resolve to an entry.
- **Use the exact repo-relative file path**, ending in `.lean`, followed by an
  em dash and the declarations.
- **Each declaration in backticks**, comma-separated. Use the names as they
  appear in the source (`deriv_smul`, `Time.deriv`, `RigidBody.mass`). An
  entry may be long; wrap it over several lines, indented, as above.
- **Instance types** name a class applied to arguments rather than a single
  declaration: `` `AddCommGroup Time` ``, `` `Module ℝ Time` ``,
  `` `InnerProductSpace ℝ (Space d)` ``. These are fine and expected; write
  the type exactly. (The grep-tier linter cannot verify instance types and
  reports them as needing the Lean environment, rather than passing or failing
  them, so keep them precise.)
- **Typed declarations** may include the signature after a colon, e.g.
  `` `slice : Space d.succ ≃L[ℝ] ℝ × Space d` ``. The name before ` : ` is
  what gets checked, so keep it correct.
- **Notations** are written with the `notation ` prefix, e.g.
  `` `notation ∂ₜ` ``, `` `notation 𝐱` ``. A bare glyph with no spaces (e.g.
  `` `⨯ₑ₃` ``) is also read as a notation.
- One file per entry. Two requirements that touch the same file get two
  entries, each listing the declarations that requirement is about.

## Run the linter before opening a PR

The linter checks the document's shape (the title, the overview, the required
sections and their order), that every requirement closes with citations or
`[planned]`, that citations and entries correspond, and, for every entry, that
the file exists and each declaration and notation named is present in it. It
needs no third-party packages.

Run it from the repository root, exactly as CI does:

    python scripts/lint/required/api_map_linter.py --repo .
    python scripts/lint/required/api_map_linter.py --repo . --verbose

A clean run reports every file as `ok` and no `MISSING_FILE` or `MISSING_NAME`
in the summary. `need_Lean_env` counts instance-type claims grep cannot verify,
and `lean_names_in_prose` counts requirement paragraphs still carrying
backticked names; neither is a failure. The linter exits non-zero on any real
failure (a malformed document, a missing section, an uncited or dangling
reference, a missing file, or a named declaration that is not in the file it
points to). Run it until green before opening a PR.

## The generated site index

`lake exe api_map_index` gathers every `API-map.md` into a single YAML data
file, `docs/_data/APIMap.yml`, in the same way `TODO_to_yml` builds
`docs/_data/TODO.yml` for the website's TODO list. The file records each map's
path, module context, title, overview, parents, further reading, requirements
and Lean declarations, with per-map and total completion counts, and the
website repository renders it. Each requirement also keeps a `location` field,
rebuilt from the entries it cites, so consumers that want the plain
`file (names)` form still have it. A plain run prints the YAML to standard
output; passing `mkFile` writes the file.
