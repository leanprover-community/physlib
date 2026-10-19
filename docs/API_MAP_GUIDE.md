# Writing good API maps

## What is an API map

In Physlib an API map is a human-readable document which discusses the physics
in a given area, and links to the corresponding Lean declarations.

It can be thought of as a `Roadmap`, a `Blueprint`, or as a `Wiki`.

## The file format of an API map

An API map is a `.md` file. This allows it to easily be viewed and edited both in VSCode, and on GitHub.

## Structure

The API map should have the following structure:
- **Title**: A single `# ` heading with the API's name.
- **Abstract**: A single section titled with either `## Abstract` or `## Abstract (Alpha)`.

  The distinction between `## Abstract` and `## Abstract (Alpha)` is that the latter is used for API maps which have not gone under the stringent review process. Similar to the distinction between Physlib and PhyslibAlpha.

  The abstract should be a single paragraph.
- **Content**: A section titled `## Content`. This is a discussion of the concepts in a given area, with references to the corresponding Lean declarations.
- **Content (Alpha)**: A section titled `## Content (Alpha)`. Same as `## Content`, but for API maps which have not gone under the stringent review process. It should extend what is in `## Content`.

  An API map can have both `## Content` and `## Content (Alpha)` sections, or just one.

  Both `## Content` and `## Content (Alpha)` sections can cite Physlib or PhyslibAlpha, the
  `Alpha` here refers to the less strictly reviewed version of the content, not the content.

- **Lean References**: A section titled `## Lean References` linking concepts discussed in the content sections to their corresponding Lean declarations.
- **References**: A section titled `## References` linking to external sources, such as papers, textbooks, or websites, that provide additional context or background for the concepts discussed in the API map. This must come directly after **Lean References**.

Some notes:
- You can have a `## Abstract (Alpha)` with a `## Content` section, although this is advised against.

## Lean citations

The *Content* explains the API in words, as you would
explain it to a colleague who does not yet know the Lean names; the Lean
declarations are collected at the end, and the prose points at them with
numbered citations — `[1]`, `[2]` — in the manner of a paper's bibliography.
Any part of *Content* which has not yet been formalized in Lean is marked `[TODO]`.

Each citation must come in its own square bracket e.g. `[1][2]` not `[1,2]`.
The abstract must not contain any citations, whether Lean or literature.

## Literature citations

Literature citations should be cited using curly brackets e.g. `{1}`. This helps distinguish them from Lean citations, which use square brackets. This should include links to other API maps.

No raw link should be included in an API map; all references should be properly cited in the `## References` section using the curly bracket notation. No `[markdown](links)` should appear directly in the content or abstract. This is because these are not easy to parse when looking at raw markdown files.

Each citation must come in its own curly bracket e.g. `{1}{2}` not `{1,2}`.

## Content first style

A content first style should be taken. For example:
```
A general gauge theory admits an arbitrary Lie group as its structure group. [TODO] Its
gauge field takes values in the Lie algebra of that group. [TODO] Matter fields carry a
gauge-covariant derivative with a defined transformation law. [TODO] The non-abelian field.
```

Not the following (which is a RoadMap style)
```
The general non-abelian theory remains planned. It will allow an arbitrary Lie group as the structure group and define a gauge field valued in its Lie algebra. [TODO] It will also define the gauge-covariant derivative on matter fields and its transformation law, along with the Yang–Mills curvature and its covariant transformation. [TODO] The Yang–Mills action and its field equations, parallel transport and holonomy, and a formulation of gauge fields as connections on principal bundles are also planned. [TODO]
```

## When to write one

Write an `API-map.md` for any API that groups a coherent body of definitions
and results, for example `Time`, `Space`, the Lorentz group, or the quantum
operators. If a directory holds an API worth documenting as a unit, it gets a
map. Requirements that are planned but not yet formalized still belong in the
map, marked `[TODO]`, so the map doubles as the API's roadmap.

## File location

One `API-map.md` sits in the top directory of the API it describes:

    Physlib/SpaceAndTime/Time/API-map.md
    Physlib/Relativity/LorentzGroup/API-map.md
    Physlib/QuantumMechanics/HilbertSpaces/SpaceD/API-map.md

The map's own path is the API's directory; the reference entries at the end
then point at the specific `.lean` files under (or near) it.

## Writing a reference entry

Each entry of `## Lean References` is one file and the declarations in it
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

The linter checks the following things:
- The correct `# ` and `## ` headings are used.
- Each Lean citation in the text has a corresponding reference.
- Each entry in the references section corresponds to at least one citation in the text.
- Every Lean declaration referenced exists in the corresponding file.

Run it from the repository root with `lake exe api_map_lint` (add `--verbose` to also see notes
on instance claims and Lean names in the prose). It needs no build of Physlib.

## The generated site index

`lake exe api_map_index` greates a single YAML data file, `docs/_data/APIMap.yml`, from all `API-map.md` files in the repository. It lists the contents of each API map in a structured format.
