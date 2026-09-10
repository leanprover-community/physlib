
<div align="center">
<img src="./docs/Physlib-logo.jpeg" alt="Physlib logo" width="500">
</div>


<div align="center">

## An open-source, community, project to digitalize results from physics into Lean 4



[![](https://img.shields.io/badge/Getting-Started-darkgreen)](https://physlib.io/GettingStarted.html)
[![](https://img.shields.io/badge/The-Website-darkgreen)](https://physlib.io)
[![](https://img.shields.io/badge/How_To-Get_Involved-darkgreen)](https://physlib.io/get-involved)
[![](https://img.shields.io/badge/Physlib_Zulip-Discussion-darkgreen)](https://leanprover.zulipchat.com/#narrow/channel/479953-Physlib/)
[![](https://img.shields.io/badge/TODO-List-darkgreen)](https://physlib.io/todo)


[![](https://img.shields.io/badge/View_The-Stats-blue)](https://physlib.io/Stats)
[![](https://img.shields.io/badge/Lean-v4.33.0-blue)](https://github.com/leanprover/lean4/releases/tag/v4.33.0)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/leanprover-community/physlib)
[![Ask DeepWiki](https://deepwiki.com/badge.svg)](https://deepwiki.com/leanprover-community/physlib)
[![api_docs](https://img.shields.io/badge/doc-API_docs-blue)](https://physlib.io/docs/)

</div>

<table>
<tr>
<td colspan="3" align="center">

<sub><b>UPSTREAM</b></sub> · [**Mathlib**](https://github.com/leanprover-community/mathlib4) ↑

</td>
</tr>
<tr>
<td colspan="3" align="center">

<sub><b>THIS REPOSITORY</b></sub>

</td>
</tr>
<tr>
<td width="33%" valign="top">

### [**Physlib**](./Physlib)

The core library — physics digitalizations reviewed and curated to a high standard, built for long-term reuse, readability, trust, and maintenance.

</td>
<td width="33%" valign="top">

###  [**PhyslibAlpha**](./PhyslibAlpha)
### [**PhyslibAlpha**](./PhyslibAlpha)

PhyslibAlpha exists for the rapid development of physics digitalizations, enabled by a lighter review process built to handle large-scale, human- or AI-generated contributions.

</td>
<td width="33%" valign="top">

### [**QuantumInfo**](./QuantumInfo)

Quantum information theory. Currently a distinct codebase with its own conventions and review norms; work is underway to bring it closer to Physlib.

</td>
</tr><tr>
<td colspan="3" align="center"></td></tr>
<tr>
<td colspan="3" align="center">

<sub><b>ADJACENT</b></sub> · [**CSLib**](https://github.com/leanprover/cslib) →

</td>
</tr>
</table>

## Requirements of the project

🎯 The project shall contain results (definitions, theorems, lemmas and calculations) from **physics**,
  including quantum information, formalized (or **digitalized**) into the interactive theorem prover **Lean 4**.
including quantum information, formalized (or **digitalized**) into the interactive theorem prover **Lean 4**.

🎯 The project shall be **organized** by **physics**.

🎯 Each definition in the project shall carry a physics-based **documentation**.

🎯 Each module (file) in the project shall carry a physics-based **documentation**.

🎯 The project shall contain Physics Lean **tactics**, **notation** and **syntax** for physicists.

🎯 The project shall *not* be tied to physics axiomizations (e.g. axiomatic QFT), but rather flexiable enough to accommodate different approaches and starting points.
🎯 The project shall _not_ be tied to physics axiomizations (e.g. axiomatic QFT), but rather flexiable enough to accommodate different approaches and starting points.

🎯 The content of the project shall be carefully **reviewed** and curated, to ensure reusability, readability and fit.

🎯 The project shall be completely open-source, community run and independent from any company or organization.

🎯 The project shall not be tied to any specific AI model or tool.

🎯 The project shall be for **mainstream** physics only.


## PhyslibAlpha

PhyslibAlpha sits downstream of `./Physlib` (within the same repository). The core idea is that PhyslibAlpha has a lower review-standards then Physlib making it easier to contribute large PRs, AI-generated content, or formalizations which are not-quite-perfect. PRs for PhyslibAlpha must pass basic linter checks, described [here](https://github.com/leanprover-community/physlib/blob/master/scripts/PhyslibAlpha/README.md). PRs must also undergo a light 'one-look' review checking 1) Whether the content is main-stream physics, 2) Whether it looks reasonable (no axioms, easy to read etc.), 3) Whether it is within the right place within PhyslibAlpha (mirroring its place in Physlib).

Because of the lower-review bar for PhyslibAlpha we cannot promise to maintain contributions when they break — we will simply record when this happens.

## Contributing to Physlib

Physlib is open-source and community run, and we welcome contributions from anyone.
All you need to do is open a pull-request with your changes
and our team of maintainers will review it and iterate with you on feedback until it
can be merged. Please add references to the `## References` section at the top of the file
and add them to the .bib file.

If you unsure where you would like to contribute, you may find ideas on:
- our [open issues](https://github.com/leanprover-community/physlib/issues).
- our [todo list](https://physlib.io/todo)
- our [Get Involved page](https://physlib.io/get-involved)
- the [quantumInfo todo page](./docs/WildeTODO.md)
> [!NOTE]
> If stuck at any point there are lots of people happly to help on the [Physlib zulip](https://leanprover.zulipchat.com/#narrow/channel/479953-Physlib)

### Installing Lean 4

Installation instructions for Lean 4 can be found:

- https://lean-lang.org/lean4/doc/quickstart.html

or

- https://leanprover-community.github.io/get_started.html

### Installing Physlib

- Clone this repository (or download the repository as a Zip file)
- Open a terminal at the top-level in the corresponding directory.
- Run `lake exe get_cache` to download the cached artifacts from the internet. This will speed up the next step drastically. Do not worry if it fails, you can still run `lake build`, it will just be much slower.
- Run `lake build`.
- Open the directory (not a single file) in Visual Studio Code (or another Lean compatible code editor).

Once set up, `lake build` only recompiles files you have actually changed, plus
anything importing them.

At the moment Physlib is divided into two essentially disjoint halves, `Physlib` and `QuantumInfo`.
These were two repositories that merged in an effort to create a more cohesive ecosystem for physics
in Lean. There is ongoing effort to integrate them more deeply and share code, but at the moment
they offer two separate _build targets_: `Physlib` and `QuantumInfo`, as specified in `lakefile.lean`.
They are both default targets, so `lake build` will build both.

If you only want to build one, `lake build Physlib` or `lake build QuantumInfo` will target just one
or the other. This could be useful if you're working on one part or the other and want to see that
all your changes worked, or if you're only interested in having one or the other as a dependency in
your project.

### Making a pull-request

There are lots of guides on how to make a pull-request on GitHub. The first thing you
need to do is fork the repository. Once you've made your pull request we will review it:
- Guide to [Physlib reviews](https://github.com/leanprover-community/physlib/blob/master/docs/ReviewGuidelines.md).
It will also undergo a number of automated checks called linters. Sometimes these are easier
to run locally:
- Guide to [linters and running them locally](https://github.com/leanprover-community/physlib/blob/master/scripts/README.md).

Most importantly:
> [!NOTE]
> When making contributing to Physlib it is much better to do it with small steps. This makes it easier for us to review, and allows you to get feedback sooner.

## Maintainers

Below are the maintainers of the project, however the best way to reach them is by posting
on the [Lean Zulip](https://leanprover.zulipchat.com/#narrow/channel/479953-Physlib)

- Léo Lessa (@Megaleo)
- Alex Meiburg (@Timeroot)
- Daniel Morrison (@morrison-daniel)
- Zhi-Kai Pong (@zhikaip)
- Rodolfo Soldati (@rodolfor-s)
- Joseph Tooby-Smith (@jstoobysmith)
- Winston Yin (@winstonyin)

## Citing the project

If you want to cite the project as a whole please cite:

```bibtex
@misc{physlib,
  author = {The Physlib community},
  title = {Physlib: The Lean Physics Library},
  year = {2024},
  publisher = {GitHub},
  journal = {GitHub repository},
  howpublished = {\url{https://github.com/leanprover-community/physlib}},
}
```

Physlib was formed by merging the general physics Lean library PhysLean (formerly called HepLean)
with the quantum-information library Lean-QuantumInfo. Where appropriate please also consider
citing the papers associated with the origin of these projects. For the former please use:
```bibtex
@article{Tooby-Smith:2024vqu,
    author = "Tooby-Smith, Joseph",
    title = "{HepLean: Digitalising high energy physics}",
    eprint = "2405.08863",
    archivePrefix = "arXiv",
    primaryClass = "hep-ph",
    doi = "10.1016/j.cpc.2024.109457",
    journal = "Comput. Phys. Commun.",
    volume = "308",
    pages = "109457",
    year = "2025"
}
```
and for the latter please use:

```bibtex
@article{Meiburg:2025mwn,
    author = "Meiburg, Alex and Lessa, Leonardo A. and Soldati, Rodolfo R.",
    title = "{A Formalization of the Generalized Quantum Stein's Lemma in Lean}",
    eprint = "2510.08672",
    archivePrefix = "arXiv",
    primaryClass = "quant-ph",
    month = "10",
    year = "2025"
}
```
