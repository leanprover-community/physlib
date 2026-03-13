> [!NOTE]
> Things look different? We've recently undergone a name change and move from /lean-phys-community/PhysLean
> to /leanprover-community/physlib. Same repo, different location and name. This shouldn't affect
> the average user, but please be patient as we update things.


<div align="center">
<img src="./docs/PhysLib-logo.jpeg" alt="PhysLean logo" width="500">
</div>


<div align="center">

## An open-source, community, project to digitalize results from physics into Lean 4



[![](https://img.shields.io/badge/Getting-Started-darkgreen)](https://physlean.com/GettingStarted.html)
[![](https://img.shields.io/badge/The-Website-darkgreen)](https://physlean.com)
[![](https://img.shields.io/badge/How_To-Get_Involved-darkgreen)](https://physlean.com/GetInvolved.html)
[![](https://img.shields.io/badge/PhysLean_Zulip-Discussion-darkgreen)](https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/)
[![](https://img.shields.io/badge/TODO-List-darkgreen)](https://physlean.com/TODOList)

[![](https://img.shields.io/badge/PhysLean-Search-purple)](https://loogle.physlean.com)
[![](https://img.shields.io/badge/PhysLean-Online-purple)](https://live.physlean.com)

[![](https://img.shields.io/badge/View_The-Stats-blue)](https://physlean.com/Stats)
[![](https://img.shields.io/badge/Lean-v4.28.0-blue)](https://github.com/leanprover/lean4/releases/tag/v4.28.0)
[![Gitpod Ready-to-Code](https://img.shields.io/badge/Gitpod-ready--to--code-blue?logo=gitpod)](https://gitpod.io/#https://github.com/HEPLean/HepLean)
[![Ask DeepWiki](https://deepwiki.com/badge.svg)](https://deepwiki.com/HEPLean/PhysLean)
[![api_docs](https://img.shields.io/badge/doc-API_docs-blue)](https://physlean.com/docs/)

</div>


## Requirements of the project

🎯 The project shall contain results (definitions, theorems, lemmas and calculations) from **physics**,
  including quantum information, formalized (or **digitalized**) into the interactive theorem prover **Lean 4**.

🎯 The project shall be **organized** by **physics**.

🎯 Each definition in the project shall carry a physics-based **documentation**.

🎯 Each module (file) in the project shall carry a physics-based **documentation**.

🎯 The project shall contain Physics Lean **tactics**, **notation** and **syntax** for physicists.

🎯 The project shall *not* be tied to physics axiomizations (e.g. axiomatic QFT), but rather flexiable enough to accommodate different approaches and starting points.

🎯 The content of the project shall be carefully **reviewed** and curated, to ensure reusability, readability and fit.

🎯 The project shall be completely open-source, community run and independent from any company or organization.

🎯 The project shall not be tied to any specific AI model or tool.

🎯 The project shall be for **main-stream** physics only.


## Contributing to PhysLib

PhysLib is open-source and community run, and we welcome contributions from anyone.
All you need to do is open a pull-request with your changes
and our team of maintainers will review it and iterate with you on feedback until it
can be merged.

If you unsure where you would like to contribute, you may find ideas on:
- our [open issues](https://github.com/leanprover-community/physlib/issues).
- our [todo list](https://physlean.com/TODOList)
- our [Get Involved page](https://physlean.com/GetInvolved.html)
> [!NOTE]
> If stuck at any point there are lots of people happly to help on the [PhysLib zulip](https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLib)

### Installing Lean 4

Installation instructions for Lean 4 can be found:

- https://lean-lang.org/lean4/doc/quickstart.html

or

- https://leanprover-community.github.io/get_started.html

### Installing PhysLib

- Clone this repository (or download the repository as a Zip file)
- Open a terminal at the top-level in the corresponding directory.
- Run `lake exe cache get`. The command `lake` should have been installed when you installed Lean.
- Run `lake build`.
- Open the directory (not a single file) in Visual Studio Code (or another Lean compatible code editor).

### Making a pull-request

There are lots of guides on how to make a pull-request on GitHub. The first thing you
need to do is fork the repository. Once you've made your pull request we will review it:
- Guide to [PhysLib reviews](https://github.com/leanprover-community/physlib/blob/master/docs/ReviewGuidelines.md).
It will also undergo a number of automated checks called linters. Sometimes these are easier
to run locally:
- Guide to [linters and running them locally](https://github.com/leanprover-community/physlib/blob/master/scripts/README.md).

Most importantly:
> [!NOTE]
> When making contributing to PhysLib it is much better to do it with small steps. This makes it easier for us to review, and allows you to get feedback sooner.

## Maintainers

Below are the maintainers of the project, however the best way to reach them is by posting
on the [Lean Zulip](https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLib)

- Léo Lessa (@Megaleo)
- Alex Meiburg (@Timeroot)
- Daniel Morrison (@morrison-daniel)
- Zhi-Kai Pong (@zhikaip)
- Rodolfo Soldati (@rodolfor-s)
- Joseph Tooby-Smith (@jstoobysmith)
- Winston Yin (@winstonyin)

## Citing the project

If you want to cite the project as a whole please cite:

```
@misc{physlib,
  author = {The PhysLib community},
  title = {PhysLib: The Lean Physics Library},
  year = {2024},
  publisher = {GitHub},
  journal = {GitHub repository},
  howpublished = {\url{https://github.com/leanprover-community/physlib}},
}
```

PhysLib was formed by merging the general physics Lean library PhysLean (formerly called HepLean)
with the quantum-information library Lean-QuantumInfo. Where appropriate please also consider
citing the papers associated with the origin of these projects. For the former please use:
```
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

```
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
