# References in Physlib

References connect the informal literature to the formal results in Physlib. They let readers check that what is formalized is correct, and they point to background reading.

## Contents

1. [Put references in the file's references section](#references-section)
2. [Add every reference to references.bib](#references-bib)
3. [Include exact quotes](#exact-quotes)
4. [Prefer open-access sources](#open-access)
5. [Link to the exact page](#exact-page)

<a id="references-section"></a>

## 1. Put references in the file's references section

Each Lean file has a references section, and references to the literature should go there. This makes them easy to find: readers know where to look, and can quickly see what a given file draws on.

<a id="references-bib"></a>

## 2. Add every reference to references.bib

Every reference should have an entry in `docs/references.bib` at the root of the repository. These entries are used to generate the references on the website, and keeping them in one place means references aren't duplicated and everything links back to a single source. Each item in a file's references section should give the authors, the title, where in the source the result can be found, and the BibTeX key in the form `[ref: key]`. For example:

```
* Landau & Lifshitz, Mechanics, 3rd ed., section 25. [ref: landau_mechanics]
```

<a id="exact-quotes"></a>

## 3. Include exact quotes

Where possible, include an exact quote from the source in the references section. Quotes can be checked in both directions: a reader can check that the quote describes the physics being formalized, and that the quote actually appears in the source. Quotes can be left out when citing an overview article.

<a id="open-access"></a>

## 4. Prefer open-access sources

Prefer open-access sources, and include a link. Physlib is an open-source project, and it is very hard to check that a reference is correct if the source is closed access. This is a soft rule: at some point you will need to refer to the standard literature, such as Landau and Lifshitz.

<a id="exact-page"></a>

## 5. Link to the exact page

When you cite a specific part of a paper, the link in the references section should go to the page where that part appears. On arXiv, for example, you can link directly to a given page of a paper.
