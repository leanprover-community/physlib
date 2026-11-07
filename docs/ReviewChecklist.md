# Review checklist

This is a review checklist for Lean content going into ./Physlib or ./QuantumInfo.
It does not cover meta-programs, only standard additions of definitions and lemmas to Lean.

This should not be taken as a definitive guide, as every PR will be different.

There is some subjectivity in reviewing PRs, so instead of framing this in terms of hard-set rules,
this review check list is framed in terms of questions a reviewer might want to ask themsevles
when reviewing a PR.

## Level 1: Subject area

- Is the content added physics?
- Is the content added mainstream physics?

## Level 2: Organisation

- For every definition and lemma added in the PR, could I determine from the file-structure only
  where I would find that result?
- Does every definition and lemma added in the PR fit the theme of the rest of the file, or
  does it fit more appropriately elsewhere?
- If there are new files made, can I guess the content of that file from the name?
- Within a given file, can I understand the relevance of results which sit next to each other,
  or in the same section?

## Level 3: Content

- Is a definition or lemma a simple rewrite of a result already in Mathlib or Physlib?
- Does the PR reuse Physlib's physical constants and units, instead of defining its own or
  writing out their numerical values?
- Do the definitions added look generally useful, do they appear in physics, or
  do they allow you to ask interesting questions about a data-structure that exists?
- Are lemma statements and definition terms easy to read?
- Do lemmas seem like they will be useful, and are written in a reusable way?
- Are the hypotheses of the lemma minimal and necessary?
- Do any of the have statements inside the proof contain general mathematical identities or
  physical context that should be extracted into their own standalone lemmas?

## Level 4: Naming and documentation

- Are the names written in Mathlib/Physlib convention?
- From the name of a declaration can you guess what the declaration is without looking at it?
- Are the namespaces correct and make sense?
- Does the module documentation actually help either with the flow of the document or one
  understand what is in the file, or is it just padding?
- Does documentation on declarations help one understand what that declaration does?

## Level 5:

- Does the code look neat and clean, or is it difficult to read?
- Are there any newlines in proofs?
