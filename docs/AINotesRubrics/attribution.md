# Attribution

Does the PR credit what it drew on?

- Credit sources proactively. Formal: vendored Mathlib PR material, copied or closely adapted
  formalizations, and the central declarations a construction follows (not every Mathlib
  dependency, which every proof has). Informal: the paper, textbook, lecture notes, or Zulip
  discussion the work follows. Physics results usually have a standard textbook or paper
  reference; suggest one where a reader would expect it.
- Physlib keeps references in `docs/references.bib` and cites them in the module docstring's
  `## iv. References` section. Suggest adding a missing entry there.
- Check the diff against its stated sources, and watch for close following without credit:
  similarity in theorem order, notation, or proof plan to an identifiable source is enough to
  suggest credit, even with no text copied.
- Do not invent attribution requirements for routine work that draws on nothing in
  particular; give `null` when the PR draws on no source.
- Bibliographic correctness (that a work exists, that page numbers are right) is the author's
  responsibility under `AI-POLICY.md` §2.1. You may point out a reference that looks
  implausible, but do not certify references.

## Score guidance

- 0–1 when the PR vendors or closely follows identifiable existing work (a Mathlib PR, a
  paper, a prior formalization) with no credit.
- 2–3 when a central, non-obvious source is named in the description but not the code, or is
  clearly followed but unnamed.
- 5 when the work credits its central formal and informal sources.
