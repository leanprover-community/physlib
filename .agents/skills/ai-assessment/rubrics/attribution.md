# Attribution

Does the PR credit what it drew on? Uses `request_changes`, and may `block` when required
credit is clearly absent.

- Credit sources proactively. Formal: vendored Mathlib PR material, copied or closely adapted
  formalizations, and the central declarations a construction follows (not every Mathlib
  dependency, which every proof has). Informal: the paper, textbook, blueprint, notes, or
  Zulip discussion the work follows.
- Check the diff against its stated sources, and watch for laundering: similarity in theorem
  order, notation, or proof plan to an identifiable source is enough to require credit, even
  with no text copied.
- Do not invent attribution requirements for routine work that draws on nothing in
  particular.
- Do not credit the project's own roadmap (`TauCetiRoadmap`) in the file. Only credit it in
  the PR description, in the mandatory `Roadmap: <name>` line.

## Verdict

- `block` when the PR vendors or closely follows identifiable existing work (a Mathlib PR, a
  paper, a prior formalization) with no credit.
- `request_changes` when a central, non-obvious source is named in the description but not the
  code, or is clearly followed but unnamed (except the project's roadmap, which must be credited only in the PR description).
- `approve` when the work credits its central formal and informal sources.
