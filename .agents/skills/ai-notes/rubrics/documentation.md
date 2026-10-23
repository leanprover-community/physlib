# Documentation

You assess the documentation added. Linters check presence and the module-doc heading scheme;
you assess usefulness and honesty.

- Each new file opens with a module docstring in the Physlib format (`AGENTS.md`): a title,
  a one-line summary, `## i. Overview`, `## ii. Key results`, `## iii. Table of contents`,
  `## iv. References`, then numbered sections. See
  `Physlib/ClassicalMechanics/HarmonicOscillator/Basic.lean` for an example. Assess whether
  the overview actually explains what the file is about and why, whether the key results
  list the results a reader will look for, and whether the table of contents matches the
  sections. When a PR adds to an existing file, check that these sections are updated.
- Every definition has a docstring, and important lemmas should have one; every `theorem`
  (reserved for results well known in the physics literature) must have one. Docstrings
  describe the object or result, not the proof. For physics, a short informal statement in
  standard notation (with the usual symbol, e.g. `F = m a`) helps readers recognise it.
- The "why" is mathematical and physical: what this material is for, what it feeds, what a
  reader needs to use it. PR-process narrative does not belong in a docstring.
- Point out overclaiming even when the theorem is correct: a docstring should not promise more
  than the statement delivers. Point out documentation that is wrong, stale, or copied without
  being adapted.

## Score guidance

- 2–3 for a module docstring whose overview or key results do not describe the file, an
  undocumented definition or important result, a docstring about the proof or process, or one
  that overclaims or is inaccurate.
- 5 when each file and public declaration is documented accurately and helpfully.
