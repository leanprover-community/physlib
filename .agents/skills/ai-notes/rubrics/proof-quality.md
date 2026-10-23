# Proof quality

You assess how proofs are written, not whether they are correct (the kernel owns soundness,
the correctness angle owns meaning).

- Prefer robust automation (`simp`, `fun_prop`, `ring`, `linarith`, `omega`, `grind`) over
  long chains of named-lemma rewriting, which break on Mathlib renames. A single explicit
  `simp only` or `rw` step is fine; the brittle chain is not.
- `change` and `show` deserve a comment saying why the goal cannot be reached otherwise.
  Prefer a rewrite to `rfl` or `convert` where one is available, and point out reliance on
  accidental definitional equality across wrappers or coercions; suggest an explicit lemma
  instead.
- Watch for short-but-brittle proofs: a `simpa` that closes a non-obvious goal through
  unfolding-heavy context is fragile even though it is terse.
- Proofs should generally be short (under 50 lines). Following the "Proof structure" section
  of `AGENTS.md`, suggest how a long proof could be split:
  - *by meaning*: further properties of existing definitions, `have`/`calc` steps with physics
    content or general mathematical value (an algebraic identity, an inequality, a
    differentiability side-goal), a general statement then instantiated, a part that uses only
    a weaker hypothesis, or a `let`/`set` object that deserves to be a `def` with lemmas;
  - *by structure*: substantial `rcases`/`match` branches, the base case and step of a long
    induction, a long `calc` block, or a symmetric half that follows by symmetry.

  When a long proof cannot be split, it should contain comments explaining its structure.
- Point out redundant hypotheses, and a `revert` the following proof does not justify.

## Score guidance

- 2–3 for long proofs with extractable reusable facts, proofs whose reason for working is
  obscured, or reliance on undocumented definitional equality.
- 5 when proofs are short, robust, free of undocumented defeq manipulation, and readable.
