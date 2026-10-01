# AGENTS file

## Introduction

- The human-facing policy and disclosure obligations are in [AI-POLICY.md](AI-POLICY.md); read it too.
- The human author must certify the code you write; the fact that it builds does not prove that what you have written is what the human author meant.
- Obey also [docs/ReviewGuidelines.md](docs/ReviewGuidelines.md).

## Content

- Use `lemma`, not `theorem`, unless the result is well known in the physics literature.
- Never use the `axiom` declaration.
- Never use `sorry`.
- Never use structure fields of type `True`, or theorems returning `True`.
- Never use an existential statement of the form `∃ x, ..., True` (any number of quantifiers ending in `True`).
- Never use a scope-level variable hypothesis that assumes the conclusion, or a statement that trivially entails it.
- Never include trailing white space.
- Make sure that hypotheses are distributed compactly and neatly over new lines, only include new lines when genuinely needed.
- Do not add lemmas that are trivial rewrites of existing Mathlib or Physlib results, unless they add genuine physics context.
- Place results in the appropriate existing file; do not create new files without good reason. For example, if you need to prove a general result about derivatives on space in order to prove something in classical mechanics, that result should go in `Space.Derivatives.Basic`, not the classical mechanics file.
- Include sections which are numbered by `# A. ...`, `## A.1. ...`. See [Physlib/ClassicalMechanics/HarmonicOscillator/Basic.lean](Physlib/ClassicalMechanics/HarmonicOscillator/Basic.lean) for an example.
- Every definition must have a docstring.
- Important lemmas should have a docstring.

## Proof structure

In general proofs of lemmas and theorems should be short (under 50 LOC).

Long proofs should be split into smaller lemmas. Where possible this should be done along one of the following directions.

**Extract by meaning** — the fragment says something independently true:

- The proof contains further properties about existing definitions. These properties should be extracted into their own lemmas.
- The proof contains `calc` or `have` statements which contain physics context, and may be generally applicable.
- The proof contains `have` statements with no physics content but general mathematical value (an algebraic identity, an inequality, a measurability/continuity/differentiability side-goal). These belong as general lemmas.
- The proof first establishes a general statement and then instantiates it. Extract the general statement and keep the specialization as a corollary.
- Part of the proof uses only the weaker form of a hypothesis (e.g. only continuity, not smoothness). Extract that part as a lemma stated under the weaker assumption.
- A `let`/`set` constructs an object and proves properties about it inline. Promote the object to a `def` and its properties to lemmas.

**Extract by structure** — the proof breaks into independent pieces:

- Substantial `rcases`/`match` branches. Each branch becomes its own lemma, and the main proof dispatches.
- The base case and inductive step of an induction, when long.
- A long `calc` block. A contiguous run of steps establishing a named equality can become its own equational lemma.
- Symmetry or duality, where half the proof mirrors the other (`≤` then `≥`, swapping two indices). Prove one direction as a lemma and obtain the other by symmetry.

Surface a recommendation when a condition above is met.

When a long proof cannot be split, make sure it contains comments.

## Before you finish

- Make sure all new files are imported into `Physlib.lean` or `PhyslibAlpha.lean` (keep sorted).
- Anything depending on `sorry` or `Lean.ofReduceBool` must be tagged `@[sorryful]` or `@[pseudo]`.
- New physics terms that trip the spell-checker go in `scripts/MetaPrograms/spellingWords.txt`.
- Check that `lake build` works (run `lake exe cache get` first).
- Check that `lake exe lint_all` passes.
- Check that `lake exe forMathlib_lint` passes: files in `Physlib/Mathematics/ForMathlib/` may only
  import from within that directory, and each must be used outside it.
- Check `./scripts/lint-style.sh`, but **commit your changes first**; this linter reads committed state.
- Check that `lake exe auxillary_script_test` passes (needs `Physlib`, `QuantumInfo` and
  `PhyslibAlpha` built).
- If edited a `PhyslibAlpha` file, check the following:
  - `lake exe runPhyslibAlphaLinters`
  - `lake exe noAlphaImports`
  - `lake exe alphaFileImports`
  - `./scripts/PhyslibAlpha/alphaPythonLinters.sh`

## PR scope

A PR should add a **single coherent concept**.

- Every definition and lemma should either *be* that concept or supply the minimal API to state and prove it.

## Commits

- Split a PR into atomic commits where it makes sense; keep commits focused.
- Commit titles must describe the lemmas or definitions added or changed.
- Include a [sign-off](https://git-scm.com/docs/SubmittingPatches.html#sign-off)-style
  `Co-authored-by: Claude Opus 4.8 <no-reply+claude-opus-4-8@anthropic.com>` trailer on commits you
  produced.

## PR descriptions

If you write the PR description:

- The PR description must list all lemmas and definitions added or removed, the file in which each appears, and a brief explanation of each.
- The PR description should include a reviewer map: a brief guide indicating the order in which the reviewer should look at the changes.
- The PR description must be concise.
