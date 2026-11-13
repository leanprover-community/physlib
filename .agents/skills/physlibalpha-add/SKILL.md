---
name: physlibalpha-add
description:  Add a single result or definition to PhyslibAlpha, starting from its statement and ending with the project edited, committed in small atomic commits, and a diff for the human to review. Use this whenever someone wants to formalize, add, prove or contribute a physics result, lemma or definition to PhyslibAlpha, even if they never say "PhyslibAlpha".
---

# Add a result to PhyslibAlpha

Help a contributor, new or regular, add a single result or definition to PhyslibAlpha. They give you its statement (maybe as an input X); you check it suits the project, build whatever it needs in PhyslibAlpha, write it, check it and commit it. They get back the edited project and a diff to review.

## Ground rules

- Think about generality and placement, not only the target. Newcomers tend to focus on the specific thing they want to prove, which is not the way to build a library; decide where each piece belongs and state it at the right level of generality.
- Only ever edit PhyslibAlpha. Never touch Physlib.
- Never use the `theorem` keyword.
- Never add references you are not sure about.
- Refuse anything that is not mainstream research physics (see Step 1).
- Commit in small, atomic, logically independent commits with easy-to-follow, standardized names.
- Never push. Pushing is entirely up to the person.

Follow `AGENTS.md` throughout, and read the files in `docs/ContributionHandbook/` while writing so the change aligns with them.

## Step 1: Check the result suits Physlib

Decide whether the result belongs in the project at all. Use your own judgment: it is fine if it is in a standard undergraduate physics course, or is the kind of thing that appears in a normal physics journal or on the arXiv. If it is non-mainstream physics, or away from what academics normally work on, stop and refuse. If you are unsure, do not ask the person; refuse.

## Step 2: Check for missing core definitions

Work out whether any core definitions are missing that would be useful as general concepts in the project. Look in Physlib and PhyslibAlpha. Any missing definitions you add go in PhyslibAlpha. If infrastructure is missing, build it in this same run.

## Step 3: Find what the project already has to build on

Find the existing definitions and results you can use to derive the target. Search all relevant areas of the library. Whenever you think you will need a concept, first check whether it already exists. Never reproduce mathematical results from Mathlib unless they have important physics context.

## Step 4: Plan, working backwards from the target

Take the target, whether a definition or a lemma, and work out what needs to go into it, then move step by step further back. For each new piece, decide where it goes in the library, keeping to the handbook: only physics results, everything readable. Carry straight on to writing; do not wait for approval of the plan.

## Step 5: Write it

Write the definitions and lemmas, building the files you edit as you go. If a proof is hard, try and try again; these proofs can almost always be filled in. If you really cannot do it, stop and report back to the person with the error, and ask them whether to reduce the scope.

## Step 6: Review what you wrote

Go back over every definition, lemma and result. Make sure each is in the right place, has the right name, and does not reproduce anything already in the project.

## Step 7: Run the checks

Run the checks in the "Before you finish" section of `AGENTS.md`. Do this only once, right at the end, just before handing back, but always do it. Run `lake exe cache get` first so you do not have to build everything.

## Step 8: Hand back the diff

Give the person the diff of your commits. Tell them that they need to open the PR themselves, and write a short, human-written and human-readable description for it.
