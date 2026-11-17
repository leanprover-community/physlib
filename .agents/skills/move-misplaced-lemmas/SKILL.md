# .agents/skills/move-misplaced-lemmas/SKILL.md

````markdown
---
name: move-misplaced-lemmas
description: Find lemmas in PhyslibAlpha that do not use the definitions of their own file or section, move each next to the definitions it depends on, and check that everything still builds. Use it when someone asks to find misplaced, misfiled or out-of-place lemmas, relocate results, or tidy where things live in PhyslibAlpha, even if they never say "misplaced".
---

# Move misplaced lemmas

You will find lemmas in PhyslibAlpha that sit in the wrong place and move each one to where it belongs, next to the definitions it actually depends on. The user can give a number of lemmas to move, five if they give none, and can point you at a file or folder; otherwise you search all of PhyslibAlpha. At the end the user has the lemmas moved in place, with the checks run, ready for them to review.

## Ground rules

- Keep the meaning. Every lemma must state the same thing after you move it as before.
- You may rename a lemma and fix its namespace where the move makes that necessary. When you do, update every use across the repository. Do not leave deprecated aliases under the old names.
- Move all the lemmas first, and run the checks only once, at the very end (Step 5), because building is slow.

## Step 1: The setup

Your goal is to know how many lemmas to move and where to look. Take the number from the request, or use five if none is given. If the request names a file or folder, search only there; otherwise search all of `PhyslibAlpha/`.

## Step 2: Find misplaced lemmas

Your goal is a list of lemmas, up to the number from Step 1, that belong somewhere else. A lemma is likely misplaced when it does not use the definitions made in its own file or in its own section, and is really about something more fundamental than what the file is about.

## Step 3: Decide where each lemma belongs

Your goal is a destination for each lemma. Look at the definitions it does depend on and find where they live; that tells you where the lemma should go.

- If those definitions live in PhyslibAlpha, move the lemma to the file that defines them.
- If they live in Physlib, move it to the PhyslibAlpha file that corresponds to that Physlib file, creating that file if it does not exist yet.
- If they live only in Mathlib, move it to the folder in `PhyslibAlpha/Mathematics/ForMathlib/` that mirrors where those definitions live in Mathlib.

## Step 4: Move the lemmas

Your goal is every lemma in its new home, with nothing left broken by the move. Move each lemma, renaming it and fixing its namespace where needed, and update every use. Place it in the section of its new file where it fits. Add any new file to `PhyslibAlpha.lean` (keeping it sorted) and fix the imports of every affected file.

## Step 5: Check everything still runs

Your goal is a repository that works after all the moves. Run these once all lemmas are moved, fixing anything they report and rerunning:

```bash
lake exe runPhyslibAlphaLinters
lake exe noAlphaImports
lake exe alphaFileImports
./scripts/lint/required/alpha/alphaPythonLinters.sh
```

Then, at the very end, build the project:

```bash
lake exe get_cache
lake build
```

## Step 6: Hand back the changes for review

Your goal is for the user to review the moves quickly. For each lemma, tell them where it was, where it went and why, and any rename. Report the actual results of the linters and the build. The user checks that each lemma now lives in the right place and still means what it did.
````
