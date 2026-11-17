---

name: guided-review
description: Walks a reviewer through a Physlib PR step by step, whether it changes Lean code or infrastructure such as scripts, linters, CI, documentation or skills, pointing out where to look so they can write their own comments. Use it when someone wants help reviewing a PR, even if they only say "help me review PR 1234" or "take me through this PR".

---

# Guided PR review

This skill guides a reviewer, newcomer or expert, through a Physlib PR in a fixed order. They give you a PR number. At each step you show them where to look and what is worth their attention; they make every judgment and write every comment themselves. Let the reviewer know that anyone is welcome to review, and that a review covering only some of these steps is still valuable, so they can stop whenever they like.

## Ground rules

- Do not write, draft or edit review comments. Guide the reviewer to what to look at and leave the wording to them. All communication with PR authors must be human, as `AI-POLICY.md` requires.
- Everything is the reviewer's call. Point things out and ask questions; do not give verdicts.
- Stay on the reviewer's machine. Never post, push, comment or approve anything on GitHub.
- Do not build the project; this review does not need it, and it takes hours.

## Step 1: Get the PR

The goal is to have the PR's description and changes in front of you. If the request has no PR number, which we call `<N>`, ask the reviewer for one.

Read the description and the diff:

```bash
gh pr view <N> --repo leanprover-community/physlib --json title,body,author,files
```

```bash
gh pr diff <N> --repo leanprover-community/physlib
```

If the diff is not enough to follow the code, check the PR out locally as a fallback, in a scratch directory we call `$WORK`:

```bash
git fetch https://github.com/leanprover-community/physlib.git "pull/<N>/head"
git worktree add --detach "$WORK/pr-<N>" FETCH_HEAD
```

Go through the steps below one at a time, pausing after each for the reviewer to think and make notes. At each step, present what you found clearly: a short summary first, then the details, grouped in a way that is easy to scan (for example, files by folder). Flag what seems worth a look and leave every decision to the reviewer.

From the changed files, decide whether the PR is a Lean code PR or an infrastructure PR (scripts, linters, CI, documentation such as the Contribution Handbook, and skills), and tell the reviewer which. Use Part A for Lean code and Part B for infrastructure. A PR is rarely both; if it is, point this out to the reviewer and ask which part to follow.

## Part A: Lean code (Steps 2 to 11)

Use these steps for changes to Lean files.

### Step 2: Read the description

The goal is a description that is concise and readable by a human. Show the reviewer the description and point out anything long, vague or hard to follow, since this is the first thing worth raising.

### Step 3: Look at the changed files as a whole

The goal is to see whether the files changed, taken together, point to one coherent PR. List them for the reviewer and note any that seem out of place.

### Step 4: Read the module documentation and API maps

The goal is documentation whose physics is correct and which a reader can understand. Take the reviewer through new or changed module documentation and API map additions. Flag places where the text might rely on background reading that is not there.

### Step 5: Check the references

The goal is to give the reviewer every reference so they can check it. List each one added, together with what it supports in the file: the definition, result or passage it is cited for. Do not judge them yourself: `AI-POLICY.md` says only a human can verify references.

### Step 6: Look at the shape of each Lean file

The goal is files built around the key data structure for their area of physics. For each file, help the reviewer see whether a definition comes first and the later results depend on it, and whether it uses the established data structures of that area rather than inventing its own.

### Step 7: Look at the types and connections of the lemmas

The goal is results that use the right structures and fit together. Point out where a lemma might use a general type in place of the proper one, for example `ℝ` where `Time` belongs, and where results seem disconnected or inconsistent. Also flag any lemma that does not seem to belong to this API, or that looks as if it belongs in another file.

### Step 8: Check where each lemma sits

The goal is each lemma in the right section of its file. Show the reviewer the file's sections and where each new lemma landed.

### Step 9: Read the docstrings of new results

The goal is that each new result says clearly what it does. For each one, help the reviewer check that its docstring is concise and understandable, makes plain what the lemma is doing, and fits the overall story of the PR.

### Step 10: Check the names

The goal is lemma and definition names that are easy to understand and sit in the right namespace. Go through the new names with the reviewer and flag any that are unclear or seem to be in the wrong namespace.

### Step 11: Read the proofs

The goal is proofs that are concise, clear, sensible and easy to follow. Take the reviewer through each proof and point out any that are long or hard to follow.

## Part B: Infrastructure (Steps 12 to 17)

Use these steps for changes to scripts, linters, CI, documentation such as the Contribution Handbook, and skills.

### Step 12: Ask whether the change is needed

The goal is an infrastructure change that earns its place. Help the reviewer see whether it fixes a real problem, and whether something already in the repository does the same job.

### Step 13: Check it reads clearly at a broad level

The goal is a change a human can read and understand. Help the reviewer see whether it is clear what role each added file plays.

### Step 14: Check the overall design

The goal is a design the reviewer could explain. Help them see whether the overall pattern the change follows is clear, so they could say how the whole thing works.

### Step 15: Check related documentation

The goal is documentation that stays in step with the change. Flag any documentation that depends on or relates to the change and has not been updated.

### Step 16: Check each piece

The goal is that each added piece, such as a function, script or section, makes clear what it does. Go through them with the reviewer and flag any that are unclear.

### Step 17: Check it works

The goal is a change that does what it is meant to do. Where there is something to run, such as a script or linter, offer to test it, say what the test would show, and run it only once the reviewer agrees, since this runs code from the PR on their machine. Either way, explain how the reviewer could test it themselves. For documentation this step usually does not apply.

## Step 18: Hand back to the reviewer

The goal is a reviewer ready to write their own review. Remind them of the places they marked along the way, without writing comments for them. Ask how they would like to give their review, then guide them in doing it: for example, how to leave a comment on a specific line of a PR on GitHub, and how to add a suggested change. Writing and posting the review is theirs. If you checked the PR out, remove the worktree:

```bash
git worktree remove --force "$WORK/pr-<N>"
```
