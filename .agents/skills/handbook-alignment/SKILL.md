---
name: handbook-alignment
description: A check of a pull request or local changes based on how it aligns with the points mentioned in docs/ContributionHandbook/. For each file within the handbook, it scores the changes from 0 - 5 and provides constructive suggestions on how to get a better score.
---

# Handbook alignment check

Your goal is to measure how aligned changes made either locally or in a PR are to the rules and statements in `docs/ContributionHandbook/`. You, or your agents, will compare the changes with each of the files in `docs/ContributionHandbook/` and score the alignment out of 5, whilst also giving suggested improvements.

Importantly: You should not post anything without explicit human confirmation.

Below are the steps you should follow.

## Step 1: The setup

Firstly we have to decide two things. Firstly, what changes we need to check, and secondly, what files we need to check them against.

The request should either have a PR number e.g. `#1049` (we will use `#<N>` to describe a PR) or say `local`. If it does not, then you should ask the user for one.

It may also (optionally) have a list of handbook files e.g. `Basic, Naming, References`. If it does we will only run our test on these files. If no such list is provided, we will run it on all the files appearing in `./docs/ContributionHandbook/`.

Now we have to create a local copy of the repo for the changes.
Importantly, you should never `build` the project.

Create a new empty scratch directory, which we will call `WORK` below. For PR we will use a dedicated worktree:

```bash
git fetch https://github.com/leanprover-community/physlib.git "pull/<N>/head"
git worktree add --detach "$WORK/pr-<N>" FETCH_HEAD
gh pr view <N> --repo leanprover-community/physlib \
  --json number,title,body,author,baseRefName,headRefOid,files > "$WORK/pr-<N>.json"
gh pr diff <N> --repo leanprover-community/physlib > "$WORK/pr-<N>.diff"
```

In WORK this creates two files `pr-<N>.json` containing a summary of the PR information, and `pr-<N>.diff` containing the diff; along with the repo in `pr-<N>`.

If the changes are `local` you will use the repository directly instead of creating a copy of it in `WORK`. However, we will write the changes to `local.diff` and as well as any untracked files to `local-untracked.txt` in the `WORK` directory. This should be done using:

```bash
git fetch https://github.com/leanprover-community/physlib.git master
git diff "$(git merge-base HEAD FETCH_HEAD)" > "$WORK/local.diff"
git ls-files --others --exclude-standard > "$WORK/local-untracked.txt"
```

You should also determine where a copy of Mathlib is. Use a checkout where there is a `.lake/packages/mathlib` folder (usually the directory this skill was called from). Do not make your own at any point. If there is a disagreement in the Mathlib version between the one found and the one needed for the changes, let the user know. Again, do not make or download your own copy.

## Step 2: Running the alignment tests

We now want to run the alignment task for each selected handbook file `docs/ContributionHandbook/<name>.md`. To do this:

1. Create a prompt for each pass using:
  - The text in `.agents/skills/handbook-alignment/protocol.md`
  - The text in the handbook file `docs/ContributionHandbook/<name>.md`.
  - the paths of the checkout of the changes, of `.lake/packages/mathlib`, of the description (for a PR), the untracked files (for a local change), and of the diff.
  - the instruction: "When you are done, output the JSON
     object described in the shared protocol, and nothing after it."
2. Save the json object to the file `$WORK/raw-Outputs/<name>.json`.

If you can create independent subagents or do tasks in parallel, do so for each file.


## Step 3: Creating the report

We now need to create the report. Run:
```
python3 .agents/skills/handbook-alignment/report.py "$WORK/raw-Outputs" > "$WORK/report.md"
```

Show the report to the user. For local changes, stop here.

For a pull request, first look for an earlier report on the PR by the same user. Every report
starts with the hidden line `<!-- handbook-alignment-report -->`. Find the user's GitHub name,
then the ids of their comments on the PR that start with that line:

```bash
gh api user --jq .login
gh api "repos/leanprover-community/physlib/issues/<N>/comments" --paginate \
  --jq '.[] | select(.user.login == "<login>" and (.body | startswith("<!-- handbook-alignment-report -->"))) | .id'
```

If there are several, use the last (the newest). Only ever update the user's own comments,
never a report by someone else.

Then give the user three choices, saying which one "Post" will do:

- **Post**: if there is an earlier report, replace it:

  ```bash
  gh api -X PATCH "repos/leanprover-community/physlib/issues/comments/<id>" \
    -F "body=@$WORK/report.md"
  ```

  Otherwise, add a new comment:

  ```bash
  gh pr comment <N> --repo leanprover-community/physlib --body-file "$WORK/report.md"
  ```

- **Copy**: print the contents of `$WORK/report.md` so the user can post it themselves.
- **Neither**: do nothing.

Only post after the user has explicitly chosen "Post".


## Step 4: Clean up

Clean up any of the files created, for example:
```bash
git worktree remove --force "$WORK/pr-<N>"
```
