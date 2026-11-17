---
name: physlibalpha-align-with-handbook
description: Edits local changes, or a file or small folder of PhyslibAlpha, so that it follows docs/ContributionHandbook/, choosing the worst-designed area of PhyslibAlpha itself if there are no local changes. Use it when someone wants to tidy up, clean up or improve their code or an area of PhyslibAlpha.
---

# Fix code to follow the Contribution Handbook

You will improve a piece of Physlib so that it follows the rules in `docs/ContributionHandbook/`. The piece is either the local changes, a file or small folder in `PhyslibAlpha/` that the user names, or one you choose yourself. At the end the user has edited files to review. Nothing is committed.

## Ground rules

- Do not commit, push or post anything. The user reviews the edited files themselves.
- Keep your edits inside the chosen area, and do not change what any statement means physically, unless that is truly necessary. For example, you may move a lemma to the file where it belongs.
- Follow `AGENTS.md` and `AI-POLICY.md` throughout.

## Step 1: Choose the area

Your goal is to decide which code you will improve.

If the user names a file or folder, use that. Otherwise check for local changes, meaning everything that differs from master, whether committed or not. Make an empty scratch folder, called `$WORK` below, and run:

```bash
git fetch https://github.com/leanprover-community/physlib.git master
git diff "$(git merge-base HEAD FETCH_HEAD)" > "$WORK/local.diff"
git ls-files --others --exclude-standard > "$WORK/local-untracked.txt"
```

If there are local changes, the area is the changed and untracked files.

If there are none, choose the file or small folder in `PhyslibAlpha/` that you think is most badly designed when measured against the handbook. Tell the user what you chose and why, then carry on without waiting for them.

## Step 2: Find the improvements

Your goal is a list of the changes the handbook calls for.

For each file `docs/ContributionHandbook/<name>.md`, review the area using the protocol in `.agents/skills/handbook-alignment/protocol.md`, with the area in place of a diff. You only need the `improvements` from that protocol. Leave out the score and summary. If you can run subagents in parallel, run one per handbook file.

## Step 3: Make the edits

Your goal is to apply the improvements from Step 2.

Work through the improvements, keeping to the ground rules. Where two suggestions conflict, or one would change the physics meaning, leave it out and note it for the user.

## Step 4: Check the work

Your goal is to confirm that the edited code still builds and passes the linters. Do this only once all the edits are made, because building is slow.

```bash
lake exe cache get
lake build
```

Then run the checks in the "Before you finish" section of `AGENTS.md` that apply, including the PhyslibAlpha linters if you edited a `PhyslibAlpha` file. Fix what fails and run the checks again. Report a check that you could not run as not run, never as passed.

## Step 5: Hand back the edits

Your goal is to give the user everything they need to review the edited files.

Do not commit anything. Tell the user which files you changed, what each change does and which handbook file it comes from, any edits outside the area and why you made them, any suggestions you left out, and the check results. The user checks the physics and the references, and writes any PR description themselves.
