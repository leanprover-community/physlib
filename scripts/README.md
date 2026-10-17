# Scripts

The scripts are grouped by purpose:

- `lint/required/` : linters run by CI on every pull-request; a PR cannot be merged until they
  pass. The `alpha/` subfolder holds those specific to PhyslibAlpha, see
  [lint/required/alpha/README.md](lint/required/alpha/README.md).
- `lint/optional/` : linters which are useful to run locally but are not enforced by CI.
- `lint/exemptions/` : data files read by the linters, such as exemption lists and the
  spelling word list.
- `website/` : scripts which generate the data and pages for the Physlib website.
- `github/` : scripts run by GitHub workflows and bots.
- `dev/` : tools for local development and maintenance.

# Linting Physlib

`Linting` is the process of checking changes to the project
for certain types of stylistic errors. This process is carried out
by automatic scripts called `linters`.

Physlib has a number of linters which check for various different things.
They can all be run on your local version of the project, but some of them
are also automatically run on pull-requests to Physlib. These latter linters
must be passed before the pull-request can be merged with the main branch of the
project.

Below we summarize the linters Physlib has, in each bullet point the initial `code snippet`
is how the linter can be run locally.

The first three linters are the most important, but in an ideal world you would check that
all of the following linters run correctly.

- `lake exe lint_all` (**A PR must in general pass this linter**): This linter is split into eight steps, strictly speaking not all of these steps must be past for a PR to be merged, but it is best to just fix them all.
  - step 1: This checks for basic style mistakes such as double spaces and string combinations like `):`
  - step 2: This builds the project
  - step 3: Checks all files are imported to `Physlib.lean`.
  - step 4: Checks that no tags on TODO items are duplicates of one another.
  - step 5: Checks that all lemmas and definitions dependent on `sorry` or `Lean.ofReduceBool` are correctly attributed with `@[sorryful]` or `@[pseudo]`
  - step 6: Checks that module documentation is laid out according to the set standard (see `lake exe module_doc_lint` below).
  - step 7: Checks all Lean linters run without error, this picks up things like lack of doc-strings on definitions, or incompatible `@[simp]` attributes
  - step 8: Checks there are not transitive imports, e.g. A imports B and C, but B already
  imports C.
This linter may need running a number of times.
- `./scripts/lint/required/lint-style.sh` (**A PR must pass this linter**): This linter checks for some
  style errors e.g. too long lines or wrong indentations, as well as checking if all necessary `simp` lemmas are of the form `simp only [...]`. For this linter
  to work properly you must first commit your changes to github.
- `lake exe auxillary_script_test` (**A PR must pass this linter**): Runs and checks the auxiliary
  scripts `lake exe make_tag`, `lake exe TODO_to_yml mkFile`, `lake exe stats mkHTML` and
  `lake exe informal mkFile mkDot mkHTML`, which generate the website data. `TODO_to_yml` imports
  `Physlib`, `QuantumInfo` and `PhyslibAlpha` together, so this also catches declarations with the
  same name in two of these libraries. It needs all three libraries built
  (`lake build Physlib QuantumInfo PhyslibAlpha`), and it leaves no files behind.
- `lake exe style_lint` : A linter which only does step 1 of `lake exe lint_all`.
- `lake exe runPhyslibLinters` : A linter which only does step 7 of `lake exe lint_all`.
- `lake exe module_doc_lint` (**A PR must pass this linter**): Step 6 of `lake exe lint_all`. Checks that the module
  documentation (the `/-! … -/` blocks) of every file in `Physlib`, `QuantumInfo` and
  `PhyslibAlpha` is laid out according to a set standard. It reads the source files directly,
  so it does not need the project to be built. The headings of a file must be:
  - a title `# …`, usually followed by a one-line summary of the file;
  - `## i. Overview`, `## ii. Key results`, `## iii. Table of contents` and `## iv. References`,
    in that order;
  - sections and subsections tagged as `## A.`, `### A.1.`, `#### A.1.2.` etc., listed in the
    table of contents as `- A. …`, `  - A.1. …`, `    - A.1.2. …`.

  No heading may end in a full stop. Errors are grouped by kind, each with a file and line number.
  Files in `./scripts/lint/exemptions/module_doc_no_lint.txt` are not checked; new files must not be
  added to this list, and slowly we will empty it.
- `lake exe spelling` : Checks the spelling of words in Physlib against a given list
  of correctly spelled words which can be found in `./scripts/lint/exemptions/spellingWords.txt`

## Checking golf pull requests

- `scripts/github/check_golf.py` : Verifies that a pull request only *golfs* proofs, i.e.
  that no declaration statement (its signature/type) changed and only proofs and
  definition bodies changed. Comment `/check-golf` on a PR to run it via the
  [`check-golf`](../.github/workflows/check-golf.yml) workflow; the bot posts its
  findings as a single PR comment and edits that same comment on subsequent runs.
  To run it locally against two revisions:

  ```
  scripts/github/check_golf.py --base <merge-base> --head <head-sha>
  ```

  It parses the changed Lean files textually (no build required): comments and
  whitespace are ignored, and `by` proof terms embedded inside a type are treated
  as proofs (proof-irrelevant). Anonymous instances and `example`s are not tracked.
  It also breaks the golfs down by trivial shape: proofs where only a newline was
  removed, and proofs where tactics were joined onto one line with a `;`.

  With `--measure` it also reports the **compile cost** of the golf: for each
  changed file it compiles the base and head versions and diffs their heartbeats
  (via Mathlib's `#count_heartbeats`) and wall-clock time. This needs a built
  project, so the workflow runs `lake build` on the head revision first:

  ```
  lake exe cache get && lake build
  scripts/github/check_golf.py --base <merge-base> --head <head-sha> --measure
  ```

## Summarising a pull request

- `lake exe pr_summary` : Summarises a pull request for its reviewers, as Markdown: the files it
  adds, removes, renames or modifies, with the number of lines added to and removed from each, and
  the declarations it adds, removes, moves between files or restates. The
  [`PRMessage`](../.github/workflows/PRMessage.yml) workflow runs it on every new PR, and again on
  every push to one, and posts the result, under *Summary of your PR for reviewers*, in the
  comment it leaves; the rest of that comment is
  [`.github/PRMessage.md`](../.github/PRMessage.md), whose `<!-- PR_SUMMARY -->` marker the
  summary replaces. A push updates that comment in place rather than leaving a second one: the
  workflow finds it again by the `<!-- physlib-pr-summary -->` marker which is its first line, so
  that marker must stay first.

  Each file and each declaration is a link into `leanprover-community/physlib`, at the line it
  is on, in whichever of the two revisions it belongs to, so a reviewer can jump from the table
  to the code. It also calls out the results the PR writes with `theorem`, since each one needs
  a doc-string and a line in `scripts/lint/exemptions/Theorems.txt`.

  To run it locally, with `origin/master...HEAD` by default:

  ```
  lake exe pr_summary
  lake exe pr_summary <base>
  lake exe pr_summary <base> <head>
  ```

  The Markdown goes to standard output and the progress messages to standard error, so
  `lake exe pr_summary > summary.md` writes just the summary. The declarations are found by
  reading `git diff --unified=0` as text, in the spirit of the `declarations_diff.sh` script of
  [`mathlib-ci`](https://github.com/leanprover-community/mathlib-ci), so no build is needed; the
  module documentation of `scripts/alpha/github/pr_summary.lean` lists what that misses, and gives
  examples to run on recent PRs. Its tests are `#guard_msgs` commands in its source, so
  `lake build pr_summary` runs them.
