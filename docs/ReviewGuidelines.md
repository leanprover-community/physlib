# Review guidelines

Below we give guidelines to what reviews of pull-requests (PRs) to Physlib are looking for.
This list is not exhaustive and reviews are within the judgement of the reviewer.

A good place to start for both authors and reviewers is:
- [What to consider when reviewing](https://leanprover-community.github.io/contribute/pr-review.html#what-to-consider-when-reviewing)


Note that your PR does not need to be perfect once you make it, we will work
with you to improve its quality, if you are also willing to work with us. Just do
your best. You should expect that about 50% of the work happens after you make your PR, this is normal
and it should not discourage you.

## Code quality

- Correct abstraction of lemmas and definitions.
- Correct use of type theory in definitions.
- Correct use of lemmas from Mathlib, e.g. not reproving things which are already proved.
- Concise proofs where possible.

In another programming language these points analogous to not just making sure you
have a function that does the right thing, but making sure that that function is
as efficient as possible, uses the best algorithm available etc.

## Organization

- Lemmas and definitions appear in the correct place
- Modules are easy to read and have a well-defined scope
- Any new correct files are suitably named.
- Any new correct files are suitably located.
- Modules have sufficient documentation to understand there flow.

These points are about navigability of the project as a whole and how easy it is to find results within the project.

## Style conventions

In addition to those here:

https://leanprover-community.github.io/contribute/style.html

- Use of `lemma` instead of `theorem` except for the most important results. These are listed
  in `scripts/lint/exemptions/Theorems.txt`, under a section for each library, which
  `lake exe theorem_lint` checks against the `theorem` keyword;
  it also checks that every `theorem` has a docstring.

These points are related to the readability of the project and results therein.

## PR and authorship

- The author of the PR understands the material in the PR.
- The PR is concise and adds a single new concept (which may be multiple lemmas or definitions)

These points are not to the code-base itself but the history of the project and how
easy it is for someone to find information on a given area from the git history.

## PR lengths

As a rule of thumb:

- < 50 lines = easy to check PR
- < 100 lines = average sized PR
- 100-200 lines = large PR, okay but try to break up if possible
- 200+ lines = very large PR, should be broken up into smaller pieces

There is no strict rule, as some very large PRs can be very simple e.g. documentation
or file reorganization and some small PRs can be very complicated e.g. adding definitions.

Remember, the reviewer needs to understand your PR and the more there is for them
to understand, the harder it is.

Small PRs are generally good because:

- Small changes can be merged faster and not get blocked by unrelated work
- Reduces the chance and impact of merge conflicts
- Easier for reviewers to understand

## Tag system

We operator a tag system with our PRs. This makes it easier for reviewers and authors to
understand where in the process PRs are.
- Please tag your PR with the appropriate `t-subject` tag.
- PRs marked as `draft` will not be reviewed.
- PRs marked with a `awaiting-author` tag will also not be reviewed until the author
  as addressed any reviewer comments and has removed this tag.
- If your PR is not getting reviewed and you would like to draw attention to it, please
  post [here](https://leanprover.zulipchat.com/#narrow/channel/479953-Physlib/topic/PR.20reviews/with/577663418).
- Once a PR is marked with a `ready-to-merge` the author does not need to do anything else,
  the maintainers will make sure it gets merged into the project.

## Claiming a PR for review

To keep track of PRs, reviewers can "claim" PRs and promise to review them within a certain timeframe. Failing to submit a review in that time will trigger a workflow which removes them and a Zulip bot notifies the community.

1. **Claim it.** Comment `claim` on the PR. The bot requests a review from you, assigns
   you, applies the `review-claimed` label and leaves a status comment recording the
   deadline. For a custom window, comment `claim 5 days` (hours, days and weeks all work)
   or `claim 2026-08-01`; `claim` uses the default of 2 days.
2. **You are reminded.** The bot @-mentions you 48 hours and then 24 hours before the
   deadline.
3. **It expires.** Claims carry a time to live (2 days by default, 14 days max) and are
   released automatically if they go stale, so nothing stays blocked forever. Comment
   `claim` again to extend, or `disclaim` to release early. Submitting a review completes
   the claim and clears the label.
4. **A missed claim is announced.** If the deadline passes with no review, you are removed
   as reviewer and assignee, and a message goes to the `PR reviews` topic on Zulip.
