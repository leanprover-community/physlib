# Review guidelines

Below we give guidelines to what reviews of pull-requests to PhysLib are looking for.
This list is not exhaustive and reviews are within the judgement of the reviewer.

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

- Use of `lemma` instead of `theorem` except for the most important results.

These points are related to the readability of the project and results therein.
## PR and authorship

- The author of the PR understands the material in the PR.
- The PR is concise and adds a single new concept (which may be multiple lemmas or definitions)

These points are not to the code-base itself but the history of the project and how
easy it is for someone to find information on a given area from the git history.
