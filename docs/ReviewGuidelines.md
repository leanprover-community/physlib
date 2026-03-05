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

## Organization

- Lemmas and definitions appear in the correct place
- Modules are easy to read and have a well-defined scope
- Any new correct files are suitably named.
- Any new correct files are suitably located.
- Modules have sufficent documentation to understand there flow.

These points are about readability of the project as a whole and how easy it is to find results within the project.

## Style conventions

- Use less-then rather than greater-then.
- No new lines in proofs.
- Good use of `variables`.

These points are related to how individual lemmas and theorems look, and how easy they are
to read.
