# Physical relevance

Physlib is a library of physics. Not everything that is mathematically provable is physically
relevant: a correct theorem about a well-formed definition can still fail to say anything a
physicist would recognise or use. Your angle is whether the PR connects to physics, and how
clearly it shows that connection. `docs/ReviewChecklist.md` (Level 1) asks: is the content
physics, and is it mainstream physics?

Faithfulness of the formal statements is the correctness angle; the right level of
mathematical generality is the generality angle. Judge the physics.

## What to look for

- **Physical objects.** Do new definitions correspond to recognised physical concepts or
  quantities (a field, an observable, a state, an energy, a symmetry, a conserved current)?
  A definition that has no physical counterpart and is not needed for one is worth
  questioning.
- **Physical statements.** Are the results statements a physicist would recognise or use: a
  law, an identity, a conservation law, a limit, a standard textbook result, a property of a
  model? Or are they mathematical facts with no stated bearing on the physics?
- **Physically meaningful hypotheses.** Do the assumptions correspond to physical conditions
  (positivity of mass or temperature, a bounded potential, a timelike vector, a closed system)?
  Point out artificial conditions added only to make a proof go through, and conditions that
  exclude the physically interesting cases (e.g. a result about oscillators that excludes
  every frequency of interest, or about fields that holds only when they vanish).
- **Mainstream physics.** Is the material part of established physics, with a standard
  reference (a textbook, a review, a well-known paper)? Speculative or idiosyncratic models
  deserve a clear statement of where they come from.
- **Supporting mathematics.** Material in `Physlib/Mathematics/`, `Physlib/SpaceAndTime/` or
  general API files does not need to be physics itself. Assess instead whether its physics use
  is clear: is there a consumer in the PR or on `master`, or a stated physics application? Do
  not lower the score just because supporting mathematics is mathematics.
- **Presentation.** Does the PR make the physics visible: a docstring with the informal
  physical statement in standard notation, a physically motivated special case, an example
  connecting the abstract result to a familiar system?

## Suggestions to make

Constructive suggestions here are typically: add the informal physical statement to a
docstring; state the physically relevant special case as a corollary; replace an artificial
hypothesis by its physical counterpart; add a reference; add an example or consumer showing
the physics use; or, for material with no physics connection, explain where it is needed or
move it to a more appropriate library.

## Score guidance

- 0–1 when the PR's main content has no evident connection to physics and none is stated.
- 2–3 when the physics is there but obscured: artificial hypotheses, no informal statement, or
  supporting mathematics with no stated physics use.
- 5 when the physics is evident: recognised objects, physically meaningful hypotheses, and
  statements a physicist would use, clearly presented.
