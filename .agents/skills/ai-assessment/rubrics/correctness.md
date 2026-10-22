# Correctness and faithfulness

Your angle is semantic faithfulness: green proofs can still state the wrong theorem. The kernel
checks proofs and CI checks for `sorry` and axioms; neither tells you whether a definition
captures the intended mathematical or physical object, or a theorem states the intended result.

Probe every definition and statement: try to show it is wrong, vacuous, or weaker than it
claims. Score highly only once you have tried and failed.

## What to look for

- Mis-formalization: the statement does not match the mathematics or the physics. Check
  quantifiers, the direction of implications, the objects, units and sign conventions, and
  edge cases (empty, zero, degenerate, massless, the trivial metric, a vanishing field).
- A statement whose hypotheses are too weak for the claim, or whose real content has been
  moved into its assumptions. Check whether a new structure turns downstream theorems into
  assumptions rather than consequences, and whether a hypothesis assumes the conclusion or
  trivially entails it (`AGENTS.md`).
- Vacuity and tautology: a statement that holds trivially, a definition defeq to `True` or to
  its own restatement, or a "definition" that relocates the difficulty instead of discharging
  it. Trivial-but-true is **not** your concern: a simple correct lemma is faithful. Whether
  material is worth having belongs to the scope and physical-relevance angles; look for
  vacuity in the logical sense (a `True`-typed or vacuously-quantified claim, an existential
  of the form `∃ x, ..., True`, content moved into hypotheses), not mere simplicity.
- Placeholders: `True` or any trivial stand-in in a signature or as a structure-field type,
  including a field given a plausible physical name that is really an assumption.
- An unexercised predicate: a new `Prop`-valued definition, class, or hypothesis structure with
  neither a consuming theorem nor a nontrivial witness (a concrete instance where it holds
  non-degenerately) in this PR or already on `master`. Until one exists its faithfulness cannot
  be checked; suggest adding the witness or consumer.
- Over-strong typeclass or structural assumptions that quietly narrow the claim.

## Missing prerequisites

If the PR needs something that does not exist and works around it (assumes it, bundles it as a
hypothesis, or substitutes a weaker stand-in), say so and suggest building the real
prerequisite first, as its own PR.

## Score guidance

- 0–1 when a central statement or definition does not say what it is meant to, or a missing
  prerequisite has been assumed. Name the statement, the suspected mismatch, and the check
  that failed to resolve it.
- 5 only once you have tried to break every new statement and definition and failed.
