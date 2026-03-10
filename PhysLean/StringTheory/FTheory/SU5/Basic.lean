/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

/-!

# F-theory with a SU(5) gauge group

This module contains the details of F-theory with a SU(5) gauge group, with possible
additional charges. This should be compared to the directory:

- `PhysLean.Particles.SuperSymmetry.SU5`

which contains the details of the SUSY SU(5) gauge group not in F-theory. Many of the
results here use results from that directory.

## Data structures

The main data structures part of this theory are:
- `PotentialTerm`: An inductive type containing the terms in the super and
  Kahler potential of the theory. This can be found in
  `PhysLean.Particles.SuperSymmetry.SU5.Potential`, as not specific to F-theory.
- `Fluxes`: Contains the fluxes associated with each representation present in the theory.
- `Charges`: Contains the charges associated with each representation present in the theory.
  This can be found in `PhysLean.Particles.SuperSymmetry.SU5.Potential`, as not specific to
  F-theory.
- `Quanta`: Contains the fluxes and charges of each representation present in the theory.

## Propositions

There are a number of important propositions in the theory.
- `Charges.AllowsTerm`: For a given potential term, determines whether an element of `Charges`
  allows that term.
- `Charges.IsPhenoConstrained`: Is true when the charges permit a term that is phenomenologically
  constrained, such as the four-dimension proton decay coupling.
- `Fluxes.NoExotics`: Is true when the fluxes lead to no exotic particles.
- `Quanta.IsViable`: Is true when the quanta is phenomenologically viable, meaning it satisfies
  a number of conditions, such as anomaly cancellation, no exotic particles, and allowing the top
  Yukawa coupling.

The charges are additionally constrained by the configuration `CodimensionOneConfig`,
of the zero-section (`σ₀`) and the additional rational section (`σ₁`).
This is detailed in the paper `arxiv:1504.05593`. In implemented here using
- `Charges.ofFinset S5 S10`: which gives the finite set of charges where the 5-bar charges
  must live in the set `S5` and the 10-bar charges must live in the set `S10`.

## Important results

- `isViable_iff_mem_viableElems`: Enumerates all the viable `Quanta` for a given
  `CodimensionOneConfig`.

## References

This theory is looked at in the following paper:
- arXiv:1507.05961.

-/@[expose] public section
