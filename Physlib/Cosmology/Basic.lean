/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

/-!

# Cosmology

An overview of the cosmology directory, which formalizes FLRW cosmology.

## i. Overview

This module introduces no declarations. The definitions and results live in the
`Physlib.Cosmology.FLRW` submodules, which develop homogeneous and isotropic (FLRW) cosmology:
the models and the Friedmann equations, their matter content and exact solutions, and the
observables built from them.

## ii. Key results

- `Physlib.Cosmology.FLRW.Basic`: the structures `FLRW` and `CosmicFluid`, the Friedmann
  equations, and the Hubble and deceleration parameters.
- `Physlib.Cosmology.FLRW.MatterContent`, `Physlib.Cosmology.FLRW.FriedmannSolution`: the
  continuity equation and the scaling `ρ ∝ a^(-3(1+w))`, acceleration and the Big-Bang bound.
- `Physlib.Cosmology.FLRW.Solutions`, `Physlib.Cosmology.FLRW.DeSitter` and the
  `SpecificCases` submodules: the power-law, radiation, Einstein-de Sitter, Milne and de Sitter
  solutions.
- `Physlib.Cosmology.FLRW.DensityParameters`, `Physlib.Cosmology.FLRW.ReducedHubble`,
  `Physlib.Cosmology.FLRW.Age`, `Physlib.Cosmology.FLRW.Distances`: density parameters, the
  reduced Hubble function, the age of the universe, distances, redshift and horizons.
- `Physlib.Cosmology.FLRW.EnergyConditions`: the null, weak, strong and dominant energy
  conditions.

## iii. Table of contents

- A. Future work

## iv. References

* None.

## A. Future work

Open items are recorded as TODOs in the FLRW submodules, for example the conformal time in
`Physlib.Cosmology.FLRW.ConformalTime`.

-/

@[expose] public section
