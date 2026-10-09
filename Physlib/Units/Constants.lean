/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Units.Basic
public import Physlib.Relativity.SpeedOfLight
/-!

# The physical constants of our world as dimensionful quantities

## i. Overview

A physical constant is not a unit: it is a definite physical quantity, and the number recording
it is fixed once a system of units is chosen. This module gives the types of such constants a
dimension, so that an element of `Dimensionful` of one of them records the quantity itself rather
than its value in one system of units, and then defines the values the constants take in our
world. At present it covers the speed of light; Newton's constant, Planck's constant and the
Boltzmann constant are to follow.

Such a type consists of strictly positive reals, and so receives its action of `ℝ≥0ˣ`, the
rescaling by a strictly positive factor that a change of units effects, from
`PositiveRealUnitCore.instMulActionUnitsNNReal`. On it no action of `ℝ≥0` is compatible with the
magnitude, which is why `CarriesDimension` is stated for the units of `ℝ≥0`; see
`Physlib/Units/Basic.lean`.

## ii. Key results

- `speedOfLight` : the speed of light in our world, `299792458 m s⁻¹`.

## iii. Table of contents

- A. The speed of light
  - A.1. The value in our world

## iv. References

* The defining value of the speed of light. [ref: bipm_si_brochure_2019]
-/

@[expose] public section

open Dimension LTMCTUnitChoices CarriesDimension

/-!

## A. The speed of light

-/

/-- The speed of light has the dimension of a length divided by a time. -/
instance : HasDim SpeedOfLight where
  d := L𝓭 * T𝓭⁻¹

/-!

### A.1. The value in our world

-/

/-- The speed of light in our world, `299792458 m s⁻¹`, which is exact in SI units. -/
noncomputable def speedOfLight : Dimensionful SpeedOfLight :=
  toDimensionful SI ⟨299792458, by norm_num⟩

@[simp]
lemma speedOfLight_in_SI : speedOfLight SI = ⟨299792458, by norm_num⟩ := by
  simp [speedOfLight, CarriesDimension.toDimensionful_apply_apply_units,
    LTMCTUnitChoices.dimScaleUnits_self]
