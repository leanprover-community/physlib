/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Units.Basic
public import Physlib.Relativity.SpeedOfLight
public import Physlib.Relativity.GravitationalConstant
public import Physlib.QuantumMechanics.PlanckConstant
public import Physlib.StatisticalMechanics.BoltzmannConstant
/-!

# The physical constants of our world as dimensionful quantities

## i. Overview

The speed of light, Newton's constant, Planck's constant and the Boltzmann constant are not
units: each is a definite physical quantity, and the number recording it is fixed once a system
of units is chosen. This module gives their types a dimension, so that an element of
`Dimensionful` of any of them records the quantity itself rather than its value in one system of
units, and then defines the values these constants take in our world.

Each of these types consists of strictly positive reals, and so receives its action of `ℝ≥0ˣ`,
the rescaling by a strictly positive factor that a change of units effects, from
`PositiveRealUnitCore.instMulActionUnitsNNReal`. On none of them is an action of `ℝ≥0` compatible
with the magnitude, which is why `CarriesDimension` is stated for the units of `ℝ≥0`; see
`Physlib/Units/Basic.lean`.

## ii. Key results

- `speedOfLight` : the speed of light in our world, `299792458 m s⁻¹`.
- `gravitationalConstant` : Newton's constant in our world, `6.67430 × 10⁻¹¹ m³ kg⁻¹ s⁻²`.
- `planckConstant` : Planck's constant in our world, `6.62607015 × 10⁻³⁴ J s`.
- `reducedPlanckConstant` : the reduced Planck's constant in our world, `h / 2 π`.
- `boltzmannConstant` : the Boltzmann constant in our world,
  `1.380649 × 10⁻²³ J K⁻¹`.

## iii. Table of contents

- A. The speed of light
  - A.1. The value in our world
- B. Newton's constant
  - B.1. The value in our world
- C. Planck's constant
  - C.1. The values in our world
- D. The Boltzmann constant
  - D.1. The value in our world

## iv. References

* None.
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

/-!

## B. Newton's constant

Newton's constant carries the dimension of a volume divided by a mass and by the square of a
time, as the force `G m₁ m₂ / r²` must have the dimension of a mass times an acceleration.

-/

/-- Newton's constant has the dimension `L³ M⁻¹ T⁻²`. -/
instance : HasDim GravitationalConstant where
  d := L𝓭 * L𝓭 * L𝓭 * M𝓭⁻¹ * T𝓭⁻¹ * T𝓭⁻¹

/-!

### B.1. The value in our world

-/

/-- Newton's constant in our world, `6.67430 × 10⁻¹¹ m³ kg⁻¹ s⁻²`. Unlike a unit, this is a
  specific physical quantity: the value it takes in any given system of units is fixed by this
  choice. Unlike the speed of light, Planck's constant and the Boltzmann constant, Newton's
  constant is not a defining constant of the SI but a measured one, so this value is the
  currently recommended one rather than an exact definition. -/
noncomputable def gravitationalConstant : Dimensionful GravitationalConstant :=
  toDimensionful SI ⟨6.67430e-11, by norm_num⟩

@[simp]
lemma gravitationalConstant_in_SI :
    gravitationalConstant SI = ⟨6.67430e-11, by norm_num⟩ := by
  simp [gravitationalConstant, CarriesDimension.toDimensionful_apply_apply_units,
    LTMCTUnitChoices.dimScaleUnits_self]

/-!

## C. Planck's constant

Planck's constant carries the dimension of an action, a mass times the square of a length
divided by a time, as `E = h ν` must have the dimension of an energy.

-/

/-- Planck's constant has the dimension `M L² T⁻¹`. -/
instance : HasDim PlanckConstant where
  d := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹

/-!

### C.1. The values in our world

Planck's constant is one of the defining constants of the SI, so its value in SI units is exact.
The reduced constant is `h / 2 π`.

-/

/-- Planck's constant in our world, `6.62607015 × 10⁻³⁴ J s`, which is exact in SI units. -/
noncomputable def planckConstant : Dimensionful PlanckConstant :=
  toDimensionful SI ⟨6.62607015e-34, by norm_num⟩

@[simp]
lemma planckConstant_in_SI : planckConstant SI = ⟨6.62607015e-34, by norm_num⟩ := by
  simp [planckConstant, CarriesDimension.toDimensionful_apply_apply_units,
    LTMCTUnitChoices.dimScaleUnits_self]

/-- The reduced Planck's constant in our world, `h / 2 π`. -/
noncomputable def reducedPlanckConstant : Dimensionful PlanckConstant :=
  toDimensionful SI ⟨6.62607015e-34 / (2 * Real.pi), by
    have := Real.pi_pos
    positivity⟩

@[simp]
lemma reducedPlanckConstant_in_SI :
    reducedPlanckConstant SI = ⟨6.62607015e-34 / (2 * Real.pi), by
      have := Real.pi_pos
      positivity⟩ := by
  simp [reducedPlanckConstant, CarriesDimension.toDimensionful_apply_apply_units,
    LTMCTUnitChoices.dimScaleUnits_self]

/-- The reduced Planck's constant is Planck's constant divided by `2 π`, in every system of
  units: both scale by the same factor, so the relation is unit-independent. -/
lemma reducedPlanckConstant_val (u : LTMCTUnitChoices) :
    (reducedPlanckConstant u).val = (planckConstant u).val / (2 * Real.pi) := by
  have hpi := Real.pi_ne_zero
  show (PositiveRealUnitCore.val (reducedPlanckConstant u)) =
    (PositiveRealUnitCore.val (planckConstant u)) / (2 * Real.pi)
  simp only [reducedPlanckConstant, planckConstant,
    CarriesDimension.toDimensionful_apply_apply_units, PositiveRealUnitCore.val_units_smul,
    PlanckConstant.positiveRealUnitCore_val]
  field_simp

/-!

## D. The Boltzmann constant

The Boltzmann constant converts a temperature into an energy, so it carries the dimension of an
energy divided by a temperature.

-/

/-- The Boltzmann constant has the dimension `M L² T⁻² Θ⁻¹`. -/
instance : HasDim BoltzmannConstant where
  d := M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹ * Θ𝓭⁻¹

/-!

### D.1. The value in our world

The Boltzmann constant is one of the defining constants of the SI, so its value in SI units is
exact.

-/

/-- The Boltzmann constant in our world, `1.380649 × 10⁻²³ J K⁻¹`, which is exact in SI
  units. -/
noncomputable def boltzmannConstant : Dimensionful BoltzmannConstant :=
  toDimensionful SI ⟨1.380649e-23, by norm_num⟩

@[simp]
lemma boltzmannConstant_in_SI : boltzmannConstant SI = ⟨1.380649e-23, by norm_num⟩ := by
  simp [boltzmannConstant, CarriesDimension.toDimensionful_apply_apply_units,
    LTMCTUnitChoices.dimScaleUnits_self]
