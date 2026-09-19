/-
Copyright (c) 2026 Giuseppe Barbalinardo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuseppe Barbalinardo
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
/-!

# Thermoelectric figure of merit

## i. Overview

A thermoelectric material converts a temperature difference into electrical
power. In the linear-response (Onsager) regime, the coupled transport of
charge and heat in an isotropic material is governed by the constitutive
relations

  J = σ (E − S ∇T),        q = T S J − κ ∇T,

so a thermoelectric material is characterized by exactly four transport
coefficients: the Seebeck coefficient `S`, the electrical conductivity `σ`,
and the thermal conductivity `κ = κl + κe`, split into its lattice (phonon)
and electronic contributions because the two channels respond independently
to material design. These four coefficients are collected in the structure
`ThermoelectricMaterial`, and everything in this file is stated on it.

The performance of the material at absolute temperature `T` is captured by
the dimensionless figure of merit

  zT = σ S² T / (κl + κe),

whose numerator groups into the power factor `PF = σ S²`. Temperature is a
state variable, not a material property, so `T` enters as an argument rather
than a field. The four coefficients of a real material are themselves
temperature-dependent, so a `ThermoelectricMaterial` should be read as a
material at an operating point, its coefficients evaluated at the same
temperature at which `zT` is evaluated.

In this file all quantities are real numbers in a fixed consistent system of
units, following the convention of `Physlib.Thermodynamics.IdealGas.Basic`.

## ii. Key results

- `ThermoelectricMaterial`: the four linear-response transport coefficients
  of a thermoelectric material, with their physical sign constraints.
- `powerFactor`: the thermoelectric power factor `σ S²`.
- `totalThermalConductivity`: the total thermal conductivity `κl + κe`.
- `figureOfMerit`: the dimensionless figure of merit `zT`.
- `figureOfMerit_eq`: the flat form `zT = σ S² T / (κl + κe)`.
- `figureOfMerit_pos`: positivity of `zT` for a material with a nonzero
  Seebeck coefficient at positive temperature.
- `figureOfMerit_le_of_le`: lowering the lattice thermal conductivity raises
  `zT`, the phonon-glass electron-crystal design principle.

## iii. Table of contents

- A. The thermoelectric material
- B. The power factor
- C. The total thermal conductivity
- D. The figure of merit
  - D.1. Equalities for the figure of merit
  - D.2. Positivity of the figure of merit
  - D.3. Monotonicity in the lattice thermal conductivity

## iv. References

* Ioffe, A.F., Semiconductor Thermoelements and Thermoelectric Cooling, Infosearch (1957).
  [ref: ioffe_1957]
* Snyder, G.J., Toberer, E.S., Complex thermoelectric materials, Nature Materials 7, 105–114
  (2008). [ref: snyder_toberer_2008]
-/

@[expose] public section

noncomputable section

namespace CondensedMatter

/-!

## A. The thermoelectric material

The four fields are the complete set of linear-response coefficients for
coupled charge and heat transport in an isotropic material: no further
material parameter enters the steady-state thermoelectric equations, and
`zT` is a function of exactly these four together with the temperature.
The sign constraints are physical: a thermoelectric material conducts
charge (`0 < σ`) and its lattice conducts heat (`0 < κl`), while the
electronic heat channel can be negligible but never negative (`0 ≤ κe`).
The Seebeck coefficient is unconstrained: its sign records the carrier
type (negative for electrons, positive for holes), and it vanishes at
compensation points.

-/

/-- A thermoelectric material in the linear-response regime, characterized by
its four transport coefficients. -/
structure ThermoelectricMaterial where
  /-- The Seebeck coefficient `S`: the voltage developed per unit temperature
  difference. Its sign records the dominant carrier type. -/
  S : ℝ
  /-- The electrical conductivity `σ`. -/
  σ : ℝ
  /-- The lattice (phonon) contribution `κl` to the thermal conductivity. -/
  κl : ℝ
  /-- The electronic contribution `κe` to the thermal conductivity. -/
  κe : ℝ
  σ_pos : 0 < σ
  κl_pos : 0 < κl
  κe_nonneg : 0 ≤ κe

namespace ThermoelectricMaterial

/-!

## B. The power factor

-/

/-- The thermoelectric power factor `PF = σ S²` of a material. -/
def powerFactor (M : ThermoelectricMaterial) : ℝ := M.σ * M.S ^ 2

/-- The power factor is positive when the Seebeck coefficient is nonzero. -/
lemma powerFactor_pos {M : ThermoelectricMaterial} (hS : M.S ≠ 0) :
    0 < M.powerFactor := by
  unfold powerFactor
  -- `positivity` does not look through the projection, so name the field.
  have hσ := M.σ_pos
  positivity

/-!

## C. The total thermal conductivity

-/

/-- The total thermal conductivity `κl + κe` of a material, the sum of the
lattice (phonon) and electronic contributions. -/
def totalThermalConductivity (M : ThermoelectricMaterial) : ℝ := M.κl + M.κe

/-- The total thermal conductivity is positive. -/
lemma totalThermalConductivity_pos (M : ThermoelectricMaterial) :
    0 < M.totalThermalConductivity :=
  add_pos_of_pos_of_nonneg M.κl_pos M.κe_nonneg

/-!

## D. The figure of merit

-/

/-- The dimensionless thermoelectric figure of merit
`zT = PF · T / (κl + κe)` of a material at absolute temperature `T`. -/
def figureOfMerit (M : ThermoelectricMaterial) (T : ℝ) : ℝ :=
  M.powerFactor * T / M.totalThermalConductivity

/-!

### D.1. Equalities for the figure of merit

-/

/-- The figure of merit in its standard flat form
`zT = σ S² T / (κl + κe)`. -/
lemma figureOfMerit_eq (M : ThermoelectricMaterial) (T : ℝ) :
    M.figureOfMerit T = M.σ * M.S ^ 2 * T / (M.κl + M.κe) := by
  unfold figureOfMerit powerFactor totalThermalConductivity
  ring

/-!

### D.2. Positivity of the figure of merit

-/

/-- The figure of merit is positive at positive temperature when the Seebeck
coefficient is nonzero. -/
lemma figureOfMerit_pos {M : ThermoelectricMaterial} {T : ℝ}
    (hS : M.S ≠ 0) (hT : 0 < T) :
    0 < M.figureOfMerit T :=
  div_pos (mul_pos (powerFactor_pos hS) hT) M.totalThermalConductivity_pos

/-!

### D.3. Monotonicity in the lattice thermal conductivity

-/

/-- Lowering the lattice thermal conductivity raises the figure of merit: if
`M.κl ≤ κl'` then the material with lattice conductivity `κl'` (all other
coefficients equal) has the smaller `zT`. This is the phonon-glass
electron-crystal design principle: scatter phonons without degrading
electronic transport. Note the hypotheses: no condition on the Seebeck
coefficient is needed, since monotonicity only requires the numerator
`σ S² T` to be nonnegative. -/
lemma figureOfMerit_le_of_le (M : ThermoelectricMaterial) {κl' T : ℝ}
    (hpos : 0 < κl') (h : M.κl ≤ κl') (hT : 0 ≤ T) :
    figureOfMerit { M with κl := κl', κl_pos := hpos } T ≤ M.figureOfMerit T := by
  unfold figureOfMerit powerFactor totalThermalConductivity
  have hnum : (0 : ℝ) ≤ M.σ * M.S ^ 2 * T := by
    have hσ := M.σ_pos
    positivity
  have hden : 0 < M.κl + M.κe := add_pos_of_pos_of_nonneg M.κl_pos M.κe_nonneg
  gcongr

end ThermoelectricMaterial

end CondensedMatter
