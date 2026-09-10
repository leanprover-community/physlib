/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Units.WithDim.Speed
public import Physlib.Units.FDeriv
/-!

# Examples of units in Physlib

In this module we give some examples of how to use the units system in Physlib.
This module should not be imported into any other module, and the results here
should not be used in the proofs of any other results other then those in this file.

-/

@[expose] public section

namespace UnitExamples
open Dimension CarriesDimension LTMCTUnitChoices UnitDependent HasDim
/-!

## Defining a length dependent on units

-/

/-- The length corresponding to 400 meters. -/
noncomputable def meters400 : Dimensionful (WithDim L𝓭 ℝ) := toDimensionful SI ⟨400⟩

set_option backward.isDefEq.respectTransparency false in
/-- Changing that length to miles.
  400 meters is very almost a quarter of a mile. -/
example : meters400 {SI with length := LengthUnit.miles} = ⟨1/4 - 73/50292⟩ := by
  simp [meters400, toDimensionful_apply_apply, dimScale, LengthUnit.miles]
  ext
  show (1609.344 : ℝ)⁻¹ * 400 = _
  norm_num

/-!

## Proving propositions are dimensionally correct

-/

/-!

## Cases with only WithDim

-/

open WithDim

/-- An example of dimensions corresponding to `E = m c^2` using `WithDim`. -/
def EnergyMassWithDim' (m : WithDim M𝓭 ℝ) (E : WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)
    (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ) : Prop := E = cast (m * c * c)

lemma energyMassWithDim'_isDimensionallyCorrect :
    IsDimensionallyCorrect EnergyMassWithDim' := by simp [funext_iff, EnergyMassWithDim']

/-- An example of dimensions corresponding to `F = m a` using `WithDim`. -/
def NewtonsSecondWithDim' (m : WithDim M𝓭 ℝ) (F : WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)
    (a : WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) : Prop :=
    F = cast (m * a)

lemma newtonsSecondWithDim'_isDimensionallyCorrect :
    IsDimensionallyCorrect NewtonsSecondWithDim' := by simp [funext_iff, NewtonsSecondWithDim']

/-- An example of dimensions corresponding to `s = d/t` using `WithDim`. -/
def SpeedEq (s : WithDim (L𝓭 * T𝓭⁻¹) ℝ) (d : WithDim L𝓭 ℝ) (t : WithDim T𝓭 ℝ) : Prop :=
  s = cast (d / t)

lemma speedEq_isDimensionallyCorrect : IsDimensionallyCorrect SpeedEq := by
  simp [funext_iff, SpeedEq]

/-- An example with complicated dimensions. -/
def OddDimensions (m1 m2 : WithDim (M𝓭) ℝ)
    (θ : WithDim Θ𝓭 ℝ) (I1 I2 : WithDim (C𝓭/T𝓭) ℝ) (d : WithDim L𝓭 ℝ) (t : WithDim T𝓭 ℝ)
    (X : WithDim (L𝓭 * T𝓭⁻¹ ^ 3 * Θ𝓭⁻¹ * C𝓭 ^2) ℝ) : Prop :=
    X = cast (m1 * (d / t) / (m2 * θ) * I2 * I1)

lemma oddDimensions_isDimensionallyCorrect : IsDimensionallyCorrect OddDimensions := by
  simp [funext_iff, OddDimensions]

/-- An example of dimensions corresponding to `E = m c^2` using `WithDim` with `.val`. -/
def EnergyMassWithDim (m : WithDim M𝓭 ℝ) (E : WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)
    (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ) : Prop :=
  E.1 = m.1 * c.1 ^ 2

lemma energyMassWithDim_isDimensionallyCorrect : IsDimensionallyCorrect EnergyMassWithDim := by
  simp [funext_iff, EnergyMassWithDim]
  intros
  rw [WithDim.scaleUnit_val_eq_scaleUnit_val_of_dim_eq]

/-- An example of dimensions corresponding to `F = m a` using `WithDim` with `.val`. -/
def NewtonsSecondWithDim (m : WithDim M𝓭 ℝ) (F : WithDim (M𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)
    (a : WithDim (L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ) : Prop :=
  F.1 = m.1 * a.1

lemma newtonsSecondWithDim_isDimensionallyCorrect :
    IsDimensionallyCorrect NewtonsSecondWithDim := by
  simp [funext_iff, NewtonsSecondWithDim]
  intros
  rw [WithDim.scaleUnit_val_eq_scaleUnit_val_of_dim_eq]

/-- An example of dimensions corresponding to `E = m c` using `WithDim` with `.val`,
  which is not dimensionally correct. -/
def EnergyMassWithDimNot (m : WithDim M𝓭 ℝ) (E : WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)
    (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ) : Prop :=
  E.1 = m.1 * c.1

lemma energyMassWithDimNot_not_isDimensionallyCorrect :
    ¬ IsDimensionallyCorrect EnergyMassWithDimNot := by
  simp only [isDimensionallyCorrect_fun_iff, not_forall, funext_iff, scaleUnit_apply_fun]
  /- We show that `EnergyMassWithDimNot` is not dimensionally correct by
    changing from `SI` to `SIPrimed` with values of `E`, `m` and `c` all equal to `1`. -/
  use SI, SIPrimed, ⟨1⟩, ⟨1⟩, ⟨1⟩
  unfold EnergyMassWithDimNot
  norm_num [WithDim.scaleUnit_val, M𝓭, NNReal.smul_def]

/-!

## Cases with Dimensionful

-/
open DimSpeed

/-- The equation `E = m c^2`, in this equation we `E` and `m` are implicitly in the
  units `u`, while the speed of light is explicitly written in those units. -/
def EnergyMass (m : WithDim M𝓭 ℝ) (E : WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ)
    (u : LTMCTUnitChoices) : Prop :=
    E.1 = m.1 * (speedOfLight u).1 ^ 2

/-- The equation `E = m c^2`, in this version everything is written explicitly in
  terms of a choice of units. -/
def EnergyMass' (m : Dimensionful (WithDim M𝓭 ℝ))
    (E : Dimensionful (WithDim (M𝓭 * L𝓭 * L𝓭 * T𝓭⁻¹ * T𝓭⁻¹) ℝ))
    (u : LTMCTUnitChoices) : Prop :=
    (E.1 u).1 = (m.1 u).1 * (speedOfLight u).1 ^ 2

/-- The lemma that the proposition `EnergyMass` is dimensionally correct-/
lemma energyMass_isDimensionallyCorrect :
    IsDimensionallyCorrect EnergyMass := by
  intro u1 u2
  funext m E u
  change EnergyMassWithDim (scaleUnit u2 u1 m) (scaleUnit u2 u1 E)
    (speedOfLight (scaleUnit u2 u1 u)) = EnergyMassWithDim m E (speedOfLight u)
  have hs : speedOfLight (scaleUnit u2 u1 u) =
      scaleUnit u2 u1 (speedOfLight u) := by
    simpa only [HasDim.scaleUnit_apply] using
      (Dimensionful.of_scaleUnit (u1 := u2) (u2 := u1) (u := u) speedOfLight)
  rw [hs]
  exact congrFun (congrFun (congrFun (energyMassWithDim_isDimensionallyCorrect u1 u2)
    m) E) (speedOfLight u)

/-!

## Examples of using `isDimensionallyCorrect`

We now explore the consequences of `energyMass_isDimensionallyCorrect` and how we can use it.

-/

lemma example1_energyMass : EnergyMass ⟨2⟩ ⟨2 * 299792458 ^ 2⟩ SI := by
  simp [EnergyMass, speedOfLight, toDimensionful_apply_apply, dimScale, SI]

/- The lemma `energyMass_isDimensionallyCorrect` allows us to scale the units
  of `example1_energyMass`, that is - we proved it in one set of units, but we get the result
  in any set of units. -/
lemma example2_energyMass (u : LTMCTUnitChoices) :
    EnergyMass (scaleUnit SI u ⟨2⟩) (scaleUnit SI u ⟨2 * 299792458 ^ 2⟩) u := by
  conv_rhs => rw [← LTMCTUnitChoices.scaleUnit_apply_fst SI u]
  rw [← energyMass_isDimensionallyCorrect SI u]
  simp only [scaleUnit_apply_fst, scaleUnit_apply_fun, scaleUnit_symm_apply,
    scaleUnit_apply_fun_left]
  exact example1_energyMass

/-!

## Examples with other functions
-/

/-- An example of a dimensionally correct result using functions. -/
def CosDim (t : WithDim T𝓭 ℝ) (ω : WithDim T𝓭⁻¹ ℝ) (a : ℝ) : Prop :=
  Real.cos (ω.1 * t.1) = a

lemma cosDim_isDimensionallyCorrect : IsDimensionallyCorrect CosDim := by
  simp [funext_iff, CosDim]

/-!

## An example involving derivatives

-/

example {M1 M2 : Type} [NormedAddCommGroup M1] [NormedSpace ℝ M1]
    [ContinuousConstSMul ℝ M1] [HasDim M1]
    [NormedAddCommGroup M2] [NormedSpace ℝ M2] [SMulCommClass ℝ ℝ M2]
    [ContinuousConstSMul ℝ M2] [HasDim M2] (f : M1 → M2)
    (hf : IsDimensionallyCorrect f) (f_diff : Differentiable ℝ f) :
    IsDimensionallyCorrect (fderiv ℝ f) :=
  fderiv_isDimensionallyCorrect f hf f_diff

example {M1 M2 : Type} [NormedAddCommGroup M1] [NormedSpace ℝ M1]
    [ContinuousConstSMul ℝ M1] [HasDim M1]
    [NormedAddCommGroup M2] [NormedSpace ℝ M2] [SMulCommClass ℝ ℝ M2]
    [ContinuousConstSMul ℝ M2] [HasDim M2] (dm : M1) (f : M1 → M2)
    (hf : IsDimensionallyCorrect f) (f_diff : Differentiable ℝ f) :
    IsDimensionallyCorrect (fun x (v : WithDim (dim M2 * (dim M1)⁻¹) M2) =>
      fderiv ℝ f x dm = v.1) :=
  fderiv_dimension_const_direction dm f hf f_diff
end UnitExamples
