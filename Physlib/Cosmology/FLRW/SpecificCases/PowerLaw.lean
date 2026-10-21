/-
Copyright (c) 2026 Philippe Kevorkian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Philippe Kevorkian
-/
module

public import Physlib.Cosmology.FLRW.Solutions
/-!

# The flat power-law models

## i. Overview

The spatially flat power-law solutions `a(t) = (t / t₀) ^ n` of `Physlib.Cosmology.FLRW.Solutions`
as FLRW models. The model `FLRW.powerLaw t₀ ht₀ n` lives on the interval `t > 0`, after the
origin `t.val = 0` of the time chart (for `n > 0`, the Big Bang, where the scale factor vanishes),
for a normalisation epoch `t₀ > 0`, and has flat spatial slices. Filled with the cosmic fluid
`CosmicFluid.powerLaw n w G c`, of density `3 n² / (8 π G t²)` and pressure `w ρ c²`, it solves
the Friedmann equations without cosmological constant when `n ≠ 0` and
`1 + 3 w = 2 (1 - n) / n`. The radiation-dominated and Einstein-de Sitter models, the
cases `n = 1/2` and `n = 2/3`, are in `Physlib.Cosmology.FLRW.SpecificCases.RadiationDominated`
and `Physlib.Cosmology.FLRW.SpecificCases.EinsteinDeSitter`.

## ii. Key results

- `FLRW.powerLaw`: the flat power-law model on the interval `t > 0`.
- `CosmicFluid.powerLaw`: the cosmic fluid of the flat power-law solution.
- `FLRW.friedmannSolution_powerLaw`: the model filled with this fluid solves the Friedmann
  equations.

## iii. Table of contents

- A. The power-law model
- B. The cosmic fluid and the Friedmann equations

## iv. References

* None.

-/

@[expose] public section

namespace Cosmology

open Real FLRW.FriedmannEquation

/-!

## A. The power-law model

-/

/-- The spatially flat power-law model `a(t) = (t / t₀) ^ n` on the interval `t > 0`, after the
  origin `t.val = 0` of the time chart (for `n > 0`, the Big Bang), for a normalisation epoch
  `t₀ > 0`. -/
noncomputable def FLRW.powerLaw (t₀ : Time) (ht₀ : 0 < t₀.val) (n : ℝ) : FLRW where
  I := {t | 0 < t.val}
  isOpen_I := isOpen_lt continuous_const Time.val_differentiable.continuous
  ordConnected_I := ⟨fun x hx _ _ z hz =>
    lt_of_lt_of_le (show 0 < x.val from hx) ((Time.le_def x z).mp hz.1)⟩
  a := fun s => (s.val / t₀.val) ^ n
  a_pos _ ht := Real.rpow_pos_of_pos (div_pos ht ht₀) n
  differentiableOn_a := fun t (ht : 0 < t.val) =>
    (DifferentiableAt.comp (g := fun y : ℝ => (y / t₀.val) ^ n) t
      ((differentiableAt_id.div_const t₀.val).rpow_const (Or.inl (div_pos ht ht₀).ne'))
      (Time.val_differentiable t)).differentiableWithinAt
  differentiableOn_deriv_a := by
    refine DifferentiableOn.congr (f := fun s : Time => n / t₀.val * (s.val / t₀.val) ^ (n - 1))
      (fun t (ht : 0 < t.val) => (DifferentiableAt.comp
        (g := fun y : ℝ => n / t₀.val * (y / t₀.val) ^ (n - 1)) t
        (((differentiableAt_id.div_const t₀.val).rpow_const
          (Or.inl (div_pos ht ht₀).ne')).const_mul _)
        (Time.val_differentiable t)).differentiableWithinAt) ?_
    intro t (ht : 0 < t.val)
    exact deriv_powerLaw ht₀.ne' n (ne_of_gt ht)
  geometry := .Flat

/-!

## B. The cosmic fluid and the Friedmann equations

-/

/-- The cosmic fluid of the flat power-law solution: the density `ρ = 3 n² / (8 π G t²)` imposed by
  the first-order Friedmann equation, and the pressure `p = w ρ c²`. -/
noncomputable def CosmicFluid.powerLaw (n w G c : ℝ) : CosmicFluid :=
  ⟨fun s => 3 * n ^ 2 / (8 * π * G * s.val ^ 2),
    fun s => w * (3 * n ^ 2 / (8 * π * G * s.val ^ 2)) * c ^ 2⟩

/-- The flat power-law model with `n ≠ 0`, filled with the fluid `CosmicFluid.powerLaw n w G c`
  where `1 + 3 w = 2 (1 - n) / n`, solves the Friedmann equations without cosmological constant on
  its interval `t > 0`. -/
lemma FLRW.friedmannSolution_powerLaw {t₀ : Time} (ht₀ : 0 < t₀.val)
    {n w G c : ℝ} (hG : 0 < G) (hc : 0 < c) (hn : n ≠ 0) (hw : 1 + 3 * w = 2 * (1 - n) / n) :
    (FLRW.powerLaw t₀ ht₀ n).FriedmannSolution (CosmicFluid.powerLaw n w G c) 0 G c :=
  ⟨fun _ ht => powerLaw_firstOrderFriedmann ht₀ hG n ht,
    fun _ ht => powerLaw_secondOrderFriedmann ht₀ hG hc hn hw ht⟩

end Cosmology
