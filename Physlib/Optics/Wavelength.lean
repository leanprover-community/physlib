/-
Copyright (c) 2026 Samyak Rai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samyak Rai
-/
module

public import Physlib.Optics.Frequency
/-!

# Wavelength

In this module we define the type `Wavelength`, corresponding to the wavelength of a wave
carrying the dimension of length, and relate it to the type `Frequency` through the
propagation speed of the wave via the relation `c = λ * ν`.

## i. Overview

The type `Wavelength` is `WithDim L𝓭 ℝ≥0`, i.e., a nonnegative real number tagged with
the dimension of length.

For a wave of frequency `ν > 0` propagating at a speed `c` (e.g. the speed of light),
the associated wavelength is `λ = c / ν`, and conversely a wave of wavelength `λ > 0`
has frequency `ν = c / λ`. These two constructions are inverse to one another.

## ii. Key results

- `Wavelength` : The type of wavelengths of waves.
- `Wavelength.ofFrequency` : The wavelength `c / ν` associated with a positive frequency.
- `Frequency.ofWavelength` : The frequency `c / λ` associated with a positive wavelength.
- `Wavelength.ofFrequency_mul` : The relation `λ * ν = c`.
- `Frequency.ofWavelength_mul` : The relation `ν * λ = c`.
- `Wavelength.ofFrequency_ofWavelength` and `Frequency.ofWavelength_ofFrequency` : The
  two constructions are inverse to one another.
- `Wavelength.ofFrequency_scaleUnit` and `Frequency.ofWavelength_scaleUnit` : The
  constructions commute with changes of units.
- `speedEqWavelengthMulFrequency_isDimensionallyCorrect` : The relation `c = λ * ν` is
  dimensionally correct.

## iii. Table of contents

- A. The Wavelength type
- B. Wavelength from frequency
- C. Frequency from wavelength
- D. Round trips
- E. Dimensional correctness

## iv. References

- https://en.wikipedia.org/wiki/Wavelength

-/

@[expose] public section

open Dimension
open scoped NNReal
open LTMCTUnitChoices UnitDependent

/-!

## A. The Wavelength type

-/

/-- The type `Wavelength` represents the distance between consecutive
corresponding points of the same phase on the wave, such as two adjacent
crests, troughs, or zero crossings, i.e. a nonnegative real number
carrying the dimension of length. -/
abbrev Wavelength : Type := WithDim L𝓭 ℝ≥0

namespace Wavelength

/-!

## B. Wavelength from frequency

-/

/-- The wavelength of a wave of frequency `ν` propagating at a speed `c`,
given by `λ = c / ν`. -/
noncomputable def ofFrequency (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (ν : Frequency) (_ν_pos : 0 < ν.val) :
    Wavelength := ⟨c.val / ν.val⟩

@[simp]
lemma ofFrequency_val (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (ν : Frequency) (hν : 0 < ν.val) :
    (ofFrequency c ν hν).val = c.val / ν.val := rfl

/-- Positivity of the wavelength associated with a positive frequency and a positive
speed. -/
lemma ofFrequency_pos (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (hc : 0 < c.val) (ν : Frequency)
    (hν : 0 < ν.val) : 0 < (ofFrequency c ν hν).val :=
  div_pos hc hν

/-- The wavelength associated with a frequency satisfies `λ * ν = c`. -/
lemma ofFrequency_mul (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (ν : Frequency) (hν : 0 < ν.val) :
    (ofFrequency c ν hν).val * ν.val = c.val :=
  div_mul_cancel₀ c.val (ne_of_gt hν)

/-- The wavelength associated with a frequency scales with units as a wavelength should:
changing the units from `u1` to `u2` rescales the resulting wavelength by the scale factor
of the dimension of length. -/
lemma ofFrequency_scaleUnit (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (ν : Frequency) (hν : 0 < ν.val)
    (u1 u2 : LTMCTUnitChoices) :
    ofFrequency (scaleUnit u1 u2 c) (scaleUnit u1 u2 ν) (WithDim.scaleUnit_val_pos ν hν u1 u2) =
      scaleUnit u1 u2 (ofFrequency c ν hν) := by
  refine WithDim.ext _ _ ?_
  simp only [ofFrequency_val, WithDim.scaleUnit_val, smul_eq_mul, map_mul]
  field_simp [dimScale_ne_zero u1 u2 T𝓭⁻¹, hν]

end Wavelength

namespace Frequency

/-!

## C. Frequency from wavelength

-/

/-- The frequency of a wave of wavelength `w` propagating at a speed `c`,
given by `ν = c / w`. We can't use `λ` due to Lean anon function. -/
noncomputable def ofWavelength (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (w : Wavelength) (_w_pos : 0 < w.val) :
    Frequency := ⟨c.val / w.val⟩

@[simp]
lemma ofWavelength_val (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (w : Wavelength) (w_pos : 0 < w.val) :
    (ofWavelength c w w_pos).val = c.val / w.val := rfl

/-- Positivity of the frequency associated with a positive wavelength and a positive
speed. -/
lemma ofWavelength_pos (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (c_pos : 0 < c.val) (w : Wavelength)
    (hw : 0 < w.val) : 0 < (ofWavelength c w hw).val :=
  div_pos c_pos hw

/-- The frequency associated with a wavelength satisfies `ν * λ = c`. -/
lemma ofWavelength_mul (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (w : Wavelength) (w_pos : 0 < w.val) :
    (ofWavelength c w w_pos).val * w.val = c.val :=
  div_mul_cancel₀ c.val (ne_of_gt w_pos)

/-- The frequency associated with a wavelength scales with units as a frequency should:
changing the units from `u1` to `u2` rescales the resulting frequency by the scale factor
of the dimension of inverse time. -/
lemma ofWavelength_scaleUnit (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (w : Wavelength) (w_pos : 0 < w.val)
    (u1 u2 : LTMCTUnitChoices) :
    ofWavelength (scaleUnit u1 u2 c) (scaleUnit u1 u2 w)
      (WithDim.scaleUnit_val_pos w w_pos u1 u2) =
      scaleUnit u1 u2 (ofWavelength c w w_pos) := by
  refine WithDim.ext _ _ ?_
  simp only [ofWavelength_val, WithDim.scaleUnit_val, smul_eq_mul, map_mul]
  field_simp [dimScale_ne_zero u1 u2 L𝓭, w_pos]

/-!

## D. Round trips

-/

/-- Converting a wavelength to a frequency and back recovers the wavelength. -/
@[simp]
lemma ofWavelength_ofFrequency (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (hc : 0 < c.val)
    (ν : Frequency) (hν : 0 < ν.val) :
    ofWavelength c (Wavelength.ofFrequency c ν hν)
      (Wavelength.ofFrequency_pos c hc ν hν) = ν := by
  ext
  simp only [ofWavelength_val, Wavelength.ofFrequency_val, NNReal.coe_div]
  exact div_div_cancel₀ (ne_of_gt hc)

end Frequency

namespace Wavelength

/-- Converting a frequency to a wavelength and back recovers the frequency. -/
@[simp]
lemma ofFrequency_ofWavelength (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ≥0) (hc : 0 < c.val)
    (w : Wavelength) (hw : 0 < w.val) :
    ofFrequency c (Frequency.ofWavelength c w hw)
      (Frequency.ofWavelength_pos c hc w hw) = w := by
  ext
  simp only [ofFrequency_val, Frequency.ofWavelength_val, NNReal.coe_div]
  exact div_div_cancel₀ (ne_of_gt hc)

end Wavelength

/-!

## E. Dimensional correctness

-/

/-- The relation `c = λ * ν` between a speed `c`, a wavelength `λ` and a frequency `ν`,
stated on real-valued quantities carrying the dimensions of speed, length and inverse time
respectively. -/
def SpeedEqWavelengthMulFrequency (c : WithDim (L𝓭 * T𝓭⁻¹) ℝ) (w : WithDim L𝓭 ℝ)
    (ν : WithDim T𝓭⁻¹ ℝ) : Prop :=
  c = w * ν

/-- The relation `c = λ * ν` is dimensionally correct: it holds in one system of units if and
only if it holds in every system of units. -/
lemma speedEqWavelengthMulFrequency_isDimensionallyCorrect :
    IsDimensionallyCorrect SpeedEqWavelengthMulFrequency := by
  simp [funext_iff, SpeedEqWavelengthMulFrequency]
