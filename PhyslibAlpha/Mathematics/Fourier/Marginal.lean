/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Distribution.SchwartzPointwise
public import PhyslibAlpha.Mathematics.MeasureTheory.EuclideanProd
public import PhyslibAlpha.Mathematics.Fourier.LinearChange

/-!

# The marginal of a Schwartz function on a Euclidean product

The integral of a Schwartz function over the second factor is continuous and integrable. Its
Fourier transform is the restriction of the transform to the first factor.

## i. Overview

A Schwartz function on `WithLp 2 (E × F)` decays faster than every power in the second variable,
uniformly in the first. The marginal over `F` is therefore a continuous integrable function on
`E`. Its Fourier transform at `ξ` is the transform of the original function at `(ξ, 0)`.

## ii. Key results

- `EuclideanProd.fourier_marginal` : the transform of the marginal is the restriction of the
  transform.
- `EuclideanProd.continuous_marginal` : the marginal of a Schwartz function is continuous.
- `EuclideanProd.integrable_marginal` : the marginal of a Schwartz function is integrable.
- `EuclideanProd.fourier_eq_integral_integral` : the transform is the iterated transform.

## iii. Table of contents

- A. The transform of the marginal
- B. The marginal of a Schwartz function
- C. The iterated transform

## iv. References

None.

## A. The transform of the marginal

- `EuclideanProd.fourier_marginal` : the transform of the marginal is the restriction of the
  transform.

## B. The marginal of a Schwartz function

- `EuclideanProd.exists_bound_marginal` : a Schwartz function decays in the extra variables.
- `EuclideanProd.continuous_marginal` : the marginal of a Schwartz function is continuous.
- `EuclideanProd.integrable_marginal` : the marginal of a Schwartz function is integrable.

## C. The iterated transform

- `EuclideanProd.fourier_eq_integral_integral` : the transform is the iterated transform.
-/

@[expose] public section

noncomputable section

open scoped FourierTransform SchwartzMap
open MeasureTheory

namespace EuclideanProd

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

/-- **The transform of the marginal.** The Fourier transform of the integral over `F` is the
restriction of the transform to the frequencies `(ξ, 0)`. -/
lemma fourier_marginal {φ : WithLp 2 (E × F) → ℂ} (hφ : Integrable φ) (ξ : E) :
    ∫ x : E, (𝐞 (-inner ℝ x ξ) : ℂ) • ∫ y : F, φ (WithLp.toLp 2 (x, y)) =
      ∫ z, (𝐞 (-inner ℝ z (WithLp.toLp 2 (ξ, (0 : F)))) : ℂ) • φ z := by
  rw [integral_withLp_prod]
  have hint := integrable_withLp_prod hφ
  have hc : Continuous fun p : E × F => (𝐞 (-inner ℝ p.1 ξ) : ℂ) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp
      ((continuous_fst.inner continuous_const).neg))
  have hint2 : Integrable (fun p : E × F => (𝐞 (-inner ℝ p.1 ξ) : ℂ) •
      φ (WithLp.toLp 2 p)) := by
    refine hint.norm.mono' (hc.aestronglyMeasurable.smul hint.aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun p => by
      rw [norm_smul, Circle.norm_coe, one_mul]
  have hinner : ∀ p : E × F, inner ℝ (WithLp.toLp 2 p) (WithLp.toLp 2 (ξ, (0 : F))) =
      inner ℝ p.1 ξ := fun p => by simp [WithLp.prod_inner_apply]
  simp_rw [hinner]
  rw [Measure.volume_eq_prod, integral_prod _ (by simpa [Measure.volume_eq_prod] using hint2)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [integral_smul]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [MeasurableSpace F] [BorelSpace F]
  [FiniteDimensional ℝ F] in
/-- A Schwartz function decays in the extra variables, uniformly in the others. -/
lemma exists_bound_marginal (h : 𝓢(WithLp 2 (E × F), ℂ)) :
    ∃ C : ℝ, ∀ (x : E) (y : F), ‖h (WithLp.toLp 2 (x, y))‖ ≤
      C * (1 + ‖y‖) ^ (-((Module.finrank ℝ F + 1 : ℕ) : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := h.exists_norm_le_rpow_neg (Module.finrank ℝ F + 1)
  refine ⟨C, fun x y => (hC _).trans (mul_le_mul_of_nonneg_left ?_ hC0)⟩
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (neg_nonpos.2 (Nat.cast_nonneg _))
  linarith [norm_le_norm_toLp_right x y]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The marginal of a Schwartz function is continuous. -/
lemma continuous_marginal (h : 𝓢(WithLp 2 (E × F), ℂ)) :
    Continuous fun x : E => ∫ y : F, h (WithLp.toLp 2 (x, y)) := by
  obtain ⟨C, hC⟩ := exists_bound_marginal h
  have hn : (Module.finrank ℝ F : ℝ) < ((Module.finrank ℝ F + 1 : ℕ) : ℝ) := by
    push_cast; linarith
  refine continuous_of_dominated (bound := fun y : F =>
    C * (1 + ‖y‖) ^ (-((Module.finrank ℝ F + 1 : ℕ) : ℝ))) (fun x => ?_) (fun x => ?_) ?_ ?_
  · exact (h.continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => hC x y
  · exact (integrable_one_add_norm hn).const_mul C
  · exact Filter.Eventually.of_forall fun y => h.continuous.comp (by fun_prop)

/-- The marginal of a Schwartz function is integrable. -/
lemma integrable_marginal (h : 𝓢(WithLp 2 (E × F), ℂ)) :
    Integrable fun x : E => ∫ y : F, h (WithLp.toLp 2 (x, y)) := by
  have := (integrable_withLp_prod h.integrable).integral_prod_left
  simpa [Measure.volume_eq_prod] using this

/-- **The iterated form of the Fourier transform.** The transform on the Euclidean product is the
transform in the first variable of the transform in the second. -/
lemma fourier_eq_integral_integral (g : 𝓢(WithLp 2 (E × F), ℂ)) (ζ : E) (ξ : F) :
    𝓕 g (WithLp.toLp 2 (ζ, ξ)) = ∫ x : E, 𝐞 (-(inner ℝ x ζ)) •
      ∫ y : F, 𝐞 (-(inner ℝ y ξ)) • g (WithLp.toLp 2 (x, y)) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq, integral_withLp_prod]
  have hi : Integrable fun y : E × F =>
      𝐞 (-inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 (ζ, ξ))) • g (WithLp.toLp 2 y) := by
    refine integrable_withLp_prod (φ := fun p => 𝐞 (-inner ℝ p (WithLp.toLp 2 (ζ, ξ))) • g p) ?_
    refine Integrable.mono' g.integrable.norm ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (Continuous.smul (by fun_prop) g.continuous).aestronglyMeasurable
    · simp
  rw [Measure.volume_eq_prod, integral_prod _ (by simpa [Measure.volume_eq_prod] using hi)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [WithLp.prod_inner_apply, neg_add, AddChar.map_add_eq_mul, mul_smul, Circle.smul_def,
    smul_eq_mul]
  rw [integral_const_mul]

end EuclideanProd
