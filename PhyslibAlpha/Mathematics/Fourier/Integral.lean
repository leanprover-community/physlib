/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Choose.Multinomial

/-!

# Fourier integrals and their derivatives

## i. Overview

Derivative bounds for the Fourier character and the Laplacian of an inverse Fourier integral.

## ii. Key results

- `laplacian_fourierInvIntegral` : The Laplacian of the inverse Fourier integral of `h` is the
  integral of `-(2π)² ‖ξ‖² h`.
- `char_pow_mul_decay_le` : Polynomial factors from spatial derivatives are absorbed by additional
  Fourier decay.
- `fourierInvIntegral_eq_fourier` : The inverse Fourier integral is the Fourier integral of the
  reflected function.
- `norm_iteratedFDeriv_timeShift_le` : The derivatives of a time translate are bounded by those of
  the function.

## iii. Table of contents

- A. The Laplacian of an inverse Fourier integral
- B. Derivative bounds for the Fourier character and for time translates
- C. Smoothness of the retarded solution

## iv. References

None.

## A. The Laplacian of an inverse Fourier integral

Lemmas: `fourierInvIntegral_eq_fourier`, `laplacian_fourierInvIntegral`.

## B. Derivative bounds for the Fourier character and for time translates

Lemmas: `iteratedDeriv_fourierChar`, `norm_iteratedFDeriv_fourierChar`, `contDiff_fourierChar_real`,
`norm_iteratedFDeriv_char_le`, `norm_iteratedFDeriv_timeShift_le`, `char_pow_mul_decay_le`.

## C. Smoothness of the retarded solution

Lemmas: `contDiff_char_pair`.

-/

@[expose] public section

noncomputable section

open scoped FourierTransform Real Laplacian ContDiff
open InnerProductSpace MeasureTheory TopologicalSpace Topology
universe u

namespace FourierIntegral

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]

omit [CompleteSpace F] in
/-- The inverse Fourier integral is the Fourier integral of the reflected function. -/
lemma fourierInvIntegral_eq_fourier (h : E → F) (x : E) :
    ∫ ξ : E, (𝐞 (inner ℝ ξ x) : ℂ) • h ξ = 𝓕 (fun v => h (-v)) x := by
  rw [Real.fourier_eq]
  rw [← integral_neg_eq_self (fun v => 𝐞 (-inner ℝ v x) • h (-v))]
  simp [Circle.smul_def]

/-- The Laplacian of the inverse Fourier integral of `h` is the integral of `-(2π)² ‖ξ‖² h`. -/
lemma laplacian_fourierInvIntegral {h : E → F} (hm : AEStronglyMeasurable h volume)
    (hi : ∀ n : ℕ, n ≤ 2 → Integrable (fun ξ : E => ‖ξ‖ ^ n * ‖h ξ‖)) (x : E) :
    Δ (fun y : E => ∫ ξ : E, (𝐞 (inner ℝ ξ y) : ℂ) • h ξ) x =
      ∫ ξ : E, (-((2 * π) ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) • ((𝐞 (inner ℝ ξ x) : ℂ) • h ξ) := by
  have hg : ∀ n : ℕ, n ≤ (2 : ℕ∞) → Integrable (fun v : E => ‖v‖ ^ n * ‖(fun v => h (-v)) v‖) := by
    intro n hn
    have := (hi n (by exact_mod_cast hn)).comp_neg
    simpa using this
  have hgm : AEStronglyMeasurable (fun v : E => h (-v)) volume := (hm.comp_measurePreserving
    (Measure.measurePreserving_neg (volume : Measure E)))
  simp_rw [fourierInvIntegral_eq_fourier]
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    Real.iteratedFDeriv_fourier hg hgm (le_refl _)]
  set g : E → F := fun v => h (-v) with hgdef
  set b := stdOrthonormalBasis ℝ E
  set G : E → ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F :=
    fun v => VectorFourier.fourierPowSMulRight (innerSL ℝ) g v 2 with hG
  have hGint : Integrable G volume :=
    VectorFourier.integrable_fourierPowSMulRight (innerSL ℝ) (hg 2 le_rfl) hgm
  have hint : Integrable (fun v : E => (𝐞 (-inner ℝ v x) : ℂ) • G v) volume := by
    refine hGint.norm.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
    · have hc : Continuous fun v : E => (𝐞 (-inner ℝ v x) : ℂ) :=
        continuous_subtype_val.comp (Real.continuous_fourierChar.comp
          ((continuous_id.inner continuous_const).neg))
      exact hc.aestronglyMeasurable.smul hGint.aestronglyMeasurable
    · rw [norm_smul, Circle.norm_coe, one_mul]
  let L : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F →L[ℝ] F :=
    ∑ i, ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) F ![b i, b i]
  have hL : ∀ v, L (G v) = ((-(2 * π * Complex.I)) ^ 2 * (‖v‖ ^ 2 : ℝ)) • g v := by
    intro v
    simp only [L, hG, sum_apply, ContinuousMultilinearMap.apply_apply,
      VectorFourier.fourierPowSMulRight_apply]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hs : ∑ i, ((innerSL ℝ v) (b i) * (innerSL ℝ v) (b i)) = ‖v‖ ^ 2 := by
      simp only [innerSL_apply_apply, ← sq]
      simp_rw [real_inner_comm (b _) v]
      exact b.sum_sq_inner_right v
    rw [← Finset.smul_sum, ← Finset.sum_smul, hs]
    simp only [mul_smul]
    congr 1
  have hcomm : ∑ i, (𝓕 G x) ![b i, b i] = L (𝓕 G x) := by simp [L]
  have hFG : L (𝓕 G x) = ∫ v : E, (𝐞 (-inner ℝ v x) : ℂ) • L (G v) := by
    rw [Real.fourier_eq]
    simp only [Circle.smul_def]
    rw [← ContinuousLinearMap.integral_comp_comm L (by simpa [Circle.smul_def] using hint)]
    congr 1; funext v
    simp [L, smul_apply, Finset.smul_sum]
  show ∑ i, (𝓕 G x) ![b i, b i] = _
  rw [hcomm, hFG]
  simp_rw [hL]
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [norm_neg, inner_neg_left, neg_neg, hgdef, smul_smul]
  congr 1
  push_cast
  ring_nf
  simp [Complex.I_sq]
end

lemma iteratedDeriv_fourierChar (i : ℕ) :
    iteratedDeriv i (fun r : ℝ => (𝐞 r : ℂ)) = fun r => (2 * π * Complex.I) ^ i * (𝐞 r : ℂ) := by
  induction i with
  | zero => funext r; simp
  | succ i ih =>
    rw [iteratedDeriv_succ, ih]
    funext r
    rw [deriv_const_mul_field']
    have h := (Real.hasDerivAt_fourierChar r).deriv
    simp only at h ⊢
    rw [h]
    ring

lemma norm_iteratedFDeriv_fourierChar (i : ℕ) (r : ℝ) :
    ‖iteratedFDeriv ℝ i (fun r : ℝ => (𝐞 r : ℂ)) r‖ = (2 * π) ^ i := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_fourierChar]
  simp [norm_pow, Complex.norm_I, abs_of_pos Real.pi_pos, Circle.norm_coe]

lemma contDiff_fourierChar_real : ContDiff ℝ ∞ (fun r : ℝ => (𝐞 r : ℂ)) := by
  refine contDiff_of_differentiable_iteratedDeriv fun m _ => ?_
  rw [iteratedDeriv_fourierChar]
  exact (differentiable_const _).mul (fun r => (Real.hasDerivAt_fourierChar r).differentiableAt)

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The derivatives of `(t, x) ↦ 𝐞 ⟪ξ, x⟫` are bounded by `(2π‖ξ‖)ⁱ`. -/
lemma norm_iteratedFDeriv_char_le (ξ : E) (i : ℕ) (q : ℝ × E) :
    ‖iteratedFDeriv ℝ i (fun q : ℝ × E => (𝐞 (inner ℝ ξ q.2) : ℂ)) q‖ ≤ (2 * π * ‖ξ‖) ^ i := by
  set ℓ : ℝ × E →L[ℝ] ℝ := (innerSL ℝ ξ).comp (ContinuousLinearMap.snd ℝ ℝ E) with hℓ
  have e : (fun q : ℝ × E => (𝐞 (inner ℝ ξ q.2) : ℂ)) = (fun r : ℝ => (𝐞 r : ℂ)) ∘ ℓ := by
    funext q; simp [hℓ]
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right ℓ contDiff_fourierChar_real q
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_iteratedFDeriv_fourierChar]
  have hn : ‖ℓ‖ ≤ ‖ξ‖ := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc ‖innerSL ℝ ξ‖ * ‖ContinuousLinearMap.snd ℝ ℝ E‖ ≤ ‖ξ‖ * 1 := by
          gcongr
          · exact (innerSL_apply_norm ℝ ξ).le
          · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => by
              simpa using norm_snd_le p
      _ = ‖ξ‖ := mul_one _
  calc (2 * π) ^ i * ‖ℓ‖ ^ i ≤ (2 * π) ^ i * ‖ξ‖ ^ i := by gcongr
    _ = (2 * π * ‖ξ‖) ^ i := (mul_pow _ _ _).symm
end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F]

/-- The derivatives of a time translate are bounded by those of the function. -/
lemma norm_iteratedFDeriv_timeShift_le (g : ℝ → F) (hg : ContDiff ℝ ∞ g) (r : ℝ) (j : ℕ)
    (q : ℝ × E) :
    ‖iteratedFDeriv ℝ j (fun q : ℝ × E => g (q.1 - r)) q‖ ≤ ‖iteratedDeriv j g (q.1 - r)‖ := by
  have e : (fun q : ℝ × E => g (q.1 - r)) = (fun s : ℝ => g (s - r)) ∘
      (ContinuousLinearMap.fst ℝ ℝ E) := by funext q; simp
  have hd : ContDiff ℝ ∞ fun s : ℝ => g (s - r) := hg.comp (contDiff_id.sub contDiff_const)
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hd q (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have h1 : ‖ContinuousLinearMap.fst ℝ ℝ E‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => by simpa using norm_fst_le p
  have h2 : ∏ _i : Fin j, ‖ContinuousLinearMap.fst ℝ ℝ E‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) h1
  calc _ ≤ ‖iteratedFDeriv ℝ j (fun s : ℝ => g (s - r)) q.1‖ * 1 :=
        mul_le_mul le_rfl h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) (norm_nonneg _)
    _ = ‖iteratedDeriv j g (q.1 - r)‖ := by
        rw [mul_one, iteratedFDeriv_comp_sub, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
end

/-- Polynomial factors from spatial derivatives are absorbed by additional Fourier decay. -/
lemma char_pow_mul_decay_le {E : Type*} [NormedAddCommGroup E] (ξ : E) (i N : ℕ) :
    (2 * π * ‖ξ‖) ^ i * (1 + ‖ξ‖) ^ (-((i + N : ℕ) : ℝ)) ≤
      (2 * π) ^ i * (1 + ‖ξ‖) ^ (-(N : ℝ)) := by
  have hp : 0 < 1 + ‖ξ‖ := by positivity
  calc
    _ ≤ (2 * π) ^ i * (1 + ‖ξ‖) ^ i * (1 + ‖ξ‖) ^ (-((i + N : ℕ) : ℝ)) := by
      rw [mul_pow]
      gcongr
      exact le_add_of_nonneg_left zero_le_one
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_natCast (1 + ‖ξ‖) i, ← Real.rpow_add hp]
      congr 2
      push_cast
      ring

section
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma contDiff_char_pair : ContDiff ℝ ∞ fun w : (ℝ × E) × (ℝ × E) =>
    (𝐞 (inner ℝ w.2.2 w.1.2) : ℂ) := by
  have hin : ContDiff ℝ ∞ fun w : (ℝ × E) × (ℝ × E) => (inner ℝ w.2.2 w.1.2 : ℝ) :=
    ContDiff.inner ℝ (contDiff_snd.comp contDiff_snd) (contDiff_snd.comp contDiff_fst)
  exact contDiff_fourierChar_real.comp hin
end

end FourierIntegral
