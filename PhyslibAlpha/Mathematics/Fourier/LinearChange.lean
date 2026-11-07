/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!

# The Fourier transform under a linear change of variables

Composition with the inverse transpose of a linear equivalence turns into evaluation of the
transform at the image point.

## i. Overview

For a linear equivalence `L` of a finite dimensional inner product space the map `A = (L⁻¹)ᵀ` is
again a linear equivalence. The Fourier transform of `f ∘ A` at `ξ` is `|det L|` times the
transform of `f` at `L ξ`. The proof moves the integral along `A` with the Haar measure scaling
and uses `⟨A⁻¹ y, ξ⟩ = ⟨y, L ξ⟩`.

## ii. Key results

- `Fourier.invTranspose` : the inverse transpose of a linear equivalence.
- `Fourier.fourier_comp_invTranspose` : the transform of `f ∘ (L⁻¹)ᵀ`.
- `Fourier.fourier_comp_isometry` : the transform commutes with linear isometries.
- `Fourier.fourier_comp_add_right` : the transform of a translate.

## iii. Table of contents

- A. The inverse transpose
- B. The transform
- C. Isometries
- D. Translations

## iv. References

None.

## A. The inverse transpose

- `Fourier.det_adjoint` : the determinant of the adjoint.
- `Fourier.invTranspose` : the inverse transpose of a linear equivalence.

## B. The transform

- `Fourier.fourier_comp_invTranspose` : the transform of `f ∘ (L⁻¹)ᵀ`.

## C. Isometries

- `Fourier.fourier_eq_complex` : the transform of a complex valued function.
- `Fourier.fourier_comp_isometry` : the transform commutes with linear isometries.

## D. Translations

- `Fourier.fourier_comp_add_right` : the transform of a translate.
-/

@[expose] public section

noncomputable section

open scoped FourierTransform InnerProductSpace
open MeasureTheory Module

namespace Fourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [MeasurableSpace V] [BorelSpace V] in
/-- The determinant of the adjoint. -/
lemma det_adjoint (f : V →ₗ[ℝ] V) : LinearMap.det (LinearMap.adjoint f) = LinearMap.det f := by
  let b := stdOrthonormalBasis ℝ V
  rw [← LinearMap.det_toMatrix b.toBasis, ← LinearMap.det_toMatrix b.toBasis,
    LinearMap.toMatrix_adjoint, Matrix.det_conjTranspose]
  simp

/-- The inverse transpose of a linear equivalence for the inner product. -/
def invTranspose (L : V ≃L[ℝ] V) : V ≃L[ℝ] V :=
  (LinearEquiv.ofLinearMap (LinearMap.adjoint L.symm.toLinearMap) (LinearMap.adjoint L.toLinearMap)
    (by rw [← LinearMap.adjoint_comp]; simp)
    (by rw [← LinearMap.adjoint_comp]; simp)).toContinuousLinearEquiv

omit [MeasurableSpace V] [BorelSpace V] in
lemma invTranspose_symm_apply (L : V ≃L[ℝ] V) (x : V) :
    (invTranspose L).symm x = LinearMap.adjoint L.toLinearMap x := rfl

omit [MeasurableSpace V] [BorelSpace V] in
lemma inner_invTranspose_symm (L : V ≃L[ℝ] V) (x y : V) :
    inner ℝ ((invTranspose L).symm x) y = inner ℝ x (L y) := by
  rw [invTranspose_symm_apply, LinearMap.adjoint_inner_left]
  rfl

omit [MeasurableSpace V] [BorelSpace V] in
lemma abs_det_invTranspose (L : V ≃L[ℝ] V) :
    |LinearMap.det (invTranspose L : V →ₗ[ℝ] V)| = |LinearMap.det (L : V →ₗ[ℝ] V)|⁻¹ := by
  have : (invTranspose L : V →ₗ[ℝ] V) = LinearMap.adjoint L.symm.toLinearMap := rfl
  rw [this, det_adjoint, ← abs_inv]
  congr 1
  have h := LinearMap.det_comp (L.symm.toLinearMap) (L.toLinearMap)
  have h2 : L.symm.toLinearMap ∘ₗ L.toLinearMap = LinearMap.id := by ext; simp
  rw [h2, LinearMap.det_id] at h
  exact eq_inv_of_mul_eq_one_left h.symm

/-- **Fourier transform and a linear change of variables.** Composition with the inverse
transpose of `L` turns into evaluation at `L ξ` and the factor `|det L|`. -/
lemma fourier_comp_invTranspose (L : V ≃L[ℝ] V) (f : V → E) (ξ : V) :
    𝓕 (f ∘ invTranspose L) ξ = |LinearMap.det (L : V →ₗ[ℝ] V)| • 𝓕 f (L ξ) := by
  set A := invTranspose L with hA
  have hL : LinearMap.det (L : V →ₗ[ℝ] V) ≠ 0 :=
    (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero
  have hdet : LinearMap.det (A : V →ₗ[ℝ] V) ≠ 0 := by
    intro h
    have := abs_det_invTranspose L
    rw [← hA, h, abs_zero] at this
    exact hL (abs_eq_zero.1 (inv_eq_zero.1 this.symm))
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure V) hdet
  set F : V → E := fun y => (𝐞 (-inner ℝ (A.symm y) ξ)) • f y with hF
  have h1 : 𝓕 (f ∘ A) ξ = ∫ x, F (A x) := by
    rw [Real.fourier_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [hF]
  have h2 : ∫ x, F (A x) = ∫ y, F y ∂(Measure.map (A : V →ₗ[ℝ] V) volume) :=
    (A.toHomeomorph.measurableEmbedding.integral_map F).symm
  rw [h1, h2, hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)]
  have h3 : |(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| = |LinearMap.det (L : V →ₗ[ℝ] V)| := by
    rw [abs_inv, hA, abs_det_invTranspose, inv_inv]
  rw [h3, Real.fourier_eq]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [hF]
  rw [hA, inner_invTranspose_symm]

/-- The Fourier transform of a complex valued function is the explicit integral. -/
lemma fourier_eq_complex {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] (f : V → ℂ) (ξ : V) :
    𝓕 f ξ = ∫ x, (𝐞 (-inner ℝ x ξ) : ℂ) • f x := by
  rw [Real.fourier_eq]
  simp [Circle.smul_def]

section Isometry

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [MeasurableSpace W]
  [BorelSpace W] [FiniteDimensional ℝ W]

/-- The Fourier transform commutes with linear isometries. -/
lemma fourier_comp_isometry (A : V ≃ₗᵢ[ℝ] W) (f : W → ℂ) (ξ : V) :
    𝓕 (f ∘ A) ξ = 𝓕 f (A ξ) := by
  rw [fourier_eq_complex, fourier_eq_complex]
  have h := A.measurePreserving.integral_comp' (f := A.toMeasurableEquiv)
    (fun y : W => (𝐞 (-inner ℝ y (A ξ)) : ℂ) • f y)
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [LinearIsometryEquiv.inner_map_map]

end Isometry

section Translation

/-- The Fourier transform turns translation into a phase. -/
lemma fourier_comp_add_right (f : V → ℂ) (q ζ : V) :
    𝓕 (fun v => f (v + q)) ζ = 𝐞 (inner ℝ q ζ) • 𝓕 f ζ := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have h := integral_add_right_eq_self (μ := volume)
    (fun w : V => (𝐞 (-inner ℝ (w - q) ζ) : Circle) • f w) q
  simp only [add_sub_cancel_right] at h
  rw [h]
  simp only [Circle.smul_def, smul_eq_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  have : (𝐞 (-inner ℝ (w - q) ζ) : ℂ) = (𝐞 (inner ℝ q ζ) : ℂ) * (𝐞 (-inner ℝ w ζ) : ℂ) := by
    rw [inner_sub_left, show -(inner ℝ w ζ - inner ℝ q ζ) = inner ℝ q ζ + -inner ℝ w ζ by ring,
      Real.fourierChar_apply, Real.fourierChar_apply, Real.fourierChar_apply, ← Complex.exp_add]
    push_cast
    ring_nf
  show (𝐞 (-inner ℝ (w - q) ζ) : ℂ) * f w = (𝐞 (inner ℝ q ζ) : ℂ) * ((𝐞 (-inner ℝ w ζ) : ℂ) * f w)
  rw [this]
  ring

end Translation

end Fourier
