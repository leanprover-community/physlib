/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.SpaceAndTime.Space.Derivatives.Curl
/-!

# Translations on space

We define translations on space, and how translations act on distributions.
Translations for part of the Poincaré group.

-/

section

variable
  {𝕜} [NontriviallyNormedField 𝕜]
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Y} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
  {ι : Type*} [Fintype ι] {Y' : ι → Type*} [∀ i, NormedAddCommGroup (Y' i)]
  [∀ i, NormedSpace 𝕜 (Y' i)] {Φ : X → ∀ i, Y' i} {x : X}

namespace Space

/-!

## Translations of distributions

-/

open Distribution
open SchwartzMap

/-- The continuous linear map translating Schwartz maps. -/
noncomputable def translateSchwartz {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) :
    𝓢(Space d, X) →L[ℝ] 𝓢(Space d, X) :=
  SchwartzMap.compCLM (𝕜 := ℝ)
      (g := fun x => x - basis.repr.symm a)
      (by
        apply Function.HasTemperateGrowth.of_fderiv (k := 1) (C := 1 + ‖a‖)
        · have hx : (fderiv ℝ (fun (x : Space d) => (x - basis.repr.symm a: Space d))) =
              fun _ => ContinuousLinearMap.id ℝ (Space d) := by
            funext x
            simp only
            erw [fderiv_sub]
            simp only [fderiv_id', fderiv_fun_const, Pi.zero_apply, sub_zero]
            fun_prop
            fun_prop
          rw [hx]
          exact Function.HasTemperateGrowth.const
              (ContinuousLinearMap.id ℝ (Space d))
        · fun_prop
        · intro x
          simp only [pow_one]
          change ‖x - basis.repr.symm a‖ ≤ _
          trans ‖x‖ + ‖a‖
          · apply (norm_sub_le x (basis.repr.symm a)).trans
            simp
          simp [mul_add, add_mul]
          trans 1 + (‖x‖ + ‖a‖)
          · simp
          trans (1 + (‖x‖ + ‖a‖)) + ‖x‖ * ‖a‖
          · simp
            positivity
          ring_nf
          rfl) (by
          simp only
          use 1, (1 + ‖a‖)
          intro x
          simp only [pow_one]
          apply (norm_le_norm_add_norm_sub' x (basis.repr.symm a)).trans
          trans 1 + (‖a‖ + ‖x - basis.repr.symm a‖)
          · simp
          trans (1 + (‖a‖ + ‖x - basis.repr.symm a‖)) + ‖a‖ * ‖x - basis.repr.symm a‖
          · simp
            positivity
          ring_nf
          rfl)

@[simp]
lemma translateSchwartz_apply {d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (η : 𝓢(Space d, X)) (x : Space d) :
    translateSchwartz a η x = η (x - basis.repr.symm a) := rfl

lemma translateSchwartz_coe_eq {d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (η : 𝓢(Space d, X)) :
    (translateSchwartz a η : Space d → X) = fun x => η (x - basis.repr.symm a) := by
  ext
  simp

/-- The continuous linear map translating distributions. -/
noncomputable def distTranslate {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) :
    ((Space d) →d[ℝ] X) →ₗ[ℝ] ((Space d) →d[ℝ] X) where
  toFun T := T.comp (translateSchwartz (-a))
  map_add' T1 T2 := by
    ext η
    simp
  map_smul' c T := by
    simp

lemma distTranslate_apply {d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (T : (Space d) →d[ℝ] X) (η : 𝓢(Space d, ℝ)) :
    distTranslate a T η = T (translateSchwartz (-a) η) := rfl

open InnerProductSpace

@[simp]
lemma distTranslate_distGrad {d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (T : (Space d) →d[ℝ] ℝ) :
    distGrad (distTranslate a T) = distTranslate a (distGrad T) := by
  apply distGrad_eq_of_inner
  intro η y
  rw [distTranslate_apply, distGrad_inner_eq]
  rw [fderivD_apply, fderivD_apply, distTranslate_apply]
  congr 2
  ext x
  simp only [translateSchwartz_apply, map_neg, sub_neg_eq_add,
    LinearIsometryEquiv.symm_apply_apply]
  change fderiv ℝ η (x + basis.repr.symm a) y = fderiv ℝ _ x y
  rw [translateSchwartz_coe_eq]
  simp only [map_neg, sub_neg_eq_add]
  rw [fderiv_comp_add_right]

open MeasureTheory
lemma distTranslate_ofFunction {d : ℕ} (a : EuclideanSpace ℝ (Fin d.succ))
    (f : Space d.succ → X) (hf : IsDistBounded f) :
    distTranslate a (distOfFunction f hf) =
    distOfFunction (fun x => f (x - basis.repr.symm a))
    (IsDistBounded.comp_add_right hf (- basis.repr.symm a)) := by
  ext η
  rw [distTranslate_apply, distOfFunction_apply, distOfFunction_apply]
  trans ∫ (x : Space d.succ), η ((x - basis.repr.symm a) + basis.repr.symm a) •
    f (x - basis.repr.symm a); swap
  · simp
  let f' := fun x : Space d.succ => η (x + basis.repr.symm a) • f (x)
  change _ = ∫ (x : Space d.succ), f' (x - basis.repr.symm a)
  rw [MeasureTheory.integral_sub_right_eq_self]
  congr
  funext x
  simp [f']

@[simp]
lemma distDiv_distTranslate {d : ℕ} (a : EuclideanSpace ℝ (Fin d))
    (T : (Space d) →d[ℝ] EuclideanSpace ℝ (Fin d)) :
    distDiv (distTranslate a T) = distTranslate a (distDiv T) := by
  ext η
  rw [distDiv_apply_eq_sum_fderivD]
  rw [distTranslate_apply, distDiv_apply_eq_sum_fderivD]
  congr
  funext i
  rw [fderivD_apply, fderivD_apply, distTranslate_apply]
  simp only [PiLp.neg_apply, neg_inj]
  have h1 : ((translateSchwartz (-a)) ((SchwartzMap.evalCLM ℝ (Space d) ℝ (basis i))
      ((fderivCLM ℝ (Space d) ℝ) η))) =
      ((SchwartzMap.evalCLM ℝ (Space d) ℝ (basis i))
        ((fderivCLM ℝ (Space d) ℝ) ((translateSchwartz (-a)) η))) := by
    ext x
    rw [translateSchwartz_apply]
    simp only [map_neg, sub_neg_eq_add]
    change fderiv ℝ η (x + basis.repr.symm a) (basis i) = fderiv ℝ _ x (basis i)
    rw [translateSchwartz_coe_eq]
    simp only [map_neg, sub_neg_eq_add]
    rw [fderiv_comp_add_right]
  rw [h1]

end Space
