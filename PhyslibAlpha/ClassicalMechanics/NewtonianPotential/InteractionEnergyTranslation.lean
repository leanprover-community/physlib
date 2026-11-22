/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import PhyslibAlpha.ClassicalMechanics.NewtonianPotential.InteractionEnergyDefinite
public import PhyslibAlpha.ClassicalMechanics.NewtonianPotential.NewtonPotentialDeriv

/-!
# The interaction energy of a displaced density

## i. Overview

For Schwartz mass densities `ρ₁` and `ρ₂` on `Space 3` we study the Newtonian interaction energy
`W(ρ₁, τ_d ρ₂)` as a function of the displacement `d` of the second density. This function is
differentiable, its derivative in a direction `v` is `W(∂_v ρ₁, τ_d ρ₂)`, and its Laplacian is
`4πG` times the overlap of the two densities,

`Δ_d W(ρ₁, τ_d ρ₂) = 4πG ∫ ρ₁(x) ρ₂(x - d) dx`.

For `ρ₁ = ρ₂ = ρ` this determines the leading behaviour for small displacements of the
interaction energy of `ρ - τ_d ρ` with itself, independently of the profile of `ρ`.

## ii. Key results

- `interactionEnergy_sub_translateSchwartz_self` : `W(ρ - τ ρ, ρ - τ ρ) = 2 W(ρ, ρ) - 2 W(ρ, τ ρ)`.
- `fderiv_interactionEnergy_translateSchwartz_right` : the derivative with respect to the
  displacement.
- `laplacian_interactionEnergy_translateSchwartz_right` : the Laplacian with respect to the
  displacement.

## iii. Table of contents

- A. The difference of a density and its translate
- B. Differentiating under the integral
- C. The Laplacian with respect to the displacement

## iv. References

- None.
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.NewtonianPotential

open MeasureTheory Space Physlib Distribution
open scoped SchwartzMap LineDeriv

/-!

## A. The difference of a density and its translate

-/

/-- The interaction energy of the difference of a density and its translate with itself. -/
lemma interactionEnergy_sub_translateSchwartz_self (G : ℝ) (ρ : 𝓢(Space 3, ℝ))
    (a : EuclideanSpace ℝ (Fin 3)) :
    interactionEnergy G (ρ - translateSchwartz a ρ) (ρ - translateSchwartz a ρ) =
      2 * interactionEnergy G ρ ρ - 2 * interactionEnergy G ρ (translateSchwartz a ρ) := by
  rw [interactionEnergy_sub_sub, interactionEnergy_translateSchwartz]
  ring

/-!

## B. Differentiating under the integral

-/

/-- The interaction energy with a translated density as an integral over the potential of the
untranslated density. -/
lemma interactionEnergy_translateSchwartz_right (G : ℝ) (σ ρ : 𝓢(Space 3, ℝ)) (d : Space 3) :
    interactionEnergy G σ (translateSchwartz (basis.repr d) ρ) =
      ∫ y, σ (y + d) * newtonPotential G ρ y := by
  simp only [interactionEnergy_apply, newtonPotential_translateSchwartz,
    LinearIsometryEquiv.symm_apply_apply]
  rw [← integral_sub_right_eq_self (fun y : Space 3 => σ (y + d) * newtonPotential G ρ y) d]
  simp

/-- A translated Schwartz density times a Newtonian potential is integrable. -/
lemma integrable_add_mul_newtonPotential (G : ℝ) (σ ρ : 𝓢(Space 3, ℝ)) (d : Space 3) :
    Integrable (fun y : Space 3 => σ (y + d) * newtonPotential G ρ y) := by
  simpa [translateSchwartz_apply] using
    integrable_mul_newtonPotential G (translateSchwartz (basis.repr (-d)) σ) ρ

/-- A Newtonian potential times the derivative of a translated Schwartz density is
integrable. -/
lemma integrable_newtonPotential_smul_fderiv_add (G : ℝ) (σ ρ : 𝓢(Space 3, ℝ)) (d : Space 3) :
    Integrable (fun y : Space 3 => newtonPotential G ρ y • fderiv ℝ σ (y + d)) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_fderiv_sub_le σ
  obtain ⟨B, hB, hΦ⟩ := exists_abs_newtonPotential_le G ρ
  have hcont : Continuous (fun w : Space 3 => fderiv ℝ σ w) :=
    (σ.smooth 1).continuous_fderiv (by norm_num)
  refine Integrable.mono'
    ((integrable_one_add_norm_pow_four_inv.const_mul (C * (1 + ‖d‖) ^ 4)).const_mul B)
    ((continuous_newtonPotential G ρ).smul
      (hcont.comp (continuous_id.add continuous_const))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  have h := hb d (-y)
  rw [sub_neg_eq_add, norm_neg, add_comm] at h
  exact mul_le_mul (hΦ y) h (norm_nonneg _) hB

open Metric in
/-- The interaction energy with a translated density is differentiable in the displacement. -/
lemma hasFDerivAt_integral_add_mul_newtonPotential (G : ℝ) (σ ρ : 𝓢(Space 3, ℝ))
    (d₀ : Space 3) :
    HasFDerivAt (fun d : Space 3 => ∫ y, σ (y + d) * newtonPotential G ρ y)
      (∫ y, newtonPotential G ρ y • fderiv ℝ σ (y + d₀)) d₀ := by
  obtain ⟨C, hC, hb⟩ := exists_norm_fderiv_sub_le σ
  obtain ⟨B, hB, hΦ⟩ := exists_abs_newtonPotential_le G ρ
  have hσd : ∀ w : Space 3, HasFDerivAt σ (fderiv ℝ σ w) w := fun w =>
    ((σ.smooth 1).differentiable (by norm_num) w).hasFDerivAt
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun (d : Space 3) (y : Space 3) => σ (y + d) * newtonPotential G ρ y)
    (F' := fun (d : Space 3) (y : Space 3) => newtonPotential G ρ y • fderiv ℝ σ (y + d))
    (bound := fun y : Space 3 => B * (C * (2 + ‖d₀‖) ^ 4 * ((1 + ‖y‖) ^ 4)⁻¹))
    (ball_mem_nhds d₀ one_pos)
    (Filter.Eventually.of_forall fun d =>
      (integrable_add_mul_newtonPotential G σ ρ d).aestronglyMeasurable)
    (integrable_add_mul_newtonPotential G σ ρ d₀)
    (integrable_newtonPotential_smul_fderiv_add G σ ρ d₀).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y d hd => by
      rw [norm_smul, Real.norm_eq_abs]
      have hd' := one_add_norm_le_of_mem_ball hd
      have h := hb d (-y)
      rw [sub_neg_eq_add, norm_neg, add_comm] at h
      exact mul_le_mul (hΦ y) (h.trans (by gcongr)) (norm_nonneg _) hB)
    ((integrable_one_add_norm_pow_four_inv.const_mul (C * (2 + ‖d₀‖) ^ 4)).const_mul B)
    (Filter.Eventually.of_forall fun y d _ => by
      have h1 : HasFDerivAt (fun d : Space 3 => y + d) (ContinuousLinearMap.id ℝ (Space 3)) d :=
        (hasFDerivAt_id d).const_add y
      simpa using ((hσd (y + d)).comp d h1).mul_const (newtonPotential G ρ y))

/-- The derivative of the interaction energy with respect to the displacement of the second
density, in a direction `v`, is the interaction energy of the derivative of the first density
in the direction `v`. -/
lemma fderiv_interactionEnergy_translateSchwartz_right (G : ℝ) (σ ρ : 𝓢(Space 3, ℝ))
    (d v : Space 3) :
    fderiv ℝ (fun d : Space 3 => interactionEnergy G σ (translateSchwartz (basis.repr d) ρ)) d v =
      interactionEnergy G (∂_{v} σ) (translateSchwartz (basis.repr d) ρ) := by
  have hfun : (fun d : Space 3 => interactionEnergy G σ (translateSchwartz (basis.repr d) ρ)) =
      fun d => ∫ y, σ (y + d) * newtonPotential G ρ y :=
    funext fun d => interactionEnergy_translateSchwartz_right G σ ρ d
  rw [hfun, (hasFDerivAt_integral_add_mul_newtonPotential G σ ρ d).fderiv,
    interactionEnergy_translateSchwartz_right,
    ContinuousLinearMap.integral_apply (integrable_newtonPotential_smul_fderiv_add G σ ρ d)]
  congr 1 with y
  simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, mul_comm]

/-!

## C. The Laplacian with respect to the displacement

-/

/-- The Laplacian of the interaction energy with respect to the displacement of the second
density is `4πG` times the overlap of the two densities:
`Δ_d W(ρ₁, τ_d ρ₂) = 4πG ∫ ρ₁(x) ρ₂(x - d) dx`. -/
theorem laplacian_interactionEnergy_translateSchwartz_right (G : ℝ) (ρ₁ ρ₂ : 𝓢(Space 3, ℝ)) :
    Space.laplacian
        (fun d : Space 3 => interactionEnergy G ρ₁ (translateSchwartz (basis.repr d) ρ₂)) =
      fun d => 4 * Real.pi * G * ∫ x, ρ₁ x * ρ₂ (x - d) := by
  have hd : ∀ (i : Fin 3) (σ : 𝓢(Space 3, ℝ)),
      Space.deriv i
          (fun d : Space 3 => interactionEnergy G σ (translateSchwartz (basis.repr d) ρ₂)) =
        fun d => interactionEnergy G (∂_{basis i} σ) (translateSchwartz (basis.repr d) ρ₂) := by
    intro i σ
    funext d
    rw [Space.deriv_eq_fderiv_basis, fderiv_interactionEnergy_translateSchwartz_right]
  rw [Space.laplacian_eq_sum_snd_deriv]
  funext d
  simp_rw [hd]
  rw [← LinearMap.sum_apply, ← map_sum, ← SchwartzMap.laplacian_eq_sum basis ρ₁,
    interactionEnergy_laplacian_left]
  simp [translateSchwartz_apply]

end PhyslibAlpha.NewtonianPotential
