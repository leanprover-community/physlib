/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Physlib.Mathematics.Calculus.ParametricIntegration
public import Physlib.Mathematics.Calculus.PartialDerivatives
public import Physlib.Mathematics.VariationalCalculus.Interval

/-!
# First variation of the action

The Euler-Lagrange covector and the first variation of `∫ L (τ, H, ∂τ H) dτ`.

## i. Overview

Along a smooth family fixing the endpoints, the derivative of the action is the integral of the
Euler-Lagrange covector `∂L/∂q - dₜ(∂L/∂q̇)` against the variation field.

## ii. Key results

- `eulerLagrange`
- `hasDerivAt_integral_variation`

## iii. Table of contents

- A. The Euler-Lagrange covector
- B. First variation

## iv. References

* I. Terek, Introductory Variational Calculus on Manifolds. [ref: terek_variational_manifolds]
* L. D. Landau and E. M. Lifshitz, Mechanics. [ref: landau_mechanics]
-/

@[expose] public section

open Set MeasureTheory intervalIntegral Filter Topology
open scoped ContDiff
namespace ClassicalMechanics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : ℝ × ℝ → E}

/-!
## A. The Euler-Lagrange covector
-/

/-- The Euler-Lagrange covector `∂L/∂q - dₜ(∂L/∂q̇)` of a curve `q`. -/
noncomputable def eulerLagrange (L : ℝ × E × E → ℝ) (q : ℝ → E) (τ : ℝ) : E →L[ℝ] ℝ :=
  fderiv ℝ (fun x ↦ L (τ, x, deriv q τ)) (q τ) -
    deriv (fun σ ↦ fderiv ℝ (fun v ↦ L (σ, q σ, v)) (deriv q σ)) τ

/-- The Euler-Lagrange covector of a smooth curve is smooth. -/
lemma contDiff_eulerLagrange {L : ℝ × E × E → ℝ} (hL : ContDiff ℝ ∞ L) {q : ℝ → E}
    (hq : ContDiff ℝ ∞ q) : ContDiff ℝ ∞ (eulerLagrange L q) :=
  (contDiff_fderiv_partial_x hL hq).sub
    (contDiff_infty_iff_deriv.1 (contDiff_fderiv_partial_v hL hq)).2

/-- The Euler-Lagrange covector at `τ` depends only on the germ of the curve at `τ`. -/
lemma eulerLagrange_congr {L : ℝ × E × E → ℝ} {q g : ℝ → E} {τ : ℝ} (h : q =ᶠ[𝓝 τ] g) :
    eulerLagrange L q τ = eulerLagrange L g τ := by
  unfold eulerLagrange
  rw [h.deriv_eq, h.eq_of_nhds]
  congr 1
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [h.eventuallyEq_nhds] with σ hσ
  rw [hσ.eq_of_nhds, hσ.deriv_eq]

/-- The Euler-Lagrange covector only depends on the Lagrangian near the curve. -/
lemma eulerLagrange_congr_lagrangian {L L' : ℝ × E × E → ℝ} {q : ℝ → E} {τ : ℝ} {N : Set E}
    (hN : IsOpen N) (hq : ∀ᶠ σ in 𝓝 τ, q σ ∈ N) (h : ∀ p : ℝ × E × E, p.2.1 ∈ N → L p = L' p) :
    eulerLagrange L q τ = eulerLagrange L' q τ := by
  unfold eulerLagrange
  have hτ : q τ ∈ N := hq.self_of_nhds
  have h1 : (fun y ↦ L (τ, y, deriv q τ)) =ᶠ[𝓝 (q τ)] fun y ↦ L' (τ, y, deriv q τ) := by
    filter_upwards [hN.mem_nhds hτ] with y hy using h _ hy
  have h2 : (fun σ ↦ fderiv ℝ (fun v ↦ L (σ, q σ, v)) (deriv q σ)) =ᶠ[𝓝 τ]
      fun σ ↦ fderiv ℝ (fun v ↦ L' (σ, q σ, v)) (deriv q σ) := by
    filter_upwards [hq] with σ hσ
    exact congrArg (fun f ↦ fderiv ℝ f (deriv q σ)) (funext fun v ↦ h _ hσ)
  rw [h1.fderiv_eq, h2.deriv_eq]

/-!
## B. First variation
-/

/-- The `s`-derivative of the integrand of the action splits into the Euler-Lagrange term and
a total `τ`-derivative. -/
lemma fderiv_integrand_apply {L : ℝ × E × E → ℝ} (hL : ContDiff ℝ ∞ L) (hH : ContDiff ℝ ∞ H)
    (τ : ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ ↦ L (p.2, H p, fderiv ℝ H p (0, 1))) (0, τ) (1, 0) =
      eulerLagrange L (fun σ ↦ H (0, σ)) τ (fderiv ℝ H (0, τ) (1, 0)) +
        (deriv (fun σ ↦ fderiv ℝ (fun v ↦ L (σ, H (0, σ), v)) (deriv (fun σ' ↦ H (0, σ')) σ)) τ
            (fderiv ℝ H (0, τ) (1, 0)) +
          fderiv ℝ (fun v ↦ L (τ, H (0, τ), v)) (deriv (fun σ' ↦ H (0, σ')) τ)
            (deriv (fun σ ↦ fderiv ℝ H (0, σ) (1, 0)) τ)) := by
  have hLd : Differentiable ℝ L := hL.differentiable (by simp)
  have hGs : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ fderiv ℝ H p (0, 1) :=
    (hH.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hφ : HasFDerivAt (fun p : ℝ × ℝ ↦ (p.2, H p, fderiv ℝ H p (0, 1)))
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod ((fderiv ℝ H (0, τ)).prod
        (fderiv ℝ (fun p : ℝ × ℝ ↦ fderiv ℝ H p (0, 1)) (0, τ)))) (0, τ) :=
    (hasFDerivAt_snd).prodMk ((hH.differentiable (by simp) _).hasFDerivAt.prodMk
      ((hGs.differentiable (by simp) _).hasFDerivAt))
  have h1 : fderiv ℝ (fun p : ℝ × ℝ ↦ L (p.2, H p, fderiv ℝ H p (0, 1))) (0, τ) =
      (fderiv ℝ L (τ, H (0, τ), fderiv ℝ H (0, τ) (0, 1))).comp
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod ((fderiv ℝ H (0, τ)).prod
          (fderiv ℝ (fun p : ℝ × ℝ ↦ fderiv ℝ H p (0, 1)) (0, τ)))) :=
    ((hLd _).hasFDerivAt.comp (0, τ) hφ).fderiv
  rw [h1]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_snd']
  rw [← deriv_fderiv_snd hH 0 τ, fderiv_apply_zero_prod hLd]
  simp only [eulerLagrange, sub_apply, fderiv_snd_apply hH 0]
  abel

/-- First variation of `∫ L(τ, H, ∂τ H) dτ` along a variation fixing the endpoints. -/
lemma hasDerivAt_integral_variation {L : ℝ × E × E → ℝ} (hL : ContDiff ℝ ∞ L)
    (hH : ContDiff ℝ ∞ H) (T : ℝ) (h0 : ∀ s, H (s, 0) = H (0, 0))
    (hT : ∀ s, H (s, T) = H (0, T)) :
    HasDerivAt (fun s ↦ ∫ τ in (0 : ℝ)..T, L (τ, H (s, τ), fderiv ℝ H (s, τ) (0, 1)))
      (∫ τ in (0 : ℝ)..T, eulerLagrange L (fun σ ↦ H (0, σ)) τ (fderiv ℝ H (0, τ) (1, 0))) 0 := by
  set q : ℝ → E := fun σ ↦ H (0, σ)
  have hdH : ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (m := ∞) (by simp)
  have hGs : ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ fderiv ℝ H p (0, 1) := hdH.clm_apply contDiff_const
  set V : ℝ → E := fun σ ↦ fderiv ℝ H (0, σ) (1, 0)
  have hVs : ContDiff ℝ ∞ V :=
    (hdH.comp (contDiff_const.prodMk contDiff_id)).clm_apply contDiff_const
  have hqs : ContDiff ℝ ∞ q := hH.comp (contDiff_const.prodMk contDiff_id)
  have hPvs := contDiff_fderiv_partial_v hL hqs
  set Pv : ℝ → E →L[ℝ] ℝ := fun σ ↦ fderiv ℝ (fun v ↦ L (σ, q σ, v)) (deriv q σ)
  have hbp := integral_by_parts_covector hPvs hVs T
  have hV0 : V 0 = 0 := fderiv_fst_apply_eq_zero hH h0
  have hVT : V T = 0 := fderiv_fst_apply_eq_zero hH hT
  rw [hV0, hVT] at hbp
  set F : ℝ × ℝ → ℝ := fun p ↦ L (p.2, H p, fderiv ℝ H p (0, 1))
  have hFs : ContDiff ℝ ∞ F := hL.comp (contDiff_snd.prodMk (hH.prodMk hGs))
  have hmain := hasDerivAt_intervalIntegral_of_contDiff (hFs.of_le (by simp)) 0 T 0
  have key : ∀ τ, fderiv ℝ F (0, τ) (1, 0) =
      eulerLagrange L q τ (V τ) + (deriv Pv τ (V τ) + Pv τ (deriv V τ)) :=
    fderiv_integrand_apply hL hH
  have hval : ∫ τ in (0 : ℝ)..T, fderiv ℝ F (0, τ) (1, 0) =
      ∫ τ in (0 : ℝ)..T, eulerLagrange L q τ (V τ) := by
    symm
    have hc1 : Continuous fun τ : ℝ ↦ fderiv ℝ F (0, τ) (1, 0) :=
      ((hFs.continuous_fderiv (by simp)).comp (by fun_prop)).clm_apply continuous_const
    have hc2 : Continuous fun τ : ℝ ↦ deriv Pv τ (V τ) + Pv τ (deriv V τ) :=
      ((hPvs.continuous_deriv (by simp)).clm_apply hVs.continuous).add
        (hPvs.continuous.clm_apply (hVs.continuous_deriv (by simp)))
    have hsub : ∀ τ, eulerLagrange L q τ (V τ) =
        fderiv ℝ F (0, τ) (1, 0) - (deriv Pv τ (V τ) + Pv τ (deriv V τ)) :=
      fun τ ↦ eq_sub_of_add_eq (key τ).symm
    simp_rw [hsub]
    rw [intervalIntegral.integral_sub (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
      hbp]
    simp
  exact hmain.congr_deriv hval

end ClassicalMechanics
