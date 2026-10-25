/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Physlib.ClassicalMechanics.EulerLagrange
public import Physlib.Mathematics.Calculus.ParametricIntegration

/-!
# First variation of the action

The first variation of `∫ L (τ, H, ∂τ H) dτ`.

## i. Overview

`H (s, τ)` is a smooth family of curves around `H (0, ·)`.
Along a smooth family fixing the endpoints, the derivative of the action is the integral of the
Euler-Lagrange covector `∂L/∂q - dₜ(∂L/∂q̇)` against the variation field.

## ii. Key results

- `contDiff_action_integrand`: smoothness of the action integrand
- `fderiv_action_integrand_apply`: first variation of the integrand, the Euler-Lagrange term
  plus a total `τ`-derivative
- `hasDerivAt_integral_variation`: first variation of the action

## iii. Table of contents

- A. First variation

## iv. References

* I. Terek, Introductory Variational Calculus on Manifolds. [ref: terek_variational_manifolds]
* L. D. Landau and E. M. Lifshitz, Mechanics. [ref: landau_mechanics]
-/

@[expose] public section

open intervalIntegral Filter Topology
open scoped ContDiff Manifold
namespace ClassicalMechanics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : ℝ × ℝ → E}

/-!
## A. First variation
-/

/-- The `s`-derivative of the integrand of the action splits into the Euler-Lagrange term and
a total `τ`-derivative. -/
lemma fderiv_action_integrand_apply (S : LagrangianSystem 𝓘(ℝ, E) ⟨E⟩) (t₀ : Time)
    (hH : ContDiff ℝ ∞ H) (τ : ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ ↦ S.coord t₀ (p.2, H p, fderiv ℝ H p (0, 1))) (0, τ) (1, 0) =
      eulerLagrange S t₀ (fun σ ↦ H (0, σ)) τ (fderiv ℝ H (0, τ) (1, 0)) +
        (deriv (canonicalMomentum S t₀ fun σ ↦ H (0, σ)) τ
            (fderiv ℝ H (0, τ) (1, 0)) +
          canonicalMomentum S t₀ (fun σ ↦ H (0, σ)) τ
            (deriv (fun σ ↦ fderiv ℝ H (0, σ) (1, 0)) τ)) := by
  have hLd : Differentiable ℝ (S.coord t₀) := (S.contDiff_coord t₀).differentiable (by simp)
  have hHd : Differentiable ℝ H := hH.differentiable (by simp)
  have hφ := (hasFDerivAt_snd (p := ((0 : ℝ), τ))).prodMk
    ((hHd _).hasFDerivAt.prodMk
      (((hH.fderiv_right (m := ∞) (by simp)).clm_apply
        (contDiff_const (c := ((0 : ℝ), (1 : ℝ))))).differentiable (by simp) _).hasFDerivAt)
  refine (congrArg (· (1, 0)) ((hLd _).hasFDerivAt.comp (0, τ) hφ).fderiv).trans ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_snd']
  rw [← deriv_fderiv_apply_comm (hH.of_le (by simp)).contDiffAt, fderiv_apply_zero_prod (hLd _)]
  simp only [eulerLagrange, canonicalMomentum, sub_apply,
    show deriv (fun σ ↦ H (0, σ)) τ = _ from fderiv_curry_snd H 0 τ (hHd _) 1]
  abel

/-- The integrand `L(τ, H, ∂τ H)` of the action is smooth. -/
lemma contDiff_action_integrand (S : LagrangianSystem 𝓘(ℝ, E) ⟨E⟩) (t₀ : Time)
    (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ S.coord t₀ (p.2, H p, fderiv ℝ H p (0, 1)) :=
  (S.contDiff_coord t₀).comp (contDiff_snd.prodMk (hH.prodMk
    ((hH.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)))

/-- First variation of `∫ L(τ, H, ∂τ H) dτ` along a variation fixing the endpoints. -/
lemma hasDerivAt_integral_variation (S : LagrangianSystem 𝓘(ℝ, E) ⟨E⟩) (t₀ : Time)
    (hH : ContDiff ℝ ∞ H)
    (T : ℝ) (h0 : ∀ s, H (s, 0) = H (0, 0)) (hT : ∀ s, H (s, T) = H (0, T)) :
    HasDerivAt
      (fun s ↦ ∫ τ in (0 : ℝ)..T, S.coord t₀ (τ, H (s, τ), fderiv ℝ H (s, τ) (0, 1)))
      (∫ τ in (0 : ℝ)..T,
        eulerLagrange S t₀ (fun σ ↦ H (0, σ)) τ (fderiv ℝ H (0, τ) (1, 0))) 0 := by
  set q : ℝ → E := fun σ ↦ H (0, σ)
  set V : ℝ → E := fun σ ↦ fderiv ℝ H (0, σ) (1, 0)
  have hVs : ContDiff ℝ ∞ V :=
    ((hH.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).comp
      (contDiff_const.prodMk contDiff_id)
  have hqs : ContDiff ℝ ∞ q := hH.comp (contDiff_const.prodMk contDiff_id)
  have hL := S.contDiff_coord t₀
  have hq' := (contDiff_infty_iff_deriv.1 hqs).2
  have hPvs : ContDiff ℝ ∞ (canonicalMomentum S t₀ q) := by unfold canonicalMomentum; fun_prop
  have hP1 : ContDiff ℝ 1 (canonicalMomentum S t₀ q) := hPvs.of_le (by simp)
  have hV1 : ContDiff ℝ 1 V := hVs.of_le (by simp)
  have hc : Continuous fun τ ↦ deriv (canonicalMomentum S t₀ q) τ (V τ) +
      canonicalMomentum S t₀ q τ (deriv V τ) :=
    ((hP1.continuous_deriv le_rfl).clm_apply hV1.continuous).add
      (hP1.continuous.clm_apply (hV1.continuous_deriv le_rfl))
  have hbp := integral_eq_sub_of_hasDerivAt (f := fun τ ↦ canonicalMomentum S t₀ q τ (V τ))
    (fun τ _ ↦ (hP1.differentiable one_ne_zero τ).hasDerivAt.clm_apply
      (hV1.differentiable one_ne_zero τ).hasDerivAt)
    (hc.intervalIntegrable 0 T)
  rw [show V 0 = 0 by simp [V, ← fderiv_curry_fst H 0 0 (hH.differentiable (by simp) _), h0],
    show V T = 0 by simp [V, ← fderiv_curry_fst H 0 T (hH.differentiable (by simp) _), hT]] at hbp
  refine (hasDerivAt_intervalIntegral_of_contDiff
    ((contDiff_action_integrand S t₀ hH).of_le (by simp)) 0 T 0).congr_deriv ?_
  simp_rw [fderiv_action_integrand_apply S t₀ hH]
  rw [integral_add (((contDiff_eulerLagrange hqs).continuous.clm_apply
    hVs.continuous).intervalIntegrable _ _)
    (hc.intervalIntegrable _ _), hbp]
  simp [V]

end ClassicalMechanics
