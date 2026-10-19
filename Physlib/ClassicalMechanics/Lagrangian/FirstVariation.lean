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

- `canonicalMomentum`: the canonical momentum of a curve
- `eulerLagrange`: the Euler-Lagrange covector of a curve
- `contDiff_eulerLagrange`: smoothness of the Euler-Lagrange covector
- `eulerLagrange_congr`: dependence on the germ of the curve only
- `eulerLagrange_congr_lagrangian`: dependence on the Lagrangian near the curve only
- `fderiv_integrand_apply`: splitting of the `s`-derivative of the integrand
- `hasDerivAt_integral_variation`: first variation of the action

## iii. Table of contents

- A. Canonical momentum and the Euler-Lagrange covector
- B. First variation

## iv. References

* I. Terek, Introductory Variational Calculus on Manifolds. [ref: terek_variational_manifolds]
* L. D. Landau and E. M. Lifshitz, Mechanics. [ref: landau_mechanics]
-/

@[expose] public section

open intervalIntegral Filter Topology
open scoped ContDiff
namespace ClassicalMechanics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : ℝ × ℝ → E}

/-!
## A. Canonical momentum and the Euler-Lagrange covector
-/

/-- The canonical momentum `∂L/∂q̇` of a curve `q`. -/
noncomputable def canonicalMomentum (L : ℝ × E × E → ℝ) (q : ℝ → E) (τ : ℝ) : E →L[ℝ] ℝ :=
  fderiv ℝ (fun v ↦ L (τ, q τ, v)) (deriv q τ)

/-- The Euler-Lagrange covector `∂L/∂q - dₜ(∂L/∂q̇)` of a curve `q`. -/
noncomputable def eulerLagrange (L : ℝ × E × E → ℝ) (q : ℝ → E) (τ : ℝ) : E →L[ℝ] ℝ :=
  fderiv ℝ (fun x ↦ L (τ, x, deriv q τ)) (q τ) - deriv (canonicalMomentum L q) τ

/-- The Euler-Lagrange covector of a smooth curve is smooth. -/
lemma contDiff_eulerLagrange {L : ℝ × E × E → ℝ} (hL : ContDiff ℝ ∞ L) {q : ℝ → E}
    (hq : ContDiff ℝ ∞ q) : ContDiff ℝ ∞ (eulerLagrange L q) :=
  (contDiff_fderiv_partial_x hL hq).sub
    (contDiff_infty_iff_deriv.1 (contDiff_fderiv_partial_v hL hq)).2

/-- The Euler-Lagrange covector at `τ` depends only on the germ of the curve at `τ`. -/
lemma eulerLagrange_congr {L : ℝ × E × E → ℝ} {q g : ℝ → E} {τ : ℝ} (h : q =ᶠ[𝓝 τ] g) :
    eulerLagrange L q τ = eulerLagrange L g τ := by
  unfold eulerLagrange canonicalMomentum
  rw [h.deriv_eq, h.eq_of_nhds]
  congr 1
  refine EventuallyEq.deriv_eq ?_
  filter_upwards [h.eventuallyEq_nhds] with σ hσ
  rw [hσ.eq_of_nhds, hσ.deriv_eq]

/-- The Euler-Lagrange covector only depends on the Lagrangian near the curve. -/
lemma eulerLagrange_congr_lagrangian {L L' : ℝ × E × E → ℝ} {q : ℝ → E} {τ : ℝ} {N : Set E}
    (hN : IsOpen N) (hq : ∀ᶠ σ in 𝓝 τ, q σ ∈ N) (h : ∀ p : ℝ × E × E, p.2.1 ∈ N → L p = L' p) :
    eulerLagrange L q τ = eulerLagrange L' q τ := by
  unfold eulerLagrange canonicalMomentum
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
        (deriv (canonicalMomentum L fun σ ↦ H (0, σ)) τ
            (fderiv ℝ H (0, τ) (1, 0)) +
          canonicalMomentum L (fun σ ↦ H (0, σ)) τ
            (deriv (fun σ ↦ fderiv ℝ H (0, σ) (1, 0)) τ)) := by
  have hLd : Differentiable ℝ L := hL.differentiable (by simp)
  have hφ := (hasFDerivAt_snd (p := ((0 : ℝ), τ))).prodMk
    ((hH.differentiable (by simp) _).hasFDerivAt.prodMk
      ((contDiff_fderiv_apply hH (0, 1)).differentiable (by simp) _).hasFDerivAt)
  refine (congrArg (· (1, 0)) ((hLd _).hasFDerivAt.comp (0, τ) hφ).fderiv).trans ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_snd']
  rw [← deriv_fderiv_snd hH 0 τ, fderiv_apply_zero_prod hLd]
  simp only [eulerLagrange, canonicalMomentum, sub_apply, fderiv_snd_apply hH 0]
  abel

/-- The integrand `L(τ, H, ∂τ H)` of the action is smooth. -/
lemma contDiff_integrand {L : ℝ × E × E → ℝ} (hL : ContDiff ℝ ∞ L) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ fun p : ℝ × ℝ ↦ L (p.2, H p, fderiv ℝ H p (0, 1)) :=
  hL.comp (contDiff_snd.prodMk (hH.prodMk (contDiff_fderiv_apply hH (0, 1))))

/-- First variation of `∫ L(τ, H, ∂τ H) dτ` along a variation fixing the endpoints. -/
lemma hasDerivAt_integral_variation {L : ℝ × E × E → ℝ} (hL : ContDiff ℝ ∞ L) (hH : ContDiff ℝ ∞ H)
    (T : ℝ) (h0 : ∀ s, H (s, 0) = H (0, 0)) (hT : ∀ s, H (s, T) = H (0, T)) :
    HasDerivAt (fun s ↦ ∫ τ in (0 : ℝ)..T, L (τ, H (s, τ), fderiv ℝ H (s, τ) (0, 1)))
      (∫ τ in (0 : ℝ)..T, eulerLagrange L (fun σ ↦ H (0, σ)) τ (fderiv ℝ H (0, τ) (1, 0))) 0 := by
  set q : ℝ → E := fun σ ↦ H (0, σ)
  set V : ℝ → E := fun σ ↦ fderiv ℝ H (0, σ) (1, 0)
  have hVs : ContDiff ℝ ∞ V :=
    (contDiff_fderiv_apply hH (1, 0)).comp (contDiff_const.prodMk contDiff_id)
  have hqs : ContDiff ℝ ∞ q := hH.comp (contDiff_const.prodMk contDiff_id)
  have hPvs : ContDiff ℝ ∞ (canonicalMomentum L q) := contDiff_fderiv_partial_v hL hqs
  have hbp := integral_by_parts_covector hPvs hVs T
  rw [show V 0 = 0 from fderiv_fst_apply_eq_zero hH h0,
    show V T = 0 from fderiv_fst_apply_eq_zero hH hT] at hbp
  refine (hasDerivAt_intervalIntegral_of_contDiff
    ((contDiff_integrand hL hH).of_le (by simp)) 0 T 0).congr_deriv ?_
  simp_rw [fderiv_integrand_apply hL hH]
  rw [integral_add (((contDiff_eulerLagrange hL hqs).continuous.clm_apply
    hVs.continuous).intervalIntegrable _ _)
    ((continuous_deriv_clm_apply_add hPvs hVs).intervalIntegrable _ _), hbp]
  simp [V]

end ClassicalMechanics
