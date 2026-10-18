/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Physlib.ClassicalMechanics.Lagrangian.Basic
public import Physlib.Mathematics.Calculus.PartialDerivatives
public import Physlib.Mathematics.ForMathlib.ContMDiffProd
public import Physlib.SpaceAndTime.Time.ManifoldCurves

/-!
# Lagrangian systems on normed spaces

The action of `L (t, q, q̇)` on a normed space in coordinates.

## i. Overview

On a normed space the tangent bundle is `E × E`, and the action along a curve is `∫ L (t, γ, γ̇)
dt`.

## ii. Key results

- `LagrangianSystem.action_ofNormedSpace`
- `action_variation`

## iii. Table of contents

- A. The action in coordinates
- B. Smoothness in coordinates
- C. The action of a variation

## iv. References

* L. D. Landau and E. M. Lifshitz, Mechanics. [ref: landau_mechanics]
-/

@[expose] public section

open Set MeasureTheory intervalIntegral
open scoped Manifold ContDiff
namespace ClassicalMechanics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {γ : Time → E} {t₀ t₁ : Time}

/-!
## A. The action in coordinates
-/

namespace LagrangianSystem

/-- The action of `L(t, q, q̇)` on a normed space is `∫ L(t, γ, γ̇) dt`. -/
lemma action_ofNormedSpace (L : Time × E × E → ℝ)
    (hL : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E × E)) 𝓘(ℝ, ℝ) ∞ L) (γ : Time → E) (t₀ t₁ : Time) :
    (ofNormedSpace L hL).action γ t₀ t₁ = ∫ s in Set.Icc 0 (t₁ -ᵥ t₀),
      L (s +ᵥ t₀, γ (s +ᵥ t₀), deriv (fun τ : ℝ ↦ γ (τ +ᵥ t₀)) s) := by
  simp only [action, ofNormedSpace, Time.tangentMap_eq_deriv_vadd]
  rfl

end LagrangianSystem

/-!
## B. Smoothness in coordinates
-/

/-- A Lagrangian in a time coordinate based at `t₀` is smooth. -/
lemma contDiff_coord (L : Time × E × E → ℝ)
    (hL : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E × E)) 𝓘(ℝ, ℝ) ∞ L) (t₀ : Time) :
    ContDiff ℝ ∞ (fun p : ℝ × E × E ↦ L (p.1 +ᵥ t₀, p.2)) := by
  exact contMDiff_prod_self_iff.1 (hL.comp
    (((Time.contMDiff_vadd t₀ ∞).comp contMDiff_fst).prodMk contMDiff_snd))

/-- A variation in a time coordinate based at `t₀` is smooth. -/
lemma contDiff_coordVariation (h : Variation (M := ⟨E⟩) 𝓘(ℝ, E) γ t₀ t₁) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ h.toFun (p.1, p.2 +ᵥ t₀)) := by
  exact contMDiff_prod_self_iff.1 (h.toFun.contMDiff.comp
    (contMDiff_fst.prodMk ((Time.contMDiff_vadd t₀ ∞).comp contMDiff_snd)))

/-!
## C. The action of a variation
-/

/-- The action along a variation in the time coordinate based at `t₀`. -/
lemma action_variation (L : Time × E × E → ℝ)
    (hL : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E × E)) 𝓘(ℝ, ℝ) ∞ L)
    (h : Variation (M := ⟨E⟩) 𝓘(ℝ, E) γ t₀ t₁) (ht : 0 ≤ t₁ -ᵥ t₀) (s : ℝ) :
    (LagrangianSystem.ofNormedSpace L hL).action (fun t ↦ h.toFun (s, t)) t₀ t₁ =
      ∫ τ in (0 : ℝ)..(t₁ -ᵥ t₀), L (τ +ᵥ t₀, h.toFun (s, τ +ᵥ t₀),
        fderiv ℝ (fun p : ℝ × ℝ ↦ h.toFun (p.1, p.2 +ᵥ t₀)) (s, τ) (0, 1)) := by
  rw [LagrangianSystem.action_ofNormedSpace, intervalIntegral.integral_of_le ht,
    ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun τ _ ↦ ?_
  simp only [← fderiv_snd_apply (contDiff_coordVariation h) s τ]

end ClassicalMechanics
