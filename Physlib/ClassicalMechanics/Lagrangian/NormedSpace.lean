/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Physlib.ClassicalMechanics.Lagrangian.FirstVariation
public import Physlib.SpaceAndTime.Time.ManifoldCurves

/-!
# The action on normed spaces

The action on a normed space in a time coordinate.

## i. Overview

`S.coord t₀ (τ, q, v)` is the Lagrangian in the coordinate `τ ↦ τ +ᵥ t₀`. The action, also
along a variation, is its integral over `[0, t₁ -ᵥ t₀]`.

## ii. Key results

- `Variation.contDiff_comp_vadd`: a variation is smooth in coordinates
- `LagrangianSystem.action_eq_integral_coord`: the action in coordinates
- `LagrangianSystem.action_variation_eq_integral`: the same along a variation
- `LagrangianSystem.hasDerivAt_action_variation`: first variation of the action

## iii. Table of contents

- A. Smoothness in coordinates
- B. The action in coordinates
- C. The action of a variation

## iv. References

* L. D. Landau and E. M. Lifshitz, Mechanics. [ref: landau_mechanics]
-/

@[expose] public section

namespace ClassicalMechanics

open MeasureTheory
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-!
## A. Smoothness in coordinates
-/

namespace Variation

/-- `(s, τ) ↦ h (s, τ +ᵥ t₀)` is smooth. -/
lemma contDiff_comp_vadd {γ : Time → E} {t₀ t₁ : Time}
    (h : Variation (M := ⟨E⟩) 𝓘(ℝ, E) γ t₀ t₁) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ h.toFun (p.1, p.2 +ᵥ t₀)) := by
  have key (f : ℝ × ℝ → E) (hf : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ f) :
      ContDiff ℝ ∞ f := by
    rwa [← modelWithCornersSelf_prod (𝕜 := ℝ) (E := ℝ) (F := ℝ),
      chartedSpaceSelf_prod (H := ℝ) (H' := ℝ), contMDiff_iff_contDiff] at hf
  exact key _ (h.toFun.contMDiff.comp
    (contMDiff_fst.prodMk ((Time.contMDiff_vadd t₀ ∞).comp contMDiff_snd)))

end Variation

/-!
## B. The action in coordinates
-/

namespace LagrangianSystem

variable (S : LagrangianSystem 𝓘(ℝ, E) ⟨E⟩)

/-- The action is the integral over `[0, t₁ -ᵥ t₀]` of `S.coord t₀ (s, q s, q' s)`, where
`q τ = γ (τ +ᵥ t₀)` and `q' = deriv q`. -/
lemma action_eq_integral_coord (γ : Time → E) (t₀ t₁ : Time) :
    S.action γ t₀ t₁ = ∫ s in Set.Icc 0 (t₁ -ᵥ t₀),
      S.coord t₀ (s, γ (s +ᵥ t₀), deriv (fun τ : ℝ ↦ γ (τ +ᵥ t₀)) s) := by
  simp only [action, coord, Time.tangentMap_eq_deriv_vadd]
  rfl

/-!
## C. The action of a variation
-/

/-- The action of `t ↦ h (s, t)` is the integral over `[0, t₁ -ᵥ t₀]` of
`S.coord t₀ (τ, q τ, q' τ)`, where `q τ = h (s, τ +ᵥ t₀)` and `q' = deriv q`. -/
lemma action_variation_eq_integral {γ : Time → E} {t₀ t₁ : Time}
    (h : Variation (M := ⟨E⟩) 𝓘(ℝ, E) γ t₀ t₁) (ht : 0 ≤ t₁ -ᵥ t₀) (s : ℝ) :
    S.action (fun t ↦ h.toFun (s, t)) t₀ t₁ =
      ∫ τ in (0 : ℝ)..(t₁ -ᵥ t₀), S.coord t₀ (τ, h.toFun (s, τ +ᵥ t₀),
        fderiv ℝ (fun p : ℝ × ℝ ↦ h.toFun (p.1, p.2 +ᵥ t₀)) (s, τ) (0, 1)) := by
  rw [action_eq_integral_coord, intervalIntegral.integral_of_le ht,
    ← integral_Icc_eq_integral_Ioc]
  exact setIntegral_congr_fun measurableSet_Icc fun τ _ ↦ by
    simp [← show deriv (fun σ ↦ h.toFun (s, σ +ᵥ t₀)) τ = _ from fderiv_curry_snd _ s τ
      (h.contDiff_comp_vadd.differentiable (by simp) (s, τ)) 1]

/-- The `s`-derivative at `0` of the action of `t ↦ h (s, t)` is the integral over
`[0, t₁ -ᵥ t₀]` of `eulerLagrange S t₀ q τ` applied to the derivative of `s ↦ h (s, τ +ᵥ t₀)` at
`0`, where `q σ = h (0, σ +ᵥ t₀)`. -/
lemma hasDerivAt_action_variation {γ : Time → E} {t₀ t₁ : Time}
    (h : Variation (M := ⟨E⟩) 𝓘(ℝ, E) γ t₀ t₁) (ht : 0 ≤ t₁ -ᵥ t₀) :
    HasDerivAt (fun s ↦ S.action (fun t ↦ h.toFun (s, t)) t₀ t₁)
      (∫ τ in (0 : ℝ)..(t₁ -ᵥ t₀),
        eulerLagrange S t₀ (fun σ ↦ h.toFun (0, σ +ᵥ t₀)) τ
          (fderiv ℝ (fun p : ℝ × ℝ ↦ h.toFun (p.1, p.2 +ᵥ t₀)) (0, τ) (1, 0))) 0 := by
  simpa only [S.action_variation_eq_integral h ht] using
    hasDerivAt_integral_variation S t₀ h.contDiff_comp_vadd
      (t₁ -ᵥ t₀) (fun s ↦ by simp [h.apply_left])
      (fun s ↦ by rw [vsub_vadd, h.apply_right, h.apply_right])

end LagrangianSystem

end ClassicalMechanics
