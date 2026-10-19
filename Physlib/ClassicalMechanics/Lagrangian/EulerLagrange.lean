/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Physlib.ClassicalMechanics.Lagrangian.FirstVariation
public import Physlib.ClassicalMechanics.Lagrangian.NormedSpace

/-!
# Euler-Lagrange equations

On a normed space, critical points of the action are the solutions of the Euler-Lagrange equations.

## i. Overview

A smooth curve is a critical point of the action over `[t₀, t₁]` iff the Euler-Lagrange covector
vanishes along it.

## ii. Key results

- `LagrangianSystem.hasDerivAt_action_variation`: first variation of the action
- `LagrangianSystem.isCriticalPoint_of_eulerLagrange`: Euler-Lagrange equations imply criticality
- `LagrangianSystem.eulerLagrange_eq_zero_of_isCriticalPoint`: criticality implies the
  Euler-Lagrange equations
- `LagrangianSystem.isCriticalPoint_ofNormedSpace_iff`: the two are equivalent

## iii. Table of contents

- A. First variation of the action
- B. Critical points

## iv. References

* V. I. Arnold, Mathematical Methods of Classical Mechanics. [ref: arnold_mechanics]
* I. Terek, Introductory Variational Calculus on Manifolds. [ref: terek_variational_manifolds]
* L. D. Landau and E. M. Lifshitz, Mechanics. [ref: landau_mechanics]
-/

@[expose] public section

open Set intervalIntegral Topology
open scoped Manifold ContDiff
namespace ClassicalMechanics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {γ : Time → E} {t₀ t₁ : Time}

namespace LagrangianSystem

/-!
## A. First variation of the action
-/

/-- First variation of the action of a Lagrangian on a normed space. -/
lemma hasDerivAt_action_variation (L : Time × E × E → ℝ)
    (hL : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E × E)) 𝓘(ℝ, ℝ) ∞ L)
    (h : Variation (M := ⟨E⟩) 𝓘(ℝ, E) γ t₀ t₁) (ht : 0 ≤ t₁ -ᵥ t₀) :
    HasDerivAt (fun s ↦ (LagrangianSystem.ofNormedSpace L hL).action (fun t ↦ h.toFun (s, t)) t₀ t₁)
      (∫ τ in (0 : ℝ)..(t₁ -ᵥ t₀),
        eulerLagrange (fun p : ℝ × E × E ↦ L (p.1 +ᵥ t₀, p.2)) (fun σ ↦ h.toFun (0, σ +ᵥ t₀)) τ
          (fderiv ℝ (fun p : ℝ × ℝ ↦ h.toFun (p.1, p.2 +ᵥ t₀)) (0, τ) (1, 0))) 0 := by
  simpa only [action_variation L hL h ht] using
    hasDerivAt_integral_variation (L := fun p : ℝ × E × E ↦ L (p.1 +ᵥ t₀, p.2))
      (contDiff_timeCoord L hL t₀) (contDiff_timeCoordVariation h) (t₁ -ᵥ t₀)
      (fun s ↦ by simp [h.apply_left])
      (fun s ↦ by rw [vsub_vadd, h.apply_right, h.apply_right])

/-!
## B. Critical points
-/

/-- A bump function gives a variation fixing the endpoints. -/
private lemma exists_variation_bump (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hs : tsupport ψ ⊆ Ioo 0 (t₁ -ᵥ t₀)) (w : E) :
    ∃ h : Variation (M := ⟨E⟩) 𝓘(ℝ, E) γ t₀ t₁,
      ∀ s τ, h.toFun (s, τ +ᵥ t₀) = γ (τ +ᵥ t₀) + s • (ψ τ • w) := by
  have hψ' : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : Time ↦ ψ (t -ᵥ t₀)) :=
    (Time.contMDiff_iff_contDiff_vadd _ t₀ ∞).2 (by simpa using hψ)
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × Time ↦ γ p.2 + p.1 • (ψ (p.2 -ᵥ t₀) • w)) :=
    (hγ.comp contMDiff_snd).add (contMDiff_fst.smul ((hψ'.comp contMDiff_snd).smul contMDiff_const))
  have h0 : ψ 0 = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hs h).1.false
  have hT : ψ (t₁ -ᵥ t₀) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hs h).2.false
  refine ⟨⟨⟨fun p ↦ γ p.2 + p.1 • (ψ (p.2 -ᵥ t₀) • w), hF⟩, fun s _ ↦ ?_, fun s ↦ ?_, fun s ↦ ?_⟩,
    fun s τ ↦ ?_⟩
  all_goals simp_all [Time.vsub_eq_val]

/-- A smooth curve satisfying the Euler-Lagrange equations is a critical point. -/
lemma isCriticalPoint_of_eulerLagrange (L : Time × E × E → ℝ)
    (hL : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E × E)) 𝓘(ℝ, ℝ) ∞ L) (ht : 0 < t₁ -ᵥ t₀)
    (hg : ContDiff ℝ ∞ (fun τ : ℝ ↦ γ (τ +ᵥ t₀))) (hEuler : ∀ τ ∈ Icc 0 (t₁ -ᵥ t₀),
      eulerLagrange (fun p : ℝ × E × E ↦ L (p.1 +ᵥ t₀, p.2)) (fun τ ↦ γ (τ +ᵥ t₀)) τ = 0) :
    (LagrangianSystem.ofNormedSpace L hL).IsCriticalPoint γ t₀ t₁ := by
  refine ⟨(Time.contMDiff_iff_contDiff_vadd γ t₀ ∞).2 hg, fun h ↦ ?_⟩
  refine (hasDerivAt_action_variation L hL h ht.le).congr_deriv ?_
  have hq : ContDiff ℝ ∞ (fun σ ↦ h.toFun (0, σ +ᵥ t₀)) :=
    (contDiff_timeCoordVariation h).comp (contDiff_const.prodMk contDiff_id)
  have hEq : ∀ τ ∈ Ioo 0 (t₁ -ᵥ t₀), (fun σ ↦ h.toFun (0, σ +ᵥ t₀)) =ᶠ[𝓝 τ]
      (fun σ ↦ γ (σ +ᵥ t₀)) := by
    intro τ hτ
    filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with σ hσ
    exact h.apply_zero σ ⟨hσ.1.le, hσ.2.le⟩
  have hzero := (contDiff_eulerLagrange (contDiff_timeCoord L hL t₀) hq).continuous
    |>.eqOn_Icc_of_eqOn_Ioo ht fun τ hτ ↦
      (eulerLagrange_congr (hEq τ hτ)).trans (hEuler τ ⟨hτ.1.le, hτ.2.le⟩)
  refine (integral_congr (g := fun _ ↦ (0 : ℝ)) fun τ hτ ↦ ?_).trans (by simp)
  rw [uIcc_of_le ht.le] at hτ
  simp [hzero τ hτ]

/-- A critical point satisfies the Euler-Lagrange equations. -/
lemma eulerLagrange_eq_zero_of_isCriticalPoint (L : Time × E × E → ℝ)
    (hL : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E × E)) 𝓘(ℝ, ℝ) ∞ L) (ht : 0 < t₁ -ᵥ t₀)
    (hc : (LagrangianSystem.ofNormedSpace L hL).IsCriticalPoint γ t₀ t₁) : ∀ τ ∈ Icc 0 (t₁ -ᵥ t₀),
      eulerLagrange (fun p : ℝ × E × E ↦ L (p.1 +ᵥ t₀, p.2)) (fun τ : ℝ ↦ γ (τ +ᵥ t₀)) τ = 0 := by
  have hg : ContDiff ℝ ∞ (fun τ : ℝ ↦ γ (τ +ᵥ t₀)) :=
    (Time.contMDiff_iff_contDiff_vadd γ t₀ ∞).1 hc.1
  refine eq_zero_of_integral_smul_eq_zero
    (contDiff_eulerLagrange (contDiff_timeCoord L hL t₀) hg).continuous ht fun ψ hψ _ hs w ↦ ?_
  obtain ⟨h, hh⟩ := exists_variation_bump hc.1 hψ hs w
  have hq : (fun σ : ℝ ↦ h.toFun (0, σ +ᵥ t₀)) = fun σ : ℝ ↦ γ (σ +ᵥ t₀) := by
    funext σ; simp [hh]
  have hV : ∀ τ, fderiv ℝ (fun p : ℝ × ℝ ↦ h.toFun (p.1, p.2 +ᵥ t₀)) (0, τ) (1, 0) = ψ τ • w := by
    intro τ
    rw [← deriv_fst_eq_fderiv_apply (contDiff_timeCoordVariation h) 0 τ,
      show (fun r ↦ h.toFun (r, τ +ᵥ t₀)) = fun r ↦ γ (τ +ᵥ t₀) + r • (ψ τ • w) from
        funext fun r ↦ hh r τ]
    simpa using (((hasDerivAt_id (0 : ℝ)).smul_const (ψ τ • w)).const_add (γ (τ +ᵥ t₀))).deriv
  have := (hasDerivAt_action_variation L hL h ht.le).unique (hc.2 h)
  simpa [hq, hV] using this

/-- A smooth curve on a normed space is a critical point of the action of `L(t, q, q̇)` over
`[t₀, t₁]` iff it satisfies the Euler-Lagrange equations in coordinates. -/
lemma isCriticalPoint_ofNormedSpace_iff (L : Time × E × E → ℝ)
    (hL : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E × E)) 𝓘(ℝ, ℝ) ∞ L) (ht : 0 < t₁ -ᵥ t₀) :
    (LagrangianSystem.ofNormedSpace L hL).IsCriticalPoint γ t₀ t₁ ↔
      ContDiff ℝ ∞ (fun τ : ℝ ↦ γ (τ +ᵥ t₀)) ∧ ∀ τ ∈ Icc 0 (t₁ -ᵥ t₀),
        eulerLagrange (fun p : ℝ × E × E ↦ L (p.1 +ᵥ t₀, p.2)) (fun τ : ℝ ↦ γ (τ +ᵥ t₀)) τ = 0 :=
  ⟨fun hc ↦ ⟨(Time.contMDiff_iff_contDiff_vadd γ t₀ ∞).1 hc.1,
      eulerLagrange_eq_zero_of_isCriticalPoint L hL ht hc⟩,
    fun h ↦ isCriticalPoint_of_eulerLagrange L hL ht h.1 h.2⟩

end LagrangianSystem

end ClassicalMechanics
