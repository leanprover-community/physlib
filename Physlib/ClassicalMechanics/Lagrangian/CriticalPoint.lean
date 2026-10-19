/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Physlib.ClassicalMechanics.Lagrangian.NormedSpace
public import Physlib.Mathematics.VariationalCalculus.Interval

/-!
# Critical points and Euler-Lagrange equations

Critical points of the action are the solutions of the Euler-Lagrange equations.

## i. Overview

For `t₀ ≠ t₁`, `γ` is a critical point over `[t₀, t₁]` iff `eulerLagrange S t₀ q = 0`, where
`q σ = γ (σ +ᵥ t₀)`.

## ii. Key results

- `LagrangianSystem.isCriticalPoint_of_eulerLagrange`: equations imply criticality
- `LagrangianSystem.eulerLagrange_eq_zero_of_isCriticalPoint`: criticality implies equations
- `LagrangianSystem.isCriticalPoint_iff_eulerLagrange`: the two are equivalent

## iii. Table of contents

- A. Critical points

## iv. References

* V. I. Arnold, Mathematical Methods of Classical Mechanics. [ref: arnold_mechanics]
* I. Terek, Introductory Variational Calculus on Manifolds. [ref: terek_variational_manifolds]
* L. D. Landau and E. M. Lifshitz, Mechanics. [ref: landau_mechanics]
-/

@[expose] public section

namespace ClassicalMechanics

open Set intervalIntegral
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : LagrangianSystem 𝓘(ℝ, E) ⟨E⟩)
  {γ : Time → E} {t₀ t₁ : Time}

namespace LagrangianSystem

/-!
## A. Critical points
-/

/-- For smooth `ψ` supported in `(0, t₁ -ᵥ t₀)` and `w : E`, a variation `h` of `γ` with
`h (s, τ +ᵥ t₀) = γ (τ +ᵥ t₀) + s • ψ τ • w`. -/
private lemma exists_variation_bump (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hs : tsupport ψ ⊆ Ioo 0 (t₁ -ᵥ t₀)) (w : E) :
    ∃ h : Variation (M := ⟨E⟩) 𝓘(ℝ, E) γ t₀ t₁,
      ∀ s τ, h.toFun (s, τ +ᵥ t₀) = γ (τ +ᵥ t₀) + s • (ψ τ • w) := by
  have hψt : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : Time ↦ ψ (t -ᵥ t₀)) :=
    (Time.contMDiff_iff_contDiff_vadd _ t₀ ∞).2 (by simpa using hψ)
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × Time ↦ γ p.2 + p.1 • (ψ (p.2 -ᵥ t₀) • w)) :=
    (hγ.comp contMDiff_snd).add (contMDiff_fst.smul ((hψt.comp contMDiff_snd).smul contMDiff_const))
  have h0 : ψ 0 = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hs h).1.false
  have hT : ψ (t₁ -ᵥ t₀) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hs h).2.false
  refine ⟨⟨⟨fun p ↦ γ p.2 + p.1 • (ψ (p.2 -ᵥ t₀) • w), hF⟩, fun s _ ↦ ?_, fun s ↦ ?_, fun s ↦ ?_⟩,
    fun s τ ↦ ?_⟩
  all_goals simp_all [Time.vsub_eq_val]

/-- If `q σ = γ (σ +ᵥ t₀)` is smooth and `eulerLagrange S t₀ q = 0` on `(0, t₁ -ᵥ t₀)`, then `γ`
is a critical point. -/
lemma isCriticalPoint_of_eulerLagrange
    (hγ : ContDiff ℝ ∞ (fun σ : ℝ ↦ γ (σ +ᵥ t₀))) (hEq : ∀ τ ∈ Ioo 0 (t₁ -ᵥ t₀),
      eulerLagrange S t₀ (fun σ ↦ γ (σ +ᵥ t₀)) τ = 0) : S.IsCriticalPoint γ t₀ t₁ := by
  have hγ' := (Time.contMDiff_iff_contDiff_vadd γ t₀ ∞).2 hγ
  rcases le_or_gt (t₁ -ᵥ t₀) 0 with ht | ht
  · exact S.isCriticalPoint_of_vsub_nonpos hγ' ht
  refine ⟨hγ', fun h ↦ ?_⟩
  refine (S.hasDerivAt_action_variation h ht.le).congr_deriv ?_
  have hq : ContDiff ℝ ∞ (fun σ ↦ h.toFun (0, σ +ᵥ t₀)) :=
    h.contDiff_comp_vadd.comp (contDiff_const.prodMk contDiff_id)
  have hzero : ∀ τ ∈ Icc 0 (t₁ -ᵥ t₀), eulerLagrange S t₀ (fun σ ↦ h.toFun (0, σ +ᵥ t₀)) τ = 0 :=
    EqOn.of_subset_closure (g := fun _ ↦ 0) (fun τ hτ ↦ by
      refine (eulerLagrange_congr ?_).trans (hEq τ hτ)
      filter_upwards [Ioo_mem_nhds hτ.1 hτ.2] with σ hσ
      exact h.apply_zero σ ⟨hσ.1.le, hσ.2.le⟩)
      (contDiff_eulerLagrange hq).continuous.continuousOn continuousOn_const
      Ioo_subset_Icc_self (by rw [closure_Ioo ht.ne])
  refine (integral_congr (g := fun _ ↦ (0 : ℝ)) fun τ hτ ↦ ?_).trans (by simp)
  rw [uIcc_of_le ht.le] at hτ
  simp [hzero τ hτ]

/-- A critical point `γ` has `eulerLagrange S t₀ q = 0` on `[0, t₁ -ᵥ t₀]`, `q σ = γ (σ +ᵥ t₀)`. -/
lemma eulerLagrange_eq_zero_of_isCriticalPoint (ht : t₁ -ᵥ t₀ ≠ 0)
    (hc : S.IsCriticalPoint γ t₀ t₁) : ∀ τ ∈ Icc 0 (t₁ -ᵥ t₀),
      eulerLagrange S t₀ (fun σ : ℝ ↦ γ (σ +ᵥ t₀)) τ = 0 := by
  rcases ht.lt_or_gt with ht | ht
  · exact fun τ hτ ↦ absurd (hτ.1.trans hτ.2) ht.not_ge
  refine eq_zero_of_integral_contDiff_smul_eq_zero
    (contDiff_eulerLagrange
      ((Time.contMDiff_iff_contDiff_vadd γ t₀ ∞).1 hc.1)).continuous.continuousOn ht
    fun ψ hψ hs w ↦ ?_
  obtain ⟨h, hh⟩ := exists_variation_bump hc.1 hψ hs w
  have hq : (fun σ : ℝ ↦ h.toFun (0, σ +ᵥ t₀)) = fun σ : ℝ ↦ γ (σ +ᵥ t₀) := by
    funext σ; simp [hh]
  have hV (τ : ℝ) :
      fderiv ℝ (fun p : ℝ × ℝ ↦ h.toFun (p.1, p.2 +ᵥ t₀)) (0, τ) (1, 0) = ψ τ • w := by
    rw [← fderiv_curry_fst _ 0 τ (h.contDiff_comp_vadd.differentiable (by simp) _)]
    simpa [Function.curry, hh] using ((hasDerivAt_id (0 : ℝ)).smul_const (ψ τ • w)).deriv
  -- the derivative at `s = 0` is unique, and zero by criticality
  simpa [hq, hV] using (S.hasDerivAt_action_variation h ht.le).unique (hc.2 h)

/-- For `t₁ -ᵥ t₀ ≠ 0`, `γ` is a critical point iff `q σ = γ (σ +ᵥ t₀)` is smooth and
`eulerLagrange S t₀ q = 0` on `[0, t₁ -ᵥ t₀]`. -/
lemma isCriticalPoint_iff_eulerLagrange (ht : t₁ -ᵥ t₀ ≠ 0) :
    S.IsCriticalPoint γ t₀ t₁ ↔ ContDiff ℝ ∞ (fun σ : ℝ ↦ γ (σ +ᵥ t₀)) ∧
      ∀ τ ∈ Icc 0 (t₁ -ᵥ t₀), eulerLagrange S t₀ (fun σ : ℝ ↦ γ (σ +ᵥ t₀)) τ = 0 :=
  ⟨fun hc ↦ ⟨(Time.contMDiff_iff_contDiff_vadd γ t₀ ∞).1 hc.1,
      S.eulerLagrange_eq_zero_of_isCriticalPoint ht hc⟩,
    fun h ↦ S.isCriticalPoint_of_eulerLagrange h.1 fun τ hτ ↦ h.2 τ (Ioo_subset_Icc_self hτ)⟩

end LagrangianSystem

end ClassicalMechanics
