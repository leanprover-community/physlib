/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Physlib.ClassicalMechanics.Lagrangian.FirstVariation
public import Physlib.Mathematics.VariationalCalculus.Interval

/-!
# Critical points and Euler-Lagrange equations

Critical points of the action are the solutions of the Euler-Lagrange equations.

## i. Overview

`γ` is a critical point over `[t₀, t₁]` if it is smooth and every variation has zero first
variation of the action, which is Hamilton's principle `δS = 0` for variations fixing the
endpoints. For `t₀ ≠ t₁`, `γ` is a critical point over `[t₀, t₁]` iff the Euler-Lagrange equations
`eulerLagrange S t₀ q = 0` hold on `[0, t₁ -ᵥ t₀]`, where `q σ = γ (σ +ᵥ t₀)`. This section treats a
normed space `E` as the configuration space.

## ii. Key results

- `LagrangianSystem.IsCriticalPoint`: critical points of the action
- `LagrangianSystem.isCriticalPoint_of_vsub_nonpos`: every smooth curve is critical over an empty
  or one-point interval
- `LagrangianSystem.isCriticalPoint_of_eulerLagrange_eq_zero`: equations imply criticality
- `LagrangianSystem.eulerLagrange_eq_zero_of_isCriticalPoint`: criticality implies equations
- `LagrangianSystem.isCriticalPoint_iff_eulerLagrange`: the two are equivalent

## iii. Table of contents

- A. Critical points
  - A.1. The definition
  - A.2. Euler-Lagrange equations

## iv. References

* V. I. Arnold, Mathematical Methods of Classical Mechanics. [ref: arnold_mechanics]
* I. Terek, Introductory Variational Calculus on Manifolds. [ref: terek_variational_manifolds]
* L. D. Landau and E. M. Lifshitz, Mechanics. [ref: landau_mechanics]
-/

@[expose] public section

namespace ClassicalMechanics

open Set intervalIntegral
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : ConfigurationSpace I}

namespace LagrangianSystem

/-!
## A. Critical points

### A.1. The definition
-/

section Definition

variable (S : LagrangianSystem I M) {γ : Time → M} {t₀ t₁ : Time}

/-- `γ` is smooth and every variation of `γ` fixing the endpoints has zero first variation of the
action, i.e. `d/ds S[γ_s]` vanishes at `s = 0` (Hamilton's principle). -/
def IsCriticalPoint (γ : Time → M) (t₀ t₁ : Time) : Prop :=
  ContMDiff 𝓘(ℝ, ℝ) I ∞ γ ∧ ∀ h : Variation I γ t₀ t₁,
    HasDerivAt (fun s ↦ S.action (fun t ↦ h.toFun (s, t)) t₀ t₁) 0 0

/-- Every smooth curve is critical over an empty or one-point interval. -/
lemma isCriticalPoint_of_vsub_nonpos (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (h : t₁ -ᵥ t₀ ≤ 0) :
    S.IsCriticalPoint γ t₀ t₁ :=
  ⟨hγ, fun _ ↦ by simp [action_eq_zero_of_vsub_nonpos _ h, hasDerivAt_const]⟩

end Definition

/-!
### A.2. Euler-Lagrange equations
-/

variable (S : LagrangianSystem 𝓘(ℝ, E) ⟨E⟩) {γ : Time → E} {t₀ t₁ : Time}

/-- If `q σ = γ (σ +ᵥ t₀)` is smooth and `eulerLagrange S t₀ q = 0` on `(0, t₁ -ᵥ t₀)`, then `γ`
is a critical point. -/
lemma isCriticalPoint_of_eulerLagrange_eq_zero
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
  refine eqOn_Icc_zero_of_integral_contDiff_smul_eq_zero
    (contDiff_eulerLagrange
      ((Time.contMDiff_iff_contDiff_vadd γ t₀ ∞).1 hc.1)).continuous.continuousOn ht
    fun ψ hψ hs w ↦ ?_
  obtain ⟨h, hh⟩ := Variation.exists_bump hc.1 hψ hs w
  have hq : (fun σ : ℝ ↦ h.toFun (0, σ +ᵥ t₀)) = fun σ : ℝ ↦ γ (σ +ᵥ t₀) := by
    funext σ; simp [hh]
  have hV (τ : ℝ) :
      fderiv ℝ (fun p : ℝ × ℝ ↦ h.toFun (p.1, p.2 +ᵥ t₀)) (0, τ) (1, 0) = ψ τ • w := by
    rw [← fderiv_curry_fst _ 0 τ (h.contDiff_comp_vadd.differentiable (by simp) _)]
    simpa [Function.curry, hh] using ((hasDerivAt_id (0 : ℝ)).smul_const (ψ τ • w)).deriv
  -- the derivative at `s = 0` is unique, and zero by criticality
  have hu := (S.hasDerivAt_action_variation h ht.le).unique (hc.2 h)
  simp only [hq, hV] at hu
  exact hu

/-- For `t₁ -ᵥ t₀ ≠ 0`, `γ` is a critical point iff `q σ = γ (σ +ᵥ t₀)` is smooth and
`eulerLagrange S t₀ q = 0` on `[0, t₁ -ᵥ t₀]`. -/
lemma isCriticalPoint_iff_eulerLagrange (ht : t₁ -ᵥ t₀ ≠ 0) :
    S.IsCriticalPoint γ t₀ t₁ ↔ ContDiff ℝ ∞ (fun σ : ℝ ↦ γ (σ +ᵥ t₀)) ∧
      ∀ τ ∈ Icc 0 (t₁ -ᵥ t₀), eulerLagrange S t₀ (fun σ : ℝ ↦ γ (σ +ᵥ t₀)) τ = 0 :=
  ⟨fun hc ↦ ⟨(Time.contMDiff_iff_contDiff_vadd γ t₀ ∞).1 hc.1,
      S.eulerLagrange_eq_zero_of_isCriticalPoint ht hc⟩,
    fun h ↦ S.isCriticalPoint_of_eulerLagrange_eq_zero h.1 fun τ hτ ↦
      h.2 τ (Ioo_subset_Icc_self hτ)⟩

end LagrangianSystem

end ClassicalMechanics
