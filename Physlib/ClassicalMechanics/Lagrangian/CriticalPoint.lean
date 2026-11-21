/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Physlib.ClassicalMechanics.Lagrangian.Chart
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
normed space `E` as the configuration space. Section B reads a critical point on a manifold in a
chart: a chart-supported bump variation has first variation the integral of the Euler-Lagrange
covector, which vanishes, and the fundamental lemma gives the equations. The chart Lagrangian is
smooth only on the chart target, so the argument uses a smooth extension. The converse is not
formalised.

## ii. Key results

- `LagrangianSystem.IsCriticalPoint`: critical points of the action
- `LagrangianSystem.isCriticalPoint_of_vsub_nonpos`: every smooth curve is critical over an empty
  or one-point interval
- `LagrangianSystem.isCriticalPoint_of_eulerLagrange_eq_zero`: equations imply criticality
- `LagrangianSystem.eulerLagrange_eq_zero_of_isCriticalPoint`: criticality implies equations
- `LagrangianSystem.isCriticalPoint_iff_eulerLagrange`: the two are equivalent
- `LagrangianSystem.integral_eulerLagrange_eq_zero_of_isCriticalPoint`: first variation along a
  chart-supported bump variation vanishes
- `LagrangianSystem.eulerLagrange_eq_zero_of_isCriticalPoint_chart`: Euler-Lagrange equations in
  every chart

## iii. Table of contents

- A. Critical points
  - A.1. The definition
  - A.2. Euler-Lagrange equations
- B. Critical points in a chart
  - B.1. First variation in a chart
  - B.2. Euler-Lagrange equations in a chart

## iv. References

* V. I. Arnold, Mathematical Methods of Classical Mechanics. [ref: arnold_mechanics]
* I. Terek, Introductory Variational Calculus on Manifolds. [ref: terek_variational_manifolds]
* L. D. Landau and E. M. Lifshitz, Mechanics. [ref: landau_mechanics]
-/

@[expose] public section

namespace ClassicalMechanics

open Set Topology Metric intervalIntegral
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

section NormedSpace

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

end NormedSpace

/-!
## B. Critical points in a chart
-/

/-!
### B.1. First variation in a chart
-/

/-- At a critical point `γ`, the first variation of the action under a localised variation vanishes
(Hamilton's principle `δS = 0`): the integral of the Euler-Lagrange expression of `S'` along `q`,
applied to `ψ • w`, is zero. Here `ψ` is a bump function supported in a compact set `C` of times,
`w` a vector, `S'` agrees with the chart Lagrangian on an open set `N`, and `q` is smooth, equal to
the chart reading of `γ` near `C`, and in `N` over `C`. -/
lemma integral_eulerLagrange_eq_zero_of_isCriticalPoint [I.Boundaryless]
    (S : LagrangianSystem I M) (x : M) {γ : Time → M} {t₀ t₁ : Time}
    (hc : S.IsCriticalPoint γ t₀ t₁) (hT : 0 ≤ t₁ -ᵥ t₀)
    {S' : LagrangianSystem 𝓘(ℝ, E) ⟨E⟩} {N : Set E} (hNo : IsOpen N)
    (hN : N ⊆ (extChartAt I x).target)
    (hLN : ∀ p : ℝ × E × E, p.2.1 ∈ N → S'.coord t₀ p = S.chartLagrangian x t₀ p) {q : ℝ → E}
    (hq : ContDiff ℝ ∞ q) {C : Set ℝ} (hC : IsCompact C)
    (hCs : ∀ τ ∈ C, γ (τ +ᵥ t₀) ∈ (extChartAt I x).source)
    (hqC : ∀ τ ∈ C, q =ᶠ[𝓝 τ] fun σ ↦ extChartAt I x (γ (σ +ᵥ t₀))) (hqN : ∀ τ ∈ C, q τ ∈ N)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hs : tsupport ψ ⊆ Ioo 0 (t₁ -ᵥ t₀))
    (hsC : tsupport ψ ⊆ C) (w : E) :
    ∫ τ in (0 : ℝ)..(t₁ -ᵥ t₀), eulerLagrange S' t₀ q τ (ψ τ • w) = 0 := by
  have hψc : HasCompactSupport ψ := hC.of_isClosed_subset (isClosed_tsupport ψ) hsC
  obtain ⟨B, hB⟩ := hψc.exists_bound_of_continuous hψ.continuous
  obtain ⟨ε, hε, hεN⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ τ ∈ C, ∀ r ∈ Icc (-ε) ε, q τ + r • (ψ τ • w) ∈ N := by
    obtain ⟨r₀, hr₀, hr₀N⟩ := (hC.image hq.continuous).exists_thickening_subset_open hNo
      (image_subset_iff.2 hqN)
    refine ⟨r₀ / (|B * ‖w‖| + 1), by positivity, fun τ hτ r hr ↦ hr₀N ?_⟩
    rw [mem_thickening_iff]
    refine ⟨q τ, ⟨τ, hτ, rfl⟩, ?_⟩
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have hr' : |r| ≤ r₀ / (|B * ‖w‖| + 1) := abs_le.2 ⟨by linarith [hr.1], hr.2⟩
    have hv : ‖ψ τ • w‖ ≤ |B * ‖w‖| :=
      (norm_smul _ _).trans_le ((mul_le_mul_of_nonneg_right (hB τ) (norm_nonneg w)).trans
        (le_abs_self _))
    calc |r| * ‖ψ τ • w‖ ≤ r₀ / (|B * ‖w‖| + 1) * |B * ‖w‖| := by gcongr
      _ < r₀ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg (B * ‖w‖)]
  obtain ⟨h, σ, hσ, hσ0, hσ'0, hσε, hoff, hsymm⟩ := Variation.exists_chart_bump x hc.1 hψ hs
    (fun τ hτ ↦ hCs τ (hsC hτ)) w hN hε
    (fun τ hτ r hr ↦ (hqC τ (hsC hτ)).eq_of_nhds ▸ hεN τ (hsC hτ) r hr)
  have hD : HasDerivAt (fun s ↦ S.action (fun t ↦ h.toFun (s, t)) t₀ t₁)
      (∫ τ in (0 : ℝ)..(t₁ -ᵥ t₀), eulerLagrange S' t₀ q τ (ψ τ • w)) 0 := by
    set Hc : ℝ × ℝ → E := fun p ↦ q p.2 + σ p.1 • (ψ p.2 • w) with hHc
    have hH : ContDiff ℝ ∞ Hc := by fun_prop
    have hψ0 : ψ 0 = 0 := image_eq_zero_of_notMem_tsupport fun h' ↦ (hs h').1.false
    have hψT : ψ (t₁ -ᵥ t₀) = 0 := image_eq_zero_of_notMem_tsupport fun h' ↦ (hs h').2.false
    have hvar := hasDerivAt_integral_variation S' t₀ hH (t₁ -ᵥ t₀)
      (fun s ↦ by simp [hHc, hψ0]) fun s ↦ by simp only [hHc, hψT, zero_smul, smul_zero, add_zero]
    have hV (τ : ℝ) : fderiv ℝ Hc (0, τ) (1, 0) = ψ τ • w := by
      rw [← fderiv_curry_fst Hc 0 τ (hH.differentiable (by simp) _) 1, fderiv_apply_one_eq_deriv]
      simp [Function.curry, hHc, deriv_smul_const (hσ.differentiable (by simp) 0), hσ'0]
    rw [show (fun σ' : ℝ ↦ Hc (0, σ')) = q from funext fun σ' ↦ by simp [hHc, hσ0]] at hvar
    simp only [hV] at hvar
    simp_rw [fun s ↦ S.action_eq_intervalIntegral (γ := fun t ↦ h.toFun (s, t)) hT]
    set G : ℝ → ℝ → ℝ := fun s τ ↦ S (τ +ᵥ t₀,
      tangentMap 𝓘(ℝ, ℝ) I (fun t ↦ h.toFun (s, t)) ⟨τ +ᵥ t₀, (1 : ℝ)⟩)
    set Gh : ℝ → ℝ → ℝ := fun s τ ↦ S'.coord t₀ (τ, Hc (s, τ), fderiv ℝ Hc (s, τ) (0, 1))
    have hG0 : IntervalIntegrable (G 0) MeasureTheory.volume 0 (t₁ -ᵥ t₀) :=
      (continuous_iff_continuousAt.2 fun τ ↦ S.continuousAt_action_integrand t₀
        (h.toFun.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)) τ).intervalIntegrable _ _
    have hGh (s : ℝ) : IntervalIntegrable (Gh s) MeasureTheory.volume 0 (t₁ -ᵥ t₀) :=
      ((contDiff_action_integrand S' t₀ hH).continuous.comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    have hkey (s τ : ℝ) : G s τ - Gh s τ = G 0 τ - Gh 0 τ :=
      S.integrand_sub_eq x hc.1 hN hLN hCs hqC hsC w hσ0 hH (fun s τ ↦ rfl)
        (fun s τ hτ ↦ hεN τ hτ (σ s) (hσε s)) (fun s t ↦ h.toFun (s, t)) hoff hsymm s τ
    exact hasDerivAt_intervalIntegral_of_sub_eq hG0 hGh hkey hvar
  exact hD.unique (hc.2 h)

/-!
### B.2. Euler-Lagrange equations in a chart
-/

/-- A critical point `γ` satisfies `∂L/∂q - d/dt ∂L/∂q̇ = 0` in the coordinates of every chart
containing it at time `τ₀`, for any Lagrangian system `S'` on the model space agreeing with the
chart Lagrangian on an open set `N` containing the chart reading of `γ` at `τ₀`. -/
lemma eulerLagrange_eq_zero_of_isCriticalPoint_chart [I.Boundaryless] [FiniteDimensional ℝ E]
    (S : LagrangianSystem I M) {γ : Time → M} {t₀ t₁ : Time}
    (hc : S.IsCriticalPoint γ t₀ t₁) (x : M) {τ₀ : ℝ} (hτ : τ₀ ∈ Ioo 0 (t₁ -ᵥ t₀))
    (hx : γ (τ₀ +ᵥ t₀) ∈ (extChartAt I x).source) (S' : LagrangianSystem 𝓘(ℝ, E) ⟨E⟩)
    {N : Set E} (hNo : IsOpen N) (hqN : extChartAt I x (γ (τ₀ +ᵥ t₀)) ∈ N)
    (hS' : ∀ p : ℝ × E × E, p.2.1 ∈ N → S'.coord t₀ p = S.chartLagrangian x t₀ p) :
    eulerLagrange S' t₀ (fun σ : ℝ ↦ extChartAt I x (γ (σ +ᵥ t₀))) τ₀ = 0 := by
  set O : Set ℝ := Ioo 0 (t₁ -ᵥ t₀) ∩ (fun σ : ℝ ↦ γ (σ +ᵥ t₀)) ⁻¹' (extChartAt I x).source
  have hOo : IsOpen O := isOpen_Ioo.inter ((isOpen_extChartAt_source x).preimage
    (hc.1.continuous.comp (Time.contMDiff_vadd t₀ ∞).continuous))
  have hqO := fun σ (hσ : σ ∈ O) ↦ Time.contDiffAt_extChartAt_comp_vadd x t₀ (hc.1 _) hσ.2
  obtain ⟨d, hd, hCO⟩ : ∃ d > 0, Icc (τ₀ - d) (τ₀ + d) ⊆ O := by
    simpa [Real.closedBall_eq_Icc] using Metric.nhds_basis_closedBall.mem_iff.1
      (hOo.mem_nhds ⟨hτ, hx⟩)
  obtain ⟨q', hq', hq'q⟩ := exists_contDiff_eventuallyEq hOo hqO isCompact_Icc hCO
  have hKt : q' '' Icc (τ₀ - d) (τ₀ + d) ⊆ (extChartAt I x).target := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact (hq'q σ hσ).eq_of_nhds ▸ (extChartAt I x).map_source (hCO hσ).2
  obtain ⟨S'', N'', hNo'', hKN, hNt, hS''⟩ :=
    S.exists_lagrangianSystem_coord_eq x t₀ (isCompact_Icc.image hq'.continuous) hKt
  have hτ₀K : τ₀ ∈ Icc (τ₀ - d) (τ₀ + d) := ⟨by linarith, by linarith⟩
  have hT := (hτ.1.trans hτ.2).le
  have hsub : Ioc (τ₀ - d) (τ₀ + d) ⊆ Ioc 0 (t₁ -ᵥ t₀) := fun σ hσ ↦
    Ioo_subset_Ioc_self (hCO ⟨hσ.1.le, hσ.2⟩).1
  have hzero := eqOn_Icc_zero_of_integral_contDiff_smul_eq_zero
    (contDiff_eulerLagrange hq').continuous.continuousOn (by linarith : τ₀ - d < τ₀ + d)
    fun ψ hψ hψs w ↦ by
      rw [intervalIntegral.integral_of_le (by linarith),
        ← MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hsub
          fun σ hσ ↦ ?_,
        ← intervalIntegral.integral_of_le hT]
      · exact integral_eulerLagrange_eq_zero_of_isCriticalPoint S x hc hT hNo'' hNt hS'' hq'
          isCompact_Icc (fun τ hτ ↦ (hCO hτ).2) hq'q (fun τ hτ ↦ hKN ⟨τ, hτ, rfl⟩) hψ
          (hψs.trans fun σ hσ ↦ (hCO (Ioo_subset_Icc_self hσ)).1)
          (hψs.trans Ioo_subset_Icc_self) w
      · have : ψ σ = 0 :=
          image_eq_zero_of_notMem_tsupport fun h ↦ hσ.2 (Ioo_subset_Ioc_self (hψs h))
        simp [this]
  rw [← eulerLagrange_congr (hq'q τ₀ hτ₀K),
    eulerLagrange_congr_lagrangian (hNo.inter hNo'')
      (hq'.continuous.continuousAt.eventually_mem ((hNo.inter hNo'').mem_nhds
        ⟨(hq'q τ₀ hτ₀K).eq_of_nhds ▸ hqN, hKN ⟨τ₀, hτ₀K, rfl⟩⟩))
      fun p hp ↦ (hS' p hp.1).trans (hS'' p hp.2).symm]
  exact hzero τ₀ hτ₀K

end LagrangianSystem

end ClassicalMechanics
