/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Physlib.ClassicalMechanics.Lagrangian.Chart
public import Physlib.ClassicalMechanics.Lagrangian.CriticalPoint

/-!
# Euler-Lagrange equations in charts

A critical point of the action satisfies the Euler-Lagrange equations in every chart.

## i. Overview

The curve is read in the chart, and the chart Lagrangian, defined only on the chart target, is
extended to a Lagrangian system on the whole normed space agreeing with it near the curve. A bump
function and a vector give a variation supported in the chart, whose first variation of the action
is the integral of the Euler-Lagrange covector against them. It vanishes at a critical point, and
the fundamental lemma of the calculus of variations gives the equations. The converse is not yet
formalised.

## ii. Key results

- `LagrangianSystem.integral_eulerLagrange_eq_zero_of_isCriticalPoint`: the first variation along
  a bump variation supported in a chart vanishes at a critical point
- `LagrangianSystem.eulerLagrange_eq_zero_of_isCriticalPoint_chart`: a critical point satisfies the
  Euler-Lagrange equations in every chart containing it

## iii. Table of contents

- A. Variations supported in a chart
- B. First variation in a chart
- C. Critical points

## iv. References

* I. Terek, Introductory Variational Calculus on Manifolds. [ref: terek_variational_manifolds]
-/

@[expose] public section

open Set Topology Metric
open scoped Manifold ContDiff
namespace ClassicalMechanics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : ConfigurationSpace I}

namespace LagrangianSystem

/-!
## A. Variations supported in a chart
-/

/-- Translating `γ` in the chart by a function of the variation parameter times a bump function of
time times a vector, over a closed set `Z` of times, and keeping `γ` outside `Z`, is smooth. -/
private lemma exists_contMDiff_glue [I.Boundaryless] (x : M) {γ : Time → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {Z : Set Time} (hZc : IsClosed Z)
    {σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) {Ψ : Time → ℝ} (hΨ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Ψ)
    (hΨ0 : ∀ t ∉ Z, Ψ t = 0) (w : E) (hZs : ∀ t ∈ Z, γ t ∈ (extChartAt I x).source)
    (hZt : ∀ t ∈ Z, ∀ s, extChartAt I x (γ t) + σ s • (Ψ t • w) ∈ (extChartAt I x).target) :
    ∃ F : ℝ × Time → M, ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞ F ∧
      (∀ s t, t ∉ Z → F (s, t) = γ t) ∧
      ∀ s t, γ t ∈ (extChartAt I x).source →
        F (s, t) = (extChartAt I x).symm (extChartAt I x (γ t) + σ s • (Ψ t • w)) := by
  classical
  refine ⟨fun p ↦ if p.2 ∈ Z then
    (extChartAt I x).symm (extChartAt I x (γ p.2) + σ p.1 • (Ψ p.2 • w)) else γ p.2,
    fun p ↦ ?_, fun s t ht ↦ by simp [ht], fun s t ht ↦ ?_⟩
  · by_cases hp : p.2 ∈ Z
    · have hch : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (extChartAt I x ∘ γ) p.2 :=
        (contMDiffAt_extChartAt' (by rw [← extChartAt_source I]; exact hZs _ hp)).comp p.2
          (hγ p.2)
      refine (((contMDiffOn_extChartAt_symm x).contMDiffAt
        (extChartAt_target_mem_nhds' (hZt _ hp p.1))).comp p
        ((hch.comp p contMDiff_snd.contMDiffAt).add
          (((hσ.contMDiff.comp contMDiff_fst).contMDiffAt).smul
            (((hΨ.comp contMDiff_snd).contMDiffAt).smul
              contMDiffAt_const)))).congr_of_eventuallyEq ?_
      filter_upwards [(hγ.continuous.comp continuous_snd).continuousAt.eventually_mem
        ((isOpen_extChartAt_source x).mem_nhds (hZs _ hp))] with q hq1
      split_ifs with hq
      · rfl
      · simpa [hΨ0 _ hq] using ((extChartAt I x).left_inv hq1).symm
    · refine ((hγ.contMDiffAt (x := p.2)).comp p contMDiff_snd.contMDiffAt).congr_of_eventuallyEq ?_
      filter_upwards [continuous_snd.continuousAt.eventually_mem (hZc.isOpen_compl.mem_nhds hp)]
        with q hq
      exact ite_eq_right hq
  · by_cases hZ : t ∈ Z
    · simp [hZ]
    · simpa [hZ, hΨ0 _ hZ] using ((extChartAt I x).left_inv ht).symm

/-- A bump function `ψ` supported in `(0, t₁ -ᵥ t₀)` and a vector `w` give a variation of `γ` which
in the chart is the curve translated by `σ s • (ψ • w)`, and `γ` outside the support of `ψ`. Here
`σ` is smooth with `σ 0 = 0`, `σ' 0 = 1` and values in `[-ε, ε]`, small enough that the translated
chart curve stays in a subset `N` of the chart target. -/
private lemma exists_variation_chart_bump [I.Boundaryless] {γ : Time → M} {t₀ t₁ : Time} (x : M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : tsupport ψ ⊆ Ioo 0 (t₁ -ᵥ t₀))
    (hx : ∀ τ ∈ tsupport ψ, γ (τ +ᵥ t₀) ∈ (extChartAt I x).source) (w : E) {N : Set E}
    (hN : N ⊆ (extChartAt I x).target) {ε : ℝ} (hε : 0 < ε)
    (hNε : ∀ τ ∈ tsupport ψ, ∀ r ∈ Icc (-ε) ε,
      extChartAt I x (γ (τ +ᵥ t₀)) + r • (ψ τ • w) ∈ N) :
    ∃ (h : Variation I γ t₀ t₁) (σ : ℝ → ℝ), ContDiff ℝ ∞ σ ∧ σ 0 = 0 ∧ deriv σ 0 = 1 ∧
      (∀ s, σ s ∈ Icc (-ε) ε) ∧ (∀ s τ, τ ∉ tsupport ψ → h.toFun (s, τ +ᵥ t₀) = γ (τ +ᵥ t₀)) ∧
      (∀ s τ, γ (τ +ᵥ t₀) ∈ (extChartAt I x).source → h.toFun (s, τ +ᵥ t₀) =
        (extChartAt I x).symm (extChartAt I x (γ (τ +ᵥ t₀)) + σ s • (ψ τ • w))) := by
  obtain ⟨σ, hσ, hσ0, hσ'0, hσε⟩ : ∃ σ : ℝ → ℝ, ContDiff ℝ ∞ σ ∧ σ 0 = 0 ∧ deriv σ 0 = 1 ∧
      ∀ s, σ s ∈ Icc (-ε) ε :=
    ⟨fun s ↦ ε * Real.sin (s / ε), by fun_prop, by simp, by simp; field_simp, fun s ↦ by
      constructor <;> nlinarith [Real.neg_one_le_sin (s / ε), Real.sin_le_one (s / ε)]⟩
  obtain ⟨F, hF, hnZ, hsymm⟩ := exists_contMDiff_glue x hγ (Z := {t | t -ᵥ t₀ ∈ tsupport ψ})
    ((isClosed_tsupport ψ).preimage (continuous_id.vsub continuous_const)) hσ
    (Ψ := fun t ↦ ψ (t -ᵥ t₀)) ((Time.contMDiff_iff_contDiff_vadd _ t₀ ∞).2 (by simpa using hψ))
    (fun t ht ↦ image_eq_zero_of_notMem_tsupport ht) w
    (fun t ht ↦ by simpa only [vsub_vadd] using hx (t -ᵥ t₀) ht)
    fun t ht s ↦ by simpa only [vsub_vadd] using hN (hNε (t -ᵥ t₀) ht (σ s) (hσε s))
  have h0 (t) : F (0, t) = γ t := by
    by_cases ht : γ t ∈ (extChartAt I x).source
    · simpa [hσ0, hsymm _ _ ht] using (extChartAt I x).left_inv ht
    · exact hnZ _ _ fun hZ ↦ ht (by simpa only [vsub_vadd] using hx _ hZ)
  exact ⟨⟨⟨F, hF⟩, fun s _ ↦ h0 _, fun s ↦ hnZ _ _ fun h ↦ by simpa using (hs h).1,
    fun s ↦ hnZ _ _ fun h ↦ (hs h).2.false⟩, σ, hσ, hσ0, hσ'0, hσε,
    fun s τ hτ ↦ hnZ _ _ (by simpa using hτ), fun s τ hτ ↦ by simpa using hsymm s _ hτ⟩

/-!
## B. First variation in a chart
-/

/-- The tangent map of a curve at a time only depends on the germ of the curve at that time. -/
private lemma tangentMap_eq_of_eventuallyEq {γ γ' : Time → M} {t : Time} (h : γ =ᶠ[𝓝 t] γ') :
    tangentMap 𝓘(ℝ, ℝ) I γ ⟨t, (1 : ℝ)⟩ = tangentMap 𝓘(ℝ, ℝ) I γ' ⟨t, (1 : ℝ)⟩ := by
  refine Bundle.TotalSpace.ext h.eq_of_nhds ?_
  simp only [tangentMap]
  rw [h.mfderiv_eq]
  rfl

private lemma eventually_vsub_of_eventually {P : ℝ → Prop} {τ : ℝ} (t₀ : Time)
    (h : ∀ᶠ σ in 𝓝 τ, P σ) : ∀ᶠ t in 𝓝 (τ +ᵥ t₀), P (t -ᵥ t₀) :=
  (Time.contMDiff_vsub t₀ ∞).continuous.continuousAt.eventually (by simpa [vadd_vsub] using h)

/-- Along a variation supported in a chart, the difference between the action integrand and the
integrand of `S'` does not depend on the variation parameter `s`. -/
private lemma integrand_sub_eq [I.Boundaryless] (S : LagrangianSystem I M) (x : M)
    {γ : Time → M} {t₀ : Time} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    {S' : LagrangianSystem 𝓘(ℝ, E) ⟨E⟩} {N : Set E} (hN : N ⊆ (extChartAt I x).target)
    (hLN : ∀ p : ℝ × E × E, p.2.1 ∈ N → S'.coord t₀ p = S.chartLagrangian x t₀ p)
    {q : ℝ → E} {C : Set ℝ}
    (hCs : ∀ τ ∈ C, γ (τ +ᵥ t₀) ∈ (extChartAt I x).source)
    (hqC : ∀ τ ∈ C, q =ᶠ[𝓝 τ] fun σ ↦ extChartAt I x (γ (σ +ᵥ t₀))) {ψ : ℝ → ℝ}
    (hsC : tsupport ψ ⊆ C) (w : E) {σ : ℝ → ℝ} (hσ0 : σ 0 = 0)
    {Hc : ℝ × ℝ → E} (hH : ContDiff ℝ ∞ Hc) (hHdef : ∀ s τ, Hc (s, τ) = q τ + σ s • (ψ τ • w))
    (hεN : ∀ s, ∀ τ ∈ C, q τ + σ s • (ψ τ • w) ∈ N) (γs : ℝ → Time → M)
    (hoff : ∀ s τ, τ ∉ tsupport ψ → γs s (τ +ᵥ t₀) = γ (τ +ᵥ t₀))
    (hsymm : ∀ s τ, γ (τ +ᵥ t₀) ∈ (extChartAt I x).source → γs s (τ +ᵥ t₀) =
      (extChartAt I x).symm (extChartAt I x (γ (τ +ᵥ t₀)) + σ s • (ψ τ • w))) (s τ : ℝ) :
    S (τ +ᵥ t₀, tangentMap 𝓘(ℝ, ℝ) I (γs s) ⟨τ +ᵥ t₀, (1 : ℝ)⟩) -
        S'.coord t₀ (τ, Hc (s, τ), fderiv ℝ Hc (s, τ) (0, 1)) =
      S (τ +ᵥ t₀, tangentMap 𝓘(ℝ, ℝ) I (γs 0) ⟨τ +ᵥ t₀, (1 : ℝ)⟩) -
        S'.coord t₀ (τ, Hc (0, τ), fderiv ℝ Hc (0, τ) (0, 1)) := by
  have hd (s' τ' : ℝ) : deriv (fun σ' ↦ Hc (s', σ')) τ' = fderiv ℝ Hc (s', τ') (0, 1) := by
    rw [← fderiv_apply_one_eq_deriv]
    exact fderiv_curry_snd Hc s' τ' (hH.differentiable (by simp) _) 1
  by_cases hτ : τ ∈ tsupport ψ
  · have hon (s' : ℝ) : S (τ +ᵥ t₀, tangentMap 𝓘(ℝ, ℝ) I (γs s') ⟨τ +ᵥ t₀, (1 : ℝ)⟩) =
        S'.coord t₀ (τ, Hc (s', τ), fderiv ℝ Hc (s', τ) (0, 1)) := by
      rw [← hd]
      refine S.action_integrand_eq_of_eventuallyEq x t₀ hN hLN
        (hH.comp (contDiff_const.prodMk contDiff_id)).contDiffAt
        (by simpa [hHdef] using hεN s' τ (hsC hτ)) ?_
      filter_upwards [(hγ.continuous.continuousAt).eventually_mem
        ((isOpen_extChartAt_source x).mem_nhds (hCs τ (hsC hτ))),
        eventually_vsub_of_eventually t₀ (hqC τ (hsC hτ))] with t ht1 ht2
      have e := hsymm s' (t -ᵥ t₀) (by rwa [vsub_vadd])
      rw [vsub_vadd] at e
      simp only [Function.comp, id, hHdef]
      rw [e, ht2, vsub_vadd]
    simp [hon s, hon 0]
  · have hnb : ∀ᶠ σ' in 𝓝 τ, σ' ∉ tsupport ψ := (isClosed_tsupport ψ).isOpen_compl.mem_nhds hτ
    have hevs (s' : ℝ) : γs s' =ᶠ[𝓝 (τ +ᵥ t₀)] γ := by
      filter_upwards [eventually_vsub_of_eventually t₀ hnb] with t' ht'
      simpa only [vsub_vadd] using hoff s' (t' -ᵥ t₀) ht'
    have hHev : (fun σ' ↦ Hc (s, σ')) =ᶠ[𝓝 τ] fun σ' ↦ Hc (0, σ') := by
      filter_upwards [hnb] with σ' hσ'
      simp [hHdef, image_eq_zero_of_notMem_tsupport hσ', hσ0]
    rw [tangentMap_eq_of_eventuallyEq (hevs s), tangentMap_eq_of_eventuallyEq (hevs 0),
      hHev.eq_of_nhds, ← hd, ← hd, hHev.deriv_eq]

/-- At a critical point, the first variation of the action along a variation supported in a chart
vanishes: the integral of the Euler-Lagrange covector of `S'` along the chart curve `q`, applied
to `ψ • w`, is zero. Here `S'` agrees with the chart Lagrangian on an open `N` of the chart target,
and `q` is a smooth curve which on a compact set `C` of times is the curve read in the chart and
stays in `N`. -/
lemma integral_eulerLagrange_eq_zero_of_isCriticalPoint [I.Boundaryless]
    (S : LagrangianSystem I M) (x : M) {γ : Time → M} {t₀ t₁ : Time}
    (hc : S.IsCriticalPoint γ t₀ t₁) (hT : 0 < t₁ -ᵥ t₀)
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
  obtain ⟨ε, hε, hεN⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ τ ∈ C, ∀ r ∈ Icc (-ε) ε,
      q τ + r • (ψ τ • w) ∈ N := by
    obtain ⟨r₀, hr₀, hr₀N⟩ := (hC.image hq.continuous).exists_thickening_subset_open hNo
      (image_subset_iff.2 hqN)
    refine ⟨r₀ / (|B * ‖w‖| + 1), by positivity, fun τ hτ r hr ↦ hr₀N ?_⟩
    rw [mem_thickening_iff]
    refine ⟨q τ, ⟨τ, hτ, rfl⟩, ?_⟩
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have hr' : |r| ≤ r₀ / (|B * ‖w‖| + 1) := abs_le.2 ⟨by linarith [hr.1], hr.2⟩
    have hv : ‖ψ τ • w‖ ≤ |B * ‖w‖| := by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_right (hB τ) (norm_nonneg w)).trans (le_abs_self _)
    calc |r| * ‖ψ τ • w‖ ≤ r₀ / (|B * ‖w‖| + 1) * |B * ‖w‖| := by gcongr
      _ < r₀ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg (B * ‖w‖)]
  obtain ⟨h, σ, hσ, hσ0, hσ'0, hσε, hoff, hsymm⟩ := exists_variation_chart_bump x hc.1 hψ hs
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
    have hact (s : ℝ) : S.action (fun t ↦ h.toFun (s, t)) t₀ t₁ =
        ∫ τ in (0 : ℝ)..(t₁ -ᵥ t₀), S (τ +ᵥ t₀,
          tangentMap 𝓘(ℝ, ℝ) I (fun t ↦ h.toFun (s, t)) ⟨τ +ᵥ t₀, (1 : ℝ)⟩) := by
      rw [action, intervalIntegral.integral_of_le hT.le,
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    simp_rw [hact]
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
      integrand_sub_eq S x hc.1 hN hLN hCs hqC hsC w hσ0 hH (fun s τ ↦ rfl)
        (fun s τ hτ ↦ hεN τ hτ (σ s) (hσε s)) (fun s t ↦ h.toFun (s, t)) hoff hsymm s τ
    have hsplit (s : ℝ) : ∫ τ in (0 : ℝ)..(t₁ -ᵥ t₀), G s τ =
        (∫ τ in (0 : ℝ)..(t₁ -ᵥ t₀), Gh s τ) +
          ∫ τ in (0 : ℝ)..(t₁ -ᵥ t₀), (G 0 τ - Gh 0 τ) := by
      rw [← intervalIntegral.integral_add (hGh s) (hG0.sub (hGh 0))]
      exact intervalIntegral.integral_congr fun τ _ ↦ by simp only [← hkey s τ, add_sub_cancel]
    rw [show (fun s ↦ ∫ τ in (0 : ℝ)..(t₁ -ᵥ t₀), G s τ) = _ from funext hsplit]
    exact hvar.add_const _
  exact hD.unique (hc.2 h)

/-!
## C. Critical points
-/

/-- A critical point satisfies the Euler-Lagrange equations in every chart containing it, for any
Lagrangian system `S'` on `E` whose coordinate form is the chart Lagrangian on the chart target. -/
lemma eulerLagrange_eq_zero_of_isCriticalPoint_chart [I.Boundaryless] [FiniteDimensional ℝ E]
    (S : LagrangianSystem I M) {γ : Time → M} {t₀ t₁ : Time}
    (hc : S.IsCriticalPoint γ t₀ t₁) (x : M) {τ₀ : ℝ} (hτ : τ₀ ∈ Ioo 0 (t₁ -ᵥ t₀))
    (hx : γ (τ₀ +ᵥ t₀) ∈ (extChartAt I x).source) (S' : LagrangianSystem 𝓘(ℝ, E) ⟨E⟩)
    (hS' : ∀ p : ℝ × E × E, p.2.1 ∈ (extChartAt I x).target →
      S'.coord t₀ p = S.chartLagrangian x t₀ p) :
    eulerLagrange S' t₀ (fun σ : ℝ ↦ extChartAt I x (γ (σ +ᵥ t₀))) τ₀ = 0 := by
  set O : Set ℝ := Ioo 0 (t₁ -ᵥ t₀) ∩ (fun σ : ℝ ↦ γ (σ +ᵥ t₀)) ⁻¹' (extChartAt I x).source
  have hOo : IsOpen O := isOpen_Ioo.inter ((isOpen_extChartAt_source x).preimage
    (hc.1.continuous.comp (Time.contMDiff_vadd t₀ ∞).continuous))
  have hqO := fun σ (hσ : σ ∈ O) ↦ Time.contDiffAt_extChartAt_comp_vadd x t₀ (hc.1 _) hσ.2
  obtain ⟨d, hd, hCO⟩ : ∃ d > 0, Icc (τ₀ - d) (τ₀ + d) ⊆ O := by
    simpa [Real.closedBall_eq_Icc] using Metric.nhds_basis_closedBall.mem_iff.1
      (hOo.mem_nhds ⟨hτ, hx⟩)
  obtain ⟨q', hq', hq'q⟩ : ∃ g : ℝ → E, ContDiff ℝ ∞ g ∧ ∀ σ ∈ Icc (τ₀ - d) (τ₀ + d),
      g =ᶠ[𝓝 σ] fun σ' ↦ extChartAt I x (γ (σ' +ᵥ t₀)) := by
    obtain ⟨ρ, N, hρ, hNo, hCN, -, hρ1, hρ0⟩ := isCompact_Icc.exists_cutoff hOo hCO
    exact ⟨fun σ ↦ ρ σ • extChartAt I x (γ (σ +ᵥ t₀)), contDiff_smul_of_cutoff hρ hρ0 hqO,
      fun σ hσ ↦ by
        filter_upwards [hNo.mem_nhds (hCN hσ)] with σ' hσ'
        simp [hρ1 _ hσ']⟩
  have hKt : q' '' Icc (τ₀ - d) (τ₀ + d) ⊆ (extChartAt I x).target := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact (hq'q σ hσ).eq_of_nhds ▸ (extChartAt I x).map_source (hCO hσ).2
  obtain ⟨S'', N, hNo, hKN, hNt, hLN⟩ :=
    S.exists_lagrangianSystem_coord_eq x t₀ (isCompact_Icc.image hq'.continuous) hKt
  have hτ₀U : τ₀ ∈ Ioo (τ₀ - d) (τ₀ + d) := ⟨by linarith, by linarith⟩
  have hT : 0 < t₁ -ᵥ t₀ := hτ.1.trans hτ.2
  have hzero := eqOn_Icc_zero_of_integral_contDiff_smul_eq_zero
    (contDiff_eulerLagrange hq').continuous.continuousOn (by linarith : τ₀ - d < τ₀ + d)
    fun ψ hψ hψs w ↦ by
      rw [intervalIntegral.integral_of_le (by linarith),
        ← MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
          (fun σ hσ ↦ Ioo_subset_Ioc_self (hCO ⟨hσ.1.le, hσ.2⟩).1) fun σ hσ ↦ ?_,
        ← intervalIntegral.integral_of_le hT.le]
      · exact integral_eulerLagrange_eq_zero_of_isCriticalPoint S x hc hT hNo hNt hLN hq'
          isCompact_Icc (fun τ hτ ↦ (hCO hτ).2) hq'q (fun τ hτ ↦ hKN ⟨τ, hτ, rfl⟩) hψ
          (hψs.trans fun σ hσ ↦ (hCO (Ioo_subset_Icc_self hσ)).1)
          (hψs.trans Ioo_subset_Icc_self) w
      · have : ψ σ = 0 :=
          image_eq_zero_of_notMem_tsupport fun h ↦ hσ.2 (Ioo_subset_Ioc_self (hψs h))
        simp [this]
  rw [← eulerLagrange_congr (hq'q τ₀ (Ioo_subset_Icc_self hτ₀U)),
    eulerLagrange_congr_lagrangian hNo
      (hq'.continuous.continuousAt.eventually_mem
        (hNo.mem_nhds (hKN ⟨τ₀, Ioo_subset_Icc_self hτ₀U, rfl⟩)))
      fun p hp ↦ (hS' p (hNt hp)).trans (hLN p hp).symm]
  exact hzero τ₀ (Ioo_subset_Icc_self hτ₀U)

end LagrangianSystem

end ClassicalMechanics
