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
# Variations supported in a chart

Variations of a curve supported in a chart, and the first variation of the action along them.

## i. Overview

A bump function and a vector give a variation which in a chart is `q + σ (s) ψ w` on the support of
the bump and the original curve elsewhere. A smooth extension `L` of the chart Lagrangian is a
globally smooth function on `ℝ × E × E` agreeing with it near the chart curve.

## ii. Key results

- `LagrangianSystem.integral_eulerLagrange_eq_zero_of_isCriticalPoint`: the first variation
  vanishes at a critical point

## iii. Table of contents

- A. Gluing
- B. Variations supported in a chart
- C. First variation in a chart

## iv. References

* I. Terek, Introductory Variational Calculus on Manifolds. [ref: terek_variational_manifolds]
-/

@[expose] public section

open Set Topology
open scoped Manifold ContDiff
namespace ClassicalMechanics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : ConfigurationSpace I}

/-!
## A. Gluing
-/

/-- Reading a smooth chart-valued map back in the chart on a closed set of times, and keeping
`γ` elsewhere, is smooth. -/
private lemma contMDiff_ite_symm [I.Boundaryless] (x : M) {γ : Time → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {Z : Set Time} [DecidablePred (· ∈ Z)]
    (hZc : IsClosed Z) {v : ℝ × Time → E}
    (hv : ∀ p : ℝ × Time, p.2 ∈ Z → ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ v p)
    (hvt : ∀ p : ℝ × Time, p.2 ∈ Z → v p ∈ (extChartAt I x).target)
    (hvγ : ∀ p : ℝ × Time, p.2 ∉ Z → v p = extChartAt I x (γ p.2))
    (hZs : ∀ t ∈ Z, γ t ∈ (extChartAt I x).source) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞ fun p : ℝ × Time ↦
      if p.2 ∈ Z then (extChartAt I x).symm (v p) else γ p.2 := by
  intro p
  by_cases hp : p.2 ∈ Z
  · refine (((contMDiffOn_extChartAt_symm x).contMDiffAt
      (extChartAt_target_mem_nhds' (hvt p hp))).comp p (hv p hp)).congr_of_eventuallyEq ?_
    filter_upwards [(hγ.continuous.comp continuous_snd).continuousAt.eventually_mem
      ((isOpen_extChartAt_source x).mem_nhds (hZs _ hp))] with q hq1
    split_ifs with hq
    · rfl
    · simpa [hvγ q hq] using ((extChartAt I x).left_inv hq1).symm
  · refine ((hγ.contMDiffAt (x := p.2)).comp p contMDiff_snd.contMDiffAt).congr_of_eventuallyEq ?_
    filter_upwards [continuous_snd.continuousAt.eventually_mem (hZc.isOpen_compl.mem_nhds hp)]
      with q hq
    exact ite_eq_right hq

/-!
## B. Variations supported in a chart
-/

/-- Glue the chart-read translate `chart γ + σ s • (Ψ • w)` over a closed set `Z` with `γ`. -/
private lemma exists_contMDiff_glue [I.Boundaryless] (x : M) {γ : Time → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {Z : Set Time} (hZc : IsClosed Z)
    {σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) {Ψ : Time → ℝ} (hΨ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Ψ)
    (hΨ0 : ∀ t ∉ Z, Ψ t = 0) (w : E) (hZs : ∀ t ∈ Z, γ t ∈ (extChartAt I x).source)
    (hZt : ∀ t ∈ Z, ∀ s, extChartAt I x (γ t) + σ s • (Ψ t • w) ∈ (extChartAt I x).target) :
    ∃ F : ℝ × Time → M, ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞ F ∧ (∀ s t, t ∉ Z → F (s, t) = γ t) ∧
      ∀ s t, γ t ∈ (extChartAt I x).source →
        F (s, t) = (extChartAt I x).symm (extChartAt I x (γ t) + σ s • (Ψ t • w)) := by
  classical
  refine ⟨_, contMDiff_ite_symm x hγ hZc (v := fun p ↦ extChartAt I x (γ p.2) + σ p.1 • (Ψ p.2 • w))
    (fun p hp ↦ ?_) (fun p hp ↦ hZt _ hp p.1) (fun p hp ↦ by simp [hΨ0 _ hp]) hZs,
    fun s t ht ↦ by simp [ht], fun s t ht ↦ ?_⟩
  · have hch : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (extChartAt I x ∘ γ) p.2 :=
      (contMDiffAt_extChartAt' (by rw [← extChartAt_source I]; exact hZs _ hp)).comp p.2 (hγ p.2)
    exact (hch.comp p contMDiff_snd.contMDiffAt).add
      (((hσ.contMDiff.comp contMDiff_fst).contMDiffAt).smul
        (((hΨ.comp contMDiff_snd).contMDiffAt).smul contMDiffAt_const))
  · by_cases hZ : t ∈ Z
    · simp [hZ]
    · simpa [hZ, hΨ0 _ hZ] using ((extChartAt I x).left_inv ht).symm

/-- A bump function and a vector give a variation of a curve supported in a chart. -/
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
  obtain ⟨σ, hσ, hσ0, hσ'0, hσε⟩ := exists_contDiff_mem_Icc_deriv_zero_eq_one hε
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
## C. First variation in a chart
-/

private lemma eventually_vsub_of_eventually {P : ℝ → Prop} {τ : ℝ} (t₀ : Time)
    (h : ∀ᶠ σ in 𝓝 τ, P σ) : ∀ᶠ t in 𝓝 (τ +ᵥ t₀), P (t -ᵥ t₀) :=
  (Time.contMDiff_vsub t₀ ∞).continuous.continuousAt.eventually (by simpa [vadd_vsub] using h)

/-- Where a curve is the chart-read translate `chart γ + r • (ψ • w)` near `τ`, its action
integrand is `L` evaluated along that chart curve. -/
private lemma LagrangianSystem.integrand_eq_of_eq_add_smul [I.Boundaryless]
    (S : LagrangianSystem I M) (x : M) {γ γs : Time → M} {t₀ : Time} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    {L : ℝ × E × E → ℝ} {N : Set E} (hN : N ⊆ (extChartAt I x).target)
    (hLN : ∀ p : ℝ × E × E, p.2.1 ∈ N → L p = S.chartLagrangian x t₀ p) {q g : ℝ → E}
    (hg : ContDiff ℝ ∞ g) {ψ : ℝ → ℝ} {w : E} {r : ℝ}
    (hgq : ∀ σ, g σ = q σ + r • (ψ σ • w)) {τ : ℝ}
    (hs : γ (τ +ᵥ t₀) ∈ (extChartAt I x).source)
    (hqτ : q =ᶠ[𝓝 τ] fun σ ↦ extChartAt I x (γ (σ +ᵥ t₀))) (hgN : g τ ∈ N)
    (hsymm : ∀ σ, γ (σ +ᵥ t₀) ∈ (extChartAt I x).source → γs (σ +ᵥ t₀) =
      (extChartAt I x).symm (extChartAt I x (γ (σ +ᵥ t₀)) + r • (ψ σ • w))) :
    S (τ +ᵥ t₀, tangentMap 𝓘(ℝ, ℝ) I γs ⟨τ +ᵥ t₀, (1 : ℝ)⟩) = L (τ, g τ, deriv g τ) := by
  refine S.integrand_eq_of_eventuallyEq x t₀ hN hLN hg.contDiffAt hgN ?_
  filter_upwards [hγ.continuous.continuousAt.eventually_mem
    ((isOpen_extChartAt_source x).mem_nhds hs), eventually_vsub_of_eventually t₀ hqτ]
    with t ht1 ht2
  have e := hsymm (t -ᵥ t₀) (by rwa [vsub_vadd])
  rw [vsub_vadd] at e
  simp only [Function.comp, hgq]
  rw [e, ht2, vsub_vadd]

/-- On a chart-supported variation, the difference of the action integrand and the
integrand of `L` is independent of `s`. -/
private lemma LagrangianSystem.integrand_sub_eq [I.Boundaryless] (S : LagrangianSystem I M) (x : M)
    {γ : Time → M} {t₀ : Time} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {L : ℝ × E × E → ℝ} {N : Set E}
    (hN : N ⊆ (extChartAt I x).target)
    (hLN : ∀ p : ℝ × E × E, p.2.1 ∈ N → L p = S.chartLagrangian x t₀ p)
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
        L (τ, Hc (s, τ), fderiv ℝ Hc (s, τ) (0, 1)) =
      S (τ +ᵥ t₀, tangentMap 𝓘(ℝ, ℝ) I (γs 0) ⟨τ +ᵥ t₀, (1 : ℝ)⟩) -
        L (τ, Hc (0, τ), fderiv ℝ Hc (0, τ) (0, 1)) := by
  by_cases hτ : τ ∈ tsupport ψ
  -- on the support both integrands are `L` along the chart variation
  · have hon (s' : ℝ) : S (τ +ᵥ t₀, tangentMap 𝓘(ℝ, ℝ) I (γs s') ⟨τ +ᵥ t₀, (1 : ℝ)⟩) =
        L (τ, Hc (s', τ), fderiv ℝ Hc (s', τ) (0, 1)) := by
      rw [← deriv_snd_eq_fderiv_apply (hH.differentiable (by simp) _)]
      exact S.integrand_eq_of_eq_add_smul x hγ hN hLN (hH.comp (contDiff_const.prodMk contDiff_id))
        (hHdef s') (hCs τ (hsC hτ)) (hqC τ (hsC hτ)) (by simpa [hHdef] using hεN s' τ (hsC hτ))
        (hsymm s')
    simp [hon s, hon 0]
  -- off the support the variation does not move, so both sides are `s`-independent
  · have hnb : ∀ᶠ σ' in 𝓝 τ, σ' ∉ tsupport ψ := (isClosed_tsupport ψ).isOpen_compl.mem_nhds hτ
    have hevs (s' : ℝ) : γs s' =ᶠ[𝓝 (τ +ᵥ t₀)] γ := by
      filter_upwards [eventually_vsub_of_eventually t₀ hnb] with t' ht'
      simpa only [vsub_vadd] using hoff s' (t' -ᵥ t₀) ht'
    have hHev : (fun σ' ↦ Hc (s, σ')) =ᶠ[𝓝 τ] fun σ' ↦ Hc (0, σ') := by
      filter_upwards [hnb] with σ' hσ'
      simp [hHdef, image_eq_zero_of_notMem_tsupport hσ', hσ0]
    rw [(hevs s).tangentMap_eq (I := 𝓘(ℝ, ℝ)) (I' := I) (p := ⟨τ +ᵥ t₀, (1 : ℝ)⟩),
      (hevs 0).tangentMap_eq (I := 𝓘(ℝ, ℝ)) (I' := I) (p := ⟨τ +ᵥ t₀, (1 : ℝ)⟩),
      hHev.eq_of_nhds, ← deriv_snd_eq_fderiv_apply (hH.differentiable (by simp) _),
      ← deriv_snd_eq_fderiv_apply (hH.differentiable (by simp) _), hHev.deriv_eq]

/-- A variation supported in a chart has the first variation of the integral of `L`. -/
private lemma LagrangianSystem.exists_variation_hasDerivAt_action [I.Boundaryless]
    (S : LagrangianSystem I M) (x : M) {γ : Time → M} {t₀ t₁ : Time}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hT : 0 < t₁ -ᵥ t₀)
    {L : ℝ × E × E → ℝ} (hL : ContDiff ℝ ∞ L) {N : Set E} (hN : N ⊆ (extChartAt I x).target)
    (hLN : ∀ p : ℝ × E × E, p.2.1 ∈ N → L p = S.chartLagrangian x t₀ p) {q : ℝ → E}
    (hq : ContDiff ℝ ∞ q) {C : Set ℝ} (hCs : ∀ τ ∈ C, γ (τ +ᵥ t₀) ∈ (extChartAt I x).source)
    (hqC : ∀ τ ∈ C, q =ᶠ[𝓝 τ] fun σ ↦ extChartAt I x (γ (σ +ᵥ t₀))) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hs : tsupport ψ ⊆ Ioo 0 (t₁ -ᵥ t₀)) (hsC : tsupport ψ ⊆ C) (w : E)
    {ε : ℝ} (hε : 0 < ε) (hεN : ∀ τ ∈ C, ∀ r ∈ Icc (-ε) ε, q τ + r • (ψ τ • w) ∈ N) :
    ∃ h : Variation I γ t₀ t₁,
      HasDerivAt (fun s ↦ S.action (fun t ↦ h.toFun (s, t)) t₀ t₁)
        (∫ τ in (0 : ℝ)..(t₁ -ᵥ t₀), eulerLagrange L q τ (ψ τ • w)) 0 := by
  obtain ⟨h, σ, hσ, hσ0, hσ'0, hσε, hoff, hsymm⟩ := exists_variation_chart_bump x hγ hψ hs
    (fun τ hτ ↦ hCs τ (hsC hτ)) w hN hε
    (fun τ hτ r hr ↦ (hqC τ (hsC hτ)).eq_of_nhds ▸ hεN τ (hsC hτ) r hr)
  refine ⟨h, ?_⟩
  -- `Hc` is the chart variation `q + σ s • (ψ • w)`; its first variation is `hvar`
  set Hc : ℝ × ℝ → E := fun p ↦ q p.2 + σ p.1 • (ψ p.2 • w) with hHc
  have hH : ContDiff ℝ ∞ Hc := by fun_prop
  have hψ0 : ψ 0 = 0 := image_eq_zero_of_notMem_tsupport fun h' ↦ (hs h').1.false
  have hψT : ψ (t₁ -ᵥ t₀) = 0 := image_eq_zero_of_notMem_tsupport fun h' ↦ (hs h').2.false
  have hvar := hasDerivAt_integral_variation hL hH (t₁ -ᵥ t₀)
    (fun s ↦ by simp [hHc, hψ0]) fun s ↦ by simp only [hHc, hψT, zero_smul, smul_zero, add_zero]
  have hV : ∀ τ, fderiv ℝ Hc (0, τ) (1, 0) = ψ τ • w := fun τ ↦
    fderiv_apply_fst_of_eq_add_smul (hH.differentiable (by simp) _)
      (hσ.differentiable (by simp) 0) hσ'0 fun s ↦ rfl
  rw [show (fun σ' : ℝ ↦ Hc (0, σ')) = q from funext fun σ' ↦ by simp [hHc, hσ0]] at hvar
  simp only [hV] at hvar
  -- the action integrand and the integrand of `L` differ by an `s`-independent term
  simp_rw [S.action_eq_intervalIntegral hT.le]
  exact hasDerivAt_intervalIntegral_of_sub_const
    ((continuous_iff_continuousAt.2 fun τ ↦ S.continuousAt_integrand t₀
      (h.toFun.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)) τ).intervalIntegrable _ _)
    (fun s ↦ ((contDiff_action_integrand hL hH).continuous.comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
    (fun s τ ↦ S.integrand_sub_eq x hγ hN hLN hCs hqC hsC w hσ0 hH (fun s τ ↦ rfl)
      (fun s τ hτ ↦ hεN τ hτ (σ s) (hσε s)) (fun s t ↦ h.toFun (s, t)) hoff hsymm s τ)
    hvar

/-- At a critical point, the first variation of `L` along a chart-supported bump vanishes. -/
lemma LagrangianSystem.integral_eulerLagrange_eq_zero_of_isCriticalPoint [I.Boundaryless]
    (S : LagrangianSystem I M) (x : M) {γ : Time → M} {t₀ t₁ : Time}
    (hc : S.IsCriticalPoint γ t₀ t₁) (hT : 0 < t₁ -ᵥ t₀)
    {L : ℝ × E × E → ℝ} (hL : ContDiff ℝ ∞ L) {N : Set E} (hNo : IsOpen N)
    (hN : N ⊆ (extChartAt I x).target)
    (hLN : ∀ p : ℝ × E × E, p.2.1 ∈ N → L p = S.chartLagrangian x t₀ p) {q : ℝ → E}
    (hq : ContDiff ℝ ∞ q) {C : Set ℝ} (hC : IsCompact C)
    (hCs : ∀ τ ∈ C, γ (τ +ᵥ t₀) ∈ (extChartAt I x).source)
    (hqC : ∀ τ ∈ C, q =ᶠ[𝓝 τ] fun σ ↦ extChartAt I x (γ (σ +ᵥ t₀))) (hqN : ∀ τ ∈ C, q τ ∈ N)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hs : tsupport ψ ⊆ Ioo 0 (t₁ -ᵥ t₀))
    (hsC : tsupport ψ ⊆ C) (w : E) :
    ∫ τ in (0 : ℝ)..(t₁ -ᵥ t₀), eulerLagrange L q τ (ψ τ • w) = 0 := by
  have hψc : HasCompactSupport ψ := hC.of_isClosed_subset (isClosed_tsupport ψ) hsC
  obtain ⟨B, hB⟩ := hψc.exists_bound_of_continuous hψ.continuous
  obtain ⟨ε, hε, hεN⟩ := (hC.image hq.continuous).exists_eps_add_smul_mem hNo
    (by rintro _ ⟨τ, hτ, rfl⟩; exact hqN τ hτ) (B * ‖w‖)
  obtain ⟨h, hh⟩ := S.exists_variation_hasDerivAt_action x hc.1 hT hL hN hLN hq hCs hqC hψ hs hsC w
    hε fun τ hτ r hr ↦ hεN _ ⟨τ, hτ, rfl⟩ _ (by rw [norm_smul]; gcongr; exact hB τ) r hr
  exact hh.unique (hc.2 h)

end ClassicalMechanics
