/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Physlib.ClassicalMechanics.Lagrangian.Chart
public import Physlib.ClassicalMechanics.Lagrangian.FirstVariation
public import Physlib.ClassicalMechanics.Lagrangian.NormedSpace

/-!
# Variations supported in a chart

Variations of a curve supported in a chart, and the first variation of the action along them.

## i. Overview

A bump function and a vector give a variation which in a chart is `q + σ (s) ψ w` on the support of
the bump and the original curve elsewhere.

## ii. Key results

- `exists_variation_chart_bump`
- `LagrangianSystem.exists_hasDerivAt_action_chart`

## iii. Table of contents

- A. Gluing
- B. Variations supported in a chart
- C. First variation in a chart

## iv. References

* I. Terek, Introductory Variational Calculus on Manifolds. [ref: terek_variational_manifolds]
-/

@[expose] public section

open Set MeasureTheory Filter Topology Metric
open scoped Manifold ContDiff
namespace ClassicalMechanics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : ConfigurationSpace I}

/-!
## A. Gluing
-/

/-- Reading a smooth chart-valued map back in the chart on a closed set of times, and keeping
`γ` elsewhere, is smooth. -/
lemma contMDiff_ite_symm [I.Boundaryless] (x : M) {γ : Time → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {Z : Set Time} [DecidablePred (· ∈ Z)] (hZc : IsClosed Z)
    {v : ℝ × Time → E}
    (hv : ∀ p : ℝ × Time, p.2 ∈ Z → ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞ v p)
    (hvt : ∀ p : ℝ × Time, p.2 ∈ Z → v p ∈ (extChartAt I x).target)
    (hvγ : ∀ p : ℝ × Time, p.2 ∉ Z → v p = extChartAt I x (γ p.2))
    (hZs : ∀ t ∈ Z, γ t ∈ (extChartAt I x).source) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞ fun p : ℝ × Time ↦
      if p.2 ∈ Z then (extChartAt I x).symm (v p) else γ p.2 := by
  intro p
  by_cases hp : p.2 ∈ Z
  · have hG : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞ (fun q ↦ (extChartAt I x).symm (v q)) p :=
      ((contMDiffOn_extChartAt_symm x).contMDiffAt
        (extChartAt_target_mem_nhds' (hvt p hp))).comp p (hv p hp)
    refine hG.congr_of_eventuallyEq ?_
    have h1 : ∀ᶠ q : ℝ × Time in 𝓝 p, γ q.2 ∈ (extChartAt I x).source :=
      (hγ.continuous.comp continuous_snd).continuousAt.eventually_mem
        ((isOpen_extChartAt_source x).mem_nhds (hZs _ hp))
    filter_upwards [h1] with q hq1
    by_cases hq : q.2 ∈ Z
    · simp [hq]
    · simp only [hq, ite_false, hvγ q hq]
      exact ((extChartAt I x).left_inv hq1).symm
  · have hev : ∀ᶠ q : ℝ × Time in 𝓝 p, q.2 ∉ Z :=
      continuous_snd.continuousAt.eventually_mem (hZc.isOpen_compl.mem_nhds hp)
    refine ((hγ.contMDiffAt (x := p.2)).comp p contMDiff_snd.contMDiffAt).congr_of_eventuallyEq ?_
    filter_upwards [hev] with q hq
    simp [hq]

/-!
## B. Variations supported in a chart
-/

/-- A bump function and a vector give a variation of a curve supported in a chart. -/
lemma exists_variation_chart_bump [I.Boundaryless] {γ : Time → M} {t₀ t₁ : Time} (x : M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : tsupport ψ ⊆ Ioo 0 (t₁ -ᵥ t₀))
    (hx : ∀ τ ∈ tsupport ψ, γ (τ +ᵥ t₀) ∈ (extChartAt I x).source) (w : E) {N : Set E}
    (hN : N ⊆ (extChartAt I x).target) {ε : ℝ} (hε : 0 < ε)
    (hNε : ∀ τ ∈ tsupport ψ, ∀ r ∈ Icc (-ε) ε,
      extChartAt I x (γ (τ +ᵥ t₀)) + r • (ψ τ • w) ∈ N) :
    ∃ (h : Variation I γ t₀ t₁) (σ : ℝ → ℝ), ContDiff ℝ ∞ σ ∧ σ 0 = 0 ∧ deriv σ 0 = 1 ∧
      (∀ s, σ s ∈ Icc (-ε) ε) ∧
      (∀ s τ, τ ∉ tsupport ψ → h.toFun (s, τ +ᵥ t₀) = γ (τ +ᵥ t₀)) ∧
      (∀ s τ, γ (τ +ᵥ t₀) ∈ (extChartAt I x).source → h.toFun (s, τ +ᵥ t₀) =
        (extChartAt I x).symm (extChartAt I x (γ (τ +ᵥ t₀)) + σ s • (ψ τ • w))) := by
  classical
  obtain ⟨σ, hσ, hσ0, hσ'0, hσε⟩ := exists_reparam hε
  set Ψ : Time → ℝ := fun t ↦ ψ (t -ᵥ t₀) with hΨ
  have hΨs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ Ψ :=
    (Time.contMDiff_iff_contDiff_vadd _ t₀ ∞).2 (by simpa [hΨ] using hψ)
  set Z : Set Time := {t | t -ᵥ t₀ ∈ tsupport ψ} with hZ
  have hZc : IsClosed Z := (isClosed_tsupport ψ).preimage (continuous_id.vsub continuous_const)
  have hZsrc : ∀ t ∈ Z, γ t ∈ (extChartAt I x).source := fun t ht ↦ by
    have := hx (t -ᵥ t₀) ht
    rwa [vsub_vadd] at this
  have hZtgt : ∀ t ∈ Z, ∀ s, extChartAt I x (γ t) + σ s • (Ψ t • w) ∈ (extChartAt I x).target :=
    fun t ht s ↦ by
      have := hN (hNε (t -ᵥ t₀) ht (σ s) (hσε s))
      rwa [vsub_vadd] at this
  have hΨ0 : ∀ t ∉ Z, Ψ t = 0 := fun t ht ↦ image_eq_zero_of_notMem_tsupport (f := ψ) ht
  let F : ℝ × Time → M := fun p ↦ if p.2 ∈ Z then
    (extChartAt I x).symm (extChartAt I x (γ p.2) + σ p.1 • (Ψ p.2 • w)) else γ p.2
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞ F := by
    refine contMDiff_ite_symm x hγ hZc (fun p hp ↦ ?_) (fun p hp ↦ hZtgt _ hp p.1)
      (fun p hp ↦ by simp [hΨ0 _ hp]) hZsrc
    have hch : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (extChartAt I x ∘ γ) p.2 :=
      (contMDiffAt_extChartAt' (by rw [← extChartAt_source I]; exact hZsrc _ hp)).comp p.2
        (hγ p.2)
    exact (hch.comp p contMDiff_snd.contMDiffAt).add
      (((hσ.contMDiff.comp contMDiff_fst).contMDiffAt).smul
        (((hΨs.comp contMDiff_snd).contMDiffAt).smul contMDiffAt_const))
  have h0 : t₀ ∉ Z := fun ht ↦ by simpa using (hs ht).1
  have h1 : t₁ ∉ Z := fun ht ↦ (hs ht).2.false
  have hFZ : ∀ s t, t ∈ Z → F (s, t) =
      (extChartAt I x).symm (extChartAt I x (γ t) + σ s • (Ψ t • w)) := fun s t ht ↦ by
    simp [F, ht]
  have hFnZ : ∀ s t, t ∉ Z → F (s, t) = γ t := fun s t ht ↦ by simp [F, ht]
  refine ⟨⟨⟨F, hF⟩, fun s _ ↦ ?_, fun s ↦ ?_, fun s ↦ ?_⟩, σ, hσ, hσ0, hσ'0, hσε, ?_, ?_⟩
  · by_cases ht : s +ᵥ t₀ ∈ Z
    · show F (0, s +ᵥ t₀) = _
      rw [hFZ _ _ ht, hσ0]
      simpa using (extChartAt I x).left_inv (hZsrc _ ht)
    · exact hFnZ _ _ ht
  · exact hFnZ _ _ h0
  · exact hFnZ _ _ h1
  · intro s τ hτ
    exact hFnZ _ _ (by simpa [hZ] using hτ)
  · intro s τ hτ
    show F (s, τ +ᵥ t₀) = _
    by_cases ht : τ +ᵥ t₀ ∈ Z
    · rw [hFZ _ _ ht]
      simp [hΨ]
    · have hψ0 : ψ τ = 0 := image_eq_zero_of_notMem_tsupport (by simpa [hZ] using ht)
      rw [hFnZ _ _ ht, hψ0]
      simpa using ((extChartAt I x).left_inv hτ).symm

/-!
## C. First variation in a chart
-/

/-- On a chart-supported variation, the geometric action integrand is the flat one on the support
and the two differ by an `s`-independent amount. -/
lemma LagrangianSystem.integrand_sub_eq [I.Boundaryless] (S : LagrangianSystem I M) (x : M)
    {γ : Time → M} {t₀ : Time} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {L : ℝ × E × E → ℝ} {N : Set E}
    (hN : N ⊆ (extChartAt I x).target)
    (hLN : ∀ p : ℝ × E × E, p.2.1 ∈ N → L p = S.coord x t₀ p) {q : ℝ → E}
    (hq : ContDiff ℝ ∞ q) {C : Set ℝ} (hCs : ∀ τ ∈ C, γ (τ +ᵥ t₀) ∈ (extChartAt I x).source)
    (hqC : ∀ τ ∈ C, q =ᶠ[𝓝 τ] fun σ ↦ extChartAt I x (γ (σ +ᵥ t₀))) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hsC : tsupport ψ ⊆ C) (w : E) {σ : ℝ → ℝ}
    (hσ0 : σ 0 = 0) {Hc : ℝ × ℝ → E} (hH : ContDiff ℝ ∞ Hc)
    (hHdef : ∀ s τ, Hc (s, τ) = q τ + σ s • (ψ τ • w))
    (hεN : ∀ s, ∀ τ ∈ C, q τ + σ s • (ψ τ • w) ∈ N) (γs : ℝ → Time → M)
    (hoff : ∀ s τ, τ ∉ tsupport ψ → γs s (τ +ᵥ t₀) = γ (τ +ᵥ t₀))
    (hsymm : ∀ s τ, γ (τ +ᵥ t₀) ∈ (extChartAt I x).source → γs s (τ +ᵥ t₀) =
      (extChartAt I x).symm (extChartAt I x (γ (τ +ᵥ t₀)) + σ s • (ψ τ • w))) (s τ : ℝ) :
    S (τ +ᵥ t₀, tangentMap 𝓘(ℝ, ℝ) I (γs s) ⟨τ +ᵥ t₀, (1 : ℝ)⟩) -
        L (τ, Hc (s, τ), fderiv ℝ Hc (s, τ) (0, 1)) =
      S (τ +ᵥ t₀, tangentMap 𝓘(ℝ, ℝ) I (γs 0) ⟨τ +ᵥ t₀, (1 : ℝ)⟩) -
        L (τ, Hc (0, τ), fderiv ℝ Hc (0, τ) (0, 1)) := by
  by_cases hτ : τ ∈ tsupport ψ
  · have hon : ∀ s', S (τ +ᵥ t₀, tangentMap 𝓘(ℝ, ℝ) I (γs s') ⟨τ +ᵥ t₀, (1 : ℝ)⟩) =
        L (τ, Hc (s', τ), fderiv ℝ Hc (s', τ) (0, 1)) := fun s' ↦ by
      have hτC := hsC hτ
      have hGfs : ContDiff ℝ ∞ fun σ' ↦ q σ' + σ s' • (ψ σ' • w) :=
        hq.add (contDiff_const.smul (hψ.smul contDiff_const))
      have hsrcev : ∀ᶠ t' in 𝓝 (τ +ᵥ t₀), γ t' ∈ (extChartAt I x).source :=
        hγ.continuous.continuousAt.eventually_mem
          ((isOpen_extChartAt_source x).mem_nhds (hCs τ hτC))
      have hqC' : ∀ᶠ σ' in 𝓝 ((τ +ᵥ t₀) -ᵥ t₀), q σ' = extChartAt I x (γ (σ' +ᵥ t₀)) := by
        rw [vadd_vsub]; exact hqC τ hτC
      have hqev := (Time.contMDiff_vsub t₀ ∞).continuous.continuousAt.eventually hqC'
      have hev : γs s' =ᶠ[𝓝 (τ +ᵥ t₀)] (extChartAt I x).symm ∘ fun t' ↦
          (q (t' -ᵥ t₀) + σ s' • (ψ (t' -ᵥ t₀) • w)) := by
        filter_upwards [hsrcev, hqev] with t' ht1 ht2
        have e := hsymm s' (t' -ᵥ t₀) (by rw [vsub_vadd]; exact ht1)
        rw [vsub_vadd] at e
        show γs s' t' = (extChartAt I x).symm (q (t' -ᵥ t₀) + σ s' • (ψ (t' -ᵥ t₀) • w))
        rw [e, ht2, vsub_vadd]
      rw [S.integrand_eq_of_germ x t₀ hN hLN hGfs.contDiffAt (hεN s' τ hτC) hev]
      have : (fun σ' ↦ Hc (s', σ')) = fun σ' ↦ q σ' + σ s' • (ψ σ' • w) :=
        funext fun σ' ↦ hHdef s' σ'
      rw [← fderiv_snd_apply hH s' τ, this, hHdef]
    rw [hon s, hon 0]; simp
  · have hψτ : ψ τ = 0 := image_eq_zero_of_notMem_tsupport hτ
    have hnb : (tsupport ψ)ᶜ ∈ 𝓝 τ := (isClosed_tsupport ψ).isOpen_compl.mem_nhds hτ
    have hopen : ∀ᶠ t' in 𝓝 (τ +ᵥ t₀), t' -ᵥ t₀ ∉ tsupport ψ :=
      (Time.contMDiff_vsub t₀ ∞).continuous.continuousAt.eventually_mem
        (by rw [vadd_vsub]; exact hnb)
    have hevs : ∀ s', γs s' =ᶠ[𝓝 (τ +ᵥ t₀)] γ := fun s' ↦ by
      filter_upwards [hopen] with t' ht'
      have := hoff s' (t' -ᵥ t₀) ht'
      rwa [vsub_vadd] at this
    have hH0 : Hc (s, τ) = Hc (0, τ) := by simp [hHdef, hψτ]
    have hd : fderiv ℝ Hc (s, τ) (0, 1) = fderiv ℝ Hc (0, τ) (0, 1) := by
      rw [← fderiv_snd_apply hH s τ, ← fderiv_snd_apply hH 0 τ]
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [hnb] with σ' hσ'
      have : ψ σ' = 0 := image_eq_zero_of_notMem_tsupport hσ'
      simp [hHdef, this, hσ0]
    rw [tangentMap_eq_of_eventuallyEq (hevs s), tangentMap_eq_of_eventuallyEq (hevs 0), hH0, hd]

/-- A variation supported in a chart has the first variation of the flat Lagrangian. -/
lemma LagrangianSystem.exists_hasDerivAt_action_chart [I.Boundaryless]
    (S : LagrangianSystem I M) (x : M) {γ : Time → M} {t₀ t₁ : Time}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hT : 0 < t₁ -ᵥ t₀) {L : ℝ × E × E → ℝ}
    (hL : ContDiff ℝ ∞ L) {N : Set E} (hN : N ⊆ (extChartAt I x).target)
    (hLN : ∀ p : ℝ × E × E, p.2.1 ∈ N → L p = S.coord x t₀ p) {q : ℝ → E}
    (hq : ContDiff ℝ ∞ q) {C : Set ℝ} (hCs : ∀ τ ∈ C, γ (τ +ᵥ t₀) ∈ (extChartAt I x).source)
    (hqC : ∀ τ ∈ C, q =ᶠ[𝓝 τ] fun σ ↦ extChartAt I x (γ (σ +ᵥ t₀))) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hs : tsupport ψ ⊆ Ioo 0 (t₁ -ᵥ t₀)) (hsC : tsupport ψ ⊆ C) (w : E)
    {ε : ℝ} (hε : 0 < ε)
    (hεN : ∀ τ ∈ C, ∀ r ∈ Icc (-ε) ε, q τ + r • (ψ τ • w) ∈ N) :
    ∃ h : Variation I γ t₀ t₁,
      HasDerivAt (fun s ↦ S.action (fun t ↦ h.toFun (s, t)) t₀ t₁)
        (∫ τ in (0 : ℝ)..(t₁ -ᵥ t₀), eulerLagrange L q τ (ψ τ • w)) 0 := by
  obtain ⟨h, σ, hσ, hσ0, hσ'0, hσε, hoff, hsymm⟩ := exists_variation_chart_bump x hγ hψ hs
    (fun τ hτ ↦ hCs τ (hsC hτ)) w hN hε
    (fun τ hτ r hr ↦ by rw [← (hqC τ (hsC hτ)).eq_of_nhds]; exact hεN τ (hsC hτ) r hr)
  refine ⟨h, ?_⟩
  set Hc : ℝ × ℝ → E := fun p ↦ q p.2 + σ p.1 • (ψ p.2 • w) with hHc
  have hH : ContDiff ℝ ∞ Hc :=
    (hq.comp contDiff_snd).add
      ((hσ.comp contDiff_fst).smul ((hψ.comp contDiff_snd).smul contDiff_const))
  have hψ0 : ψ 0 = 0 := image_eq_zero_of_notMem_tsupport fun h' ↦ (hs h').1.false
  have hψT : ψ (t₁ -ᵥ t₀) = 0 := image_eq_zero_of_notMem_tsupport fun h' ↦ (hs h').2.false
  have hflat := hasDerivAt_integral_variation hL hH (t₁ -ᵥ t₀)
    (fun s ↦ by simp only [hHc, hψ0, zero_smul, smul_zero, add_zero])
    (fun s ↦ by simp only [hHc, hψT, zero_smul, smul_zero, add_zero])
  have hV : ∀ τ, fderiv ℝ Hc (0, τ) (1, 0) = ψ τ • w := fun τ ↦ by
    rw [← fderiv_fst_apply hH 0 τ]
    have : HasDerivAt (fun r : ℝ ↦ Hc (r, τ)) (deriv σ 0 • (ψ τ • w)) 0 :=
      (((hσ.differentiable (by simp) 0).hasDerivAt).smul_const (ψ τ • w)).const_add (q τ)
    rw [this.deriv, hσ'0, one_smul]
  rw [show (fun σ' : ℝ ↦ Hc (0, σ')) = q from funext fun σ' ↦ by simp [hHc, hσ0]] at hflat
  simp only [hV] at hflat
  have hγs : ∀ s : ℝ, ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun t ↦ h.toFun (s, t)) := fun s ↦
    h.toFun.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)
  have hact : ∀ s, S.action (fun t ↦ h.toFun (s, t)) t₀ t₁ = ∫ τ in (0 : ℝ)..(t₁ -ᵥ t₀),
      S (τ +ᵥ t₀, tangentMap 𝓘(ℝ, ℝ) I (fun t ↦ h.toFun (s, t)) ⟨τ +ᵥ t₀, (1 : ℝ)⟩) := fun s ↦ by
    rw [intervalIntegral.integral_of_le hT.le, ← integral_Icc_eq_integral_Ioc]
    rfl
  rw [show (fun s ↦ S.action (fun t ↦ h.toFun (s, t)) t₀ t₁) = _ from funext hact]
  exact hasDerivAt_integral_of_sub_eq
    (fun s ↦ continuous_iff_continuousAt.2 fun τ ↦ S.continuousAt_integrand t₀ (hγs s) τ)
    (fun s ↦ hL.continuous.comp
      (continuous_id.prodMk ((hH.continuous.comp (continuous_const.prodMk continuous_id)).prodMk
        ((hH.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_id)
          |>.clm_apply continuous_const))))
    (fun s τ ↦ S.integrand_sub_eq x hγ hN hLN hq hCs hqC hψ hsC w hσ0 hH (fun s τ ↦ rfl)
      (fun s τ hτ ↦ hεN τ hτ (σ s) (hσε s)) (fun s t ↦ h.toFun (s, t)) hoff hsymm s τ)
    hflat

end ClassicalMechanics
