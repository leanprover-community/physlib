/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Physlib.ClassicalMechanics.Lagrangian.Basic
public import Physlib.Mathematics.ForMathlib.FDerivCurry
public import Physlib.Mathematics.ForMathlib.Cutoff

/-!
# Lagrangian systems in charts

The Lagrangian in a chart, and the action integrand of a curve read in a chart.

## i. Overview

In a chart `(q, q̇)` are coordinates on the tangent bundle, so the Lagrangian is a function
`L (t, q, q̇)`. For a chart-read curve `c` the action integrand at `τ` is `L (τ, c τ, ċ τ)`.

## ii. Key results

- `LagrangianSystem.chartLagrangian`: `L (t, q, q̇)` in a chart
- `LagrangianSystem.contDiffAt_chartLagrangian`: it is smooth over the chart target
- `LagrangianSystem.exists_contDiff_chartLagrangian_eq`: it agrees with a smooth `L` near a
  compact set
- `LagrangianSystem.exists_lagrangianSystem_coord_eq`: it is the coordinate form of a Lagrangian
  system on `E` near a compact set
- `LagrangianSystem.action_integrand_eq_chartLagrangian`: the action integrand in a chart is `L`
- `LagrangianSystem.action_integrand_eq_of_eventuallyEq`: the same for a curve chart-read near a
  time
- `LagrangianSystem.continuousAt_action_integrand`: the action integrand is continuous
- `LagrangianSystem.integrand_sub_eq`: along a chart-supported variation, the action integrand
  minus that of a Lagrangian system equal to the chart Lagrangian does not depend on the parameter

## iii. Table of contents

- A. The Lagrangian in a chart
- B. The action integrand

## iv. References

* I. Terek, Introductory Variational Calculus on Manifolds. [ref: terek_variational_manifolds]
-/

@[expose] public section

open Topology
open scoped Manifold ContDiff
namespace ClassicalMechanics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : ConfigurationSpace I}

namespace LagrangianSystem

/-!
## A. The Lagrangian in a chart
-/

/-- The Lagrangian in the chart `φ = extChartAt I x`, with time coordinate based at `t₀`:
`L (t, q, q̇) = S (t +ᵥ t₀, d(φ.symm) (q, q̇))`, with generalised coordinates `q` and velocities
`q̇`. It is meaningful only for `q` in the target of `φ`. -/
noncomputable def chartLagrangian (S : LagrangianSystem I M) (x : M) (t₀ : Time) :
    ℝ × E × E → ℝ :=
  fun p ↦ S (p.1 +ᵥ t₀, tangentMap 𝓘(ℝ, E) I (extChartAt I x).symm
    (⟨p.2.1, p.2.2⟩ : TangentBundle 𝓘(ℝ, E) E))

/-- The chart Lagrangian is smooth over the target of the chart. -/
lemma contDiffAt_chartLagrangian [I.Boundaryless] (S : LagrangianSystem I M)
    (x : M) (t₀ : Time) {p : ℝ × E × E} (hp : p.2.1 ∈ (extChartAt I x).target) :
    ContDiffAt ℝ ∞ (S.chartLagrangian x t₀) p := by
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I x).symm p.2.1 :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt (extChartAt_target_mem_nhds' hp)
  have hT : ContMDiffAt 𝓘(ℝ, E).tangent I.tangent ∞
      (tangentMap 𝓘(ℝ, E) I (extChartAt I x).symm) ⟨p.2.1, p.2.2⟩ :=
    ContMDiffAt.contMDiffAt_tangentMap (m := ∞) hsymm (by simp)
  have hι : ContMDiff 𝓘(ℝ, E × E) 𝓘(ℝ, E).tangent ∞
      (fun v : E × E ↦ (⟨v.1, v.2⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_tangentBundleModelSpaceHomeomorph_symm
  have hφ : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E × E)) (𝓘(ℝ, ℝ).prod I.tangent) ∞
      (fun p : ℝ × E × E ↦ (p.1 +ᵥ t₀, tangentMap 𝓘(ℝ, E) I (extChartAt I x).symm
        (⟨p.2.1, p.2.2⟩ : TangentBundle 𝓘(ℝ, E) E))) p :=
    (((Time.contMDiff_vadd t₀ ∞).comp contMDiff_fst).contMDiffAt).prodMk
      (hT.comp p (hι.contMDiffAt.comp p contMDiff_snd.contMDiffAt))
  have h := S.contMDiff.contMDiffAt.comp p hφ
  rwa [← modelWithCornersSelf_prod (𝕜 := ℝ) (E := ℝ) (F := E × E),
    chartedSpaceSelf_prod (H := ℝ) (H' := E × E), contMDiffAt_iff_contDiffAt] at h

/-- A chart Lagrangian agrees with a globally smooth one near a compact set of positions. -/
lemma exists_contDiff_chartLagrangian_eq [I.Boundaryless] [FiniteDimensional ℝ E]
    (S : LagrangianSystem I M) (x : M) (t₀ : Time) {K : Set E} (hK : IsCompact K)
    (hKx : K ⊆ (extChartAt I x).target) :
    ∃ (L : ℝ × E × E → ℝ) (N : Set E), IsOpen N ∧ K ⊆ N ∧ N ⊆ (extChartAt I x).target ∧
      ContDiff ℝ ∞ L ∧ ∀ p : ℝ × E × E, p.2.1 ∈ N → L p = S.chartLagrangian x t₀ p := by
  obtain ⟨χ, N, hχ, hNo, hKN, hNU, hχ1, hχ0⟩ :=
    hK.exists_cutoff (isOpen_extChartAt_target x) hKx
  refine ⟨fun p ↦ χ p.2.1 * S.chartLagrangian x t₀ p, N, hNo, hKN, hNU, ?_, fun p hp ↦ ?_⟩
  · exact contDiff_smul_of_cutoff (hχ.comp (contDiff_fst.comp contDiff_snd))
      (W := {p | p.2.1 ∈ (extChartAt I x).target})
      ((tsupport_comp_subset_preimage χ (continuous_fst.comp continuous_snd)).trans
        (Set.preimage_mono hχ0))
      fun p hp ↦ S.contDiffAt_chartLagrangian x t₀ hp
  · simp [hχ1 _ hp]

/-- Near a compact set of positions, the chart Lagrangian is the coordinate form of a Lagrangian
system on `E`. -/
lemma exists_lagrangianSystem_coord_eq [I.Boundaryless] [FiniteDimensional ℝ E]
    (S : LagrangianSystem I M) (x : M) (t₀ : Time) {K : Set E} (hK : IsCompact K)
    (hKx : K ⊆ (extChartAt I x).target) :
    ∃ (S' : LagrangianSystem 𝓘(ℝ, E) ⟨E⟩) (N : Set E), IsOpen N ∧ K ⊆ N ∧
      N ⊆ (extChartAt I x).target ∧
      ∀ p : ℝ × E × E, p.2.1 ∈ N → S'.coord t₀ p = S.chartLagrangian x t₀ p := by
  obtain ⟨L, N, hNo, hKN, hNt, hL, hLN⟩ := S.exists_contDiff_chartLagrangian_eq x t₀ hK hKx
  refine ⟨ofNormedSpace (fun p ↦ L (p.1 -ᵥ t₀, p.2)) ?_, N, hNo, hKN, hNt,
    fun p hp ↦ by simpa using hLN p hp⟩
  have h : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E × E)) 𝓘(ℝ, ℝ) ∞ L := by
    rwa [← modelWithCornersSelf_prod (𝕜 := ℝ) (E := ℝ) (F := E × E),
      chartedSpaceSelf_prod (H := ℝ) (H' := E × E), contMDiff_iff_contDiff]
  exact h.comp (((Time.contMDiff_vsub t₀ ∞).comp contMDiff_fst).prodMk contMDiff_snd)

/-!
## B. The action integrand
-/

/-- Near a chart-read curve the action integrand is the chart Lagrangian. -/
lemma action_integrand_eq_chartLagrangian [I.Boundaryless]
    (S : LagrangianSystem I M) (x : M) (t₀ : Time) {γ' : Time → M} {c : Time → E} {τ : ℝ}
    (hev : γ' =ᶠ[𝓝 (τ +ᵥ t₀)] (extChartAt I x).symm ∘ c)
    (hc : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c (τ +ᵥ t₀))
    (hcx : c (τ +ᵥ t₀) ∈ (extChartAt I x).target) :
    S (τ +ᵥ t₀, tangentMap 𝓘(ℝ, ℝ) I γ' ⟨τ +ᵥ t₀, (1 : ℝ)⟩) =
      S.chartLagrangian x t₀ (τ, c (τ +ᵥ t₀), deriv (fun σ : ℝ ↦ c (σ +ᵥ t₀)) τ) := by
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I x).symm (c (τ +ᵥ t₀)) :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt (extChartAt_target_mem_nhds' hcx)
  have h := tangentMap_comp_at (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E)) (I'' := I) (f := c)
    (g := (extChartAt I x).symm) (⟨τ +ᵥ t₀, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) Time)
    (hsymm.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))
  rw [Time.tangentMap_eq_of_eventuallyEq hev, h, Time.tangentMap_eq_deriv_vadd]
  rfl

/-- If `γ'` is the chart-read curve `t ↦ (extChartAt I x).symm (c (t -ᵥ t₀))` near `τ +ᵥ t₀` and
`L` agrees with the chart Lagrangian over positions in `N ∋ c τ`, the action integrand at `τ` is
`L (τ, c τ, deriv c τ)`. Here `c` is a function of the time relative to `t₀`. -/
lemma action_integrand_eq_of_eventuallyEq [I.Boundaryless]
    (S : LagrangianSystem I M) (x : M) (t₀ : Time) {γ' : Time → M} {c : ℝ → E} {τ : ℝ}
    {L : ℝ × E × E → ℝ} {N : Set E}
    (hN : N ⊆ (extChartAt I x).target)
    (hLN : ∀ p : ℝ × E × E, p.2.1 ∈ N → L p = S.chartLagrangian x t₀ p) (hc : ContDiffAt ℝ ∞ c τ)
    (hcN : c τ ∈ N)
    (hev : γ' =ᶠ[𝓝 (τ +ᵥ t₀)] (extChartAt I x).symm ∘ fun t ↦ c (t -ᵥ t₀)) :
    S (τ +ᵥ t₀, tangentMap 𝓘(ℝ, ℝ) I γ' ⟨τ +ᵥ t₀, (1 : ℝ)⟩) = L (τ, c τ, deriv c τ) := by
  have hc' : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : Time ↦ c (t -ᵥ t₀)) (τ +ᵥ t₀) := by
    have : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c ((τ +ᵥ t₀) -ᵥ t₀) := by
      rw [vadd_vsub]
      exact contMDiffAt_iff_contDiffAt.2 hc
    exact this.comp (τ +ᵥ t₀) (Time.contMDiff_vsub t₀ ∞).contMDiffAt
  rw [S.action_integrand_eq_chartLagrangian x t₀ hev hc' (by rw [vadd_vsub]; exact hN hcN),
    hLN _ hcN]
  simp

/-- The action integrand of a smooth curve is continuous. -/
lemma continuousAt_action_integrand [I.Boundaryless]
    (S : LagrangianSystem I M) (t₀ : Time) {γ' : Time → M} (hγ' : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ')
    (τ : ℝ) : ContinuousAt (fun τ : ℝ ↦
      S (τ +ᵥ t₀, tangentMap 𝓘(ℝ, ℝ) I γ' ⟨τ +ᵥ t₀, (1 : ℝ)⟩)) τ := by
  set x := γ' (τ +ᵥ t₀)
  have h0 : γ' (τ +ᵥ t₀) ∈ (extChartAt I x).source := mem_extChartAt_source x
  have hg := Time.contDiffAt_extChartAt_comp_vadd x t₀ (hγ' _) h0
  refine ContinuousAt.congr_of_eventuallyEq
    (f := fun σ : ℝ ↦ S.chartLagrangian x t₀ (σ, extChartAt I x (γ' (σ +ᵥ t₀)),
      deriv (fun σ' : ℝ ↦ extChartAt I x (γ' (σ' +ᵥ t₀))) σ)) ?_ ?_
  · exact (S.contDiffAt_chartLagrangian x t₀
      ((extChartAt I x).map_source h0)).continuousAt.comp_of_eq
      (continuousAt_id.prodMk (hg.continuousAt.prodMk
        (hg.derivWithin (m := 0) (by simp)).continuousAt)) rfl
  · have hmem : ∀ᶠ σ in 𝓝 τ, γ' (σ +ᵥ t₀) ∈ (extChartAt I x).source :=
      (hγ'.continuous.comp (Time.contMDiff_vadd t₀ ∞).continuous).continuousAt.eventually_mem
        ((isOpen_extChartAt_source x).mem_nhds h0)
    refine hmem.mono fun _ h ↦ S.action_integrand_eq_chartLagrangian x t₀
      (c := fun t ↦ extChartAt I x (γ' t))
      ((hγ'.continuous.continuousAt.eventually_mem
        ((isOpen_extChartAt_source x).mem_nhds h)).mono
          fun _ ht ↦ ((extChartAt I x).left_inv ht).symm)
      ((contMDiffAt_extChartAt' (by rwa [extChartAt_source] at h)).comp _ (hγ' _))
      ((extChartAt I x).map_source h)

/-- For a variation localised in a chart, the action integrand of `S` and that of a Lagrangian
system `S'` agreeing with the chart Lagrangian differ by an amount independent of the variation
parameter, so the first variation can be computed in coordinates. -/
lemma integrand_sub_eq [I.Boundaryless] (S : LagrangianSystem I M) (x : M)
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
        Time.eventually_vsub t₀ (hqC τ (hsC hτ))] with t ht1 ht2
      have e := hsymm s' (t -ᵥ t₀) (by rwa [vsub_vadd])
      rw [vsub_vadd] at e
      simp only [Function.comp, id, hHdef]
      rw [e, ht2, vsub_vadd]
    simp [hon s, hon 0]
  · have hnb : ∀ᶠ σ' in 𝓝 τ, σ' ∉ tsupport ψ := (isClosed_tsupport ψ).isOpen_compl.mem_nhds hτ
    have hevs (s' : ℝ) : γs s' =ᶠ[𝓝 (τ +ᵥ t₀)] γ := by
      filter_upwards [Time.eventually_vsub t₀ hnb] with t' ht'
      simpa only [vsub_vadd] using hoff s' (t' -ᵥ t₀) ht'
    have hHev : (fun σ' ↦ Hc (s, σ')) =ᶠ[𝓝 τ] fun σ' ↦ Hc (0, σ') := by
      filter_upwards [hnb] with σ' hσ'
      simp [hHdef, image_eq_zero_of_notMem_tsupport hσ', hσ0]
    rw [Time.tangentMap_eq_of_eventuallyEq (hevs s), Time.tangentMap_eq_of_eventuallyEq (hevs 0),
      hHev.eq_of_nhds, ← hd, ← hd, hHev.deriv_eq]

end LagrangianSystem

end ClassicalMechanics
