/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Physlib.ClassicalMechanics.Lagrangian.Basic
public import Physlib.Mathematics.ForMathlib.TangentMap
public import Physlib.SpaceAndTime.Time.ManifoldCurves

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
- `LagrangianSystem.action_integrand_eq_chartLagrangian`: the action integrand in a chart is `L`
- `LagrangianSystem.action_integrand_eq_of_eventuallyEq`: the same for a curve chart-read near a
  time
- `LagrangianSystem.continuousAt_action_integrand`: the action integrand is continuous

## iii. Table of contents

- A. Smooth cutoffs
- B. The Lagrangian in a chart
- C. The action integrand

## iv. References

* I. Terek, Introductory Variational Calculus on Manifolds. [ref: terek_variational_manifolds]
-/

@[expose] public section

open Metric Topology
open scoped Manifold ContDiff
namespace ClassicalMechanics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : ConfigurationSpace I}

/-!
## A. Smooth cutoffs
-/

/-- A smooth cutoff which is `1` on a neighbourhood `N` of a compact set `K` inside an open set `U`
and has topological support inside `U`. -/
private lemma exists_cutoff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (χ : X → ℝ) (N : Set X), ContDiff ℝ ∞ χ ∧ IsOpen N ∧ K ⊆ N ∧ N ⊆ U ∧
      (∀ y ∈ N, χ y = 1) ∧ tsupport χ ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hδ2 : cthickening (δ / 2) K ⊆ thickening δ K :=
    cthickening_subset_thickening' hδ (by linarith) K
  obtain ⟨χ, hχ, -, hχ0, hχ1⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (isOpen_thickening : IsOpen (thickening δ K)).isClosed_compl
    (isClosed_cthickening : IsClosed (cthickening (δ / 2) K))
    (disjoint_compl_left.mono_right hδ2)
  have hsub : thickening (δ / 2) K ⊆ cthickening (δ / 2) K := thickening_subset_cthickening _ _
  refine ⟨χ, thickening (δ / 2) K, hχ, isOpen_thickening, self_subset_thickening (by positivity) K,
    hsub.trans ((cthickening_mono (by linarith) K).trans hδU), fun y hy ↦ (hχ1 _).1 (hsub hy),
    (closure_minimal (fun y hy ↦ ?_) isClosed_cthickening).trans hδU⟩
  by_contra h
  exact hy ((hχ0 _).1 fun h' ↦ h (thickening_subset_cthickening _ _ h'))

/-- `ρ • f` is smooth if `tsupport ρ ⊆ W` and `f` is smooth on `W`. -/
private lemma contDiff_smul_of_cutoff {Y F : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ρ : Y → ℝ} (hρ : ContDiff ℝ ∞ ρ) {W : Set Y}
    (hρ0 : tsupport ρ ⊆ W) {f : Y → F} (hf : ∀ y ∈ W, ContDiffAt ℝ ∞ f y) :
    ContDiff ℝ ∞ fun y ↦ ρ y • f y := by
  refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
  by_cases hy : y ∈ tsupport ρ
  · exact hρ.contDiffAt.smul (hf y (hρ0 hy))
  · refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hy] with z hz
    simp [hz]

namespace LagrangianSystem

/-!
## B. The Lagrangian in a chart
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
  -- identify `𝓘(ℝ, ℝ).prod 𝓘(ℝ, E × E)` with `𝓘(ℝ, ℝ × E × E)`
  rwa [← modelWithCornersSelf_prod (𝕜 := ℝ) (E := ℝ) (F := E × E),
    chartedSpaceSelf_prod (H := ℝ) (H' := E × E), contMDiffAt_iff_contDiffAt] at h

/-- A chart Lagrangian agrees with a globally smooth one near a compact set of positions. -/
lemma exists_contDiff_chartLagrangian_eq [I.Boundaryless] [FiniteDimensional ℝ E]
    (S : LagrangianSystem I M) (x : M) (t₀ : Time) {K : Set E} (hK : IsCompact K)
    (hKx : K ⊆ (extChartAt I x).target) :
    ∃ (L : ℝ × E × E → ℝ) (N : Set E), IsOpen N ∧ K ⊆ N ∧ N ⊆ (extChartAt I x).target ∧
      ContDiff ℝ ∞ L ∧ ∀ p : ℝ × E × E, p.2.1 ∈ N → L p = S.chartLagrangian x t₀ p := by
  obtain ⟨χ, N, hχ, hNo, hKN, hNU, hχ1, hχ0⟩ :=
    exists_cutoff hK (isOpen_extChartAt_target x) hKx
  refine ⟨fun p ↦ χ p.2.1 * S.chartLagrangian x t₀ p, N, hNo, hKN, hNU, ?_, fun p hp ↦ ?_⟩
  · exact contDiff_smul_of_cutoff (hχ.comp (contDiff_fst.comp contDiff_snd))
      (W := {p | p.2.1 ∈ (extChartAt I x).target})
      ((tsupport_comp_subset_preimage χ (continuous_fst.comp continuous_snd)).trans
        (Set.preimage_mono hχ0))
      fun p hp ↦ S.contDiffAt_chartLagrangian x t₀ hp
  · simp [hχ1 _ hp]

/-!
## C. The action integrand
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
  rw [hev.tangentMap_eq (I := 𝓘(ℝ, ℝ)) (I' := I) (p := ⟨τ +ᵥ t₀, (1 : ℝ)⟩), h,
    Time.tangentMap_eq_deriv_vadd]
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
  -- read `γ'` in the chart at its value at `τ`, where the integrand is the smooth chart Lagrangian
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
  · -- near `τ` the curve stays in the chart, where the integrand is the chart Lagrangian
    have hmem : ∀ᶠ σ in 𝓝 τ, γ' (σ +ᵥ t₀) ∈ (extChartAt I x).source :=
      (hγ'.continuous.comp (Time.contMDiff_vadd t₀ ∞).continuous).continuousAt.eventually_mem
        ((isOpen_extChartAt_source x).mem_nhds h0)
    refine hmem.mono fun _ h ↦ S.action_integrand_eq_chartLagrangian x t₀
      (c := fun t ↦ extChartAt I x (γ' t))
      ((hγ'.continuous.continuousAt.eventually_mem
        ((isOpen_extChartAt_source x).mem_nhds h)).mono
          fun _ ht ↦ ((extChartAt I x).left_inv ht).symm)
      ((contMDiffAt_extChartAt' (by rwa [extChartAt_source] at h)).comp _ (hγ' _))
      ((extChartAt I x).map_source h)

end LagrangianSystem

end ClassicalMechanics
