/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Physlib.ClassicalMechanics.Lagrangian.Basic
public import Physlib.Mathematics.ForMathlib.ContMDiffProd
public import Physlib.Mathematics.ForMathlib.Cutoff
public import Physlib.Mathematics.ForMathlib.TangentMap
public import Physlib.SpaceAndTime.Time.ManifoldCurves

/-!
# Lagrangian systems in charts

The Lagrangian in a chart, and the action integrand of a curve read in a chart.

## i. Overview

A chart induces coordinates `(q, q̇)` on the tangent bundle through the tangent map of its inverse,
turning the Lagrangian into a function `L (t, q, q̇)` smooth over the chart target.

## ii. Key results

- `LagrangianSystem.chartLagrangian`
- `LagrangianSystem.contDiffAt_chartLagrangian`
- `LagrangianSystem.integrand_eq_chartLagrangian`: the action integrand in a chart is the chart
  Lagrangian
- `LagrangianSystem.exists_contDiff_chartLagrangian_eq`: the chart Lagrangian agrees with a smooth
  one
  near a compact set
- `LagrangianSystem.continuousAt_integrand`: the action integrand is continuous
- `contDiffAt_chart_curve`: a chart-read curve is smooth
- `LagrangianSystem.integrand_eq_of_germ`: the action integrand of a curve that is chart-read
  near a time

## iii. Table of contents

- A. The Lagrangian in a chart
- B. Curves read in a chart
- C. The action integrand

## iv. References

* I. Terek, Introductory Variational Calculus on Manifolds. [ref: terek_variational_manifolds]
-/

@[expose] public section

open Topology
open scoped Manifold ContDiff
namespace ClassicalMechanics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : ConfigurationSpace I}

/-!
## A. The Lagrangian in a chart
-/

/-- The Lagrangian in the chart at `x`, with time coordinate based at `t₀`. -/
noncomputable def LagrangianSystem.chartLagrangian (S : LagrangianSystem I M) (x : M) (t₀ : Time) :
    ℝ × E × E → ℝ :=
  fun p ↦ S (p.1 +ᵥ t₀, tangentMap 𝓘(ℝ, E) I (extChartAt I x).symm
    (⟨p.2.1, p.2.2⟩ : TangentBundle 𝓘(ℝ, E) E))

/-- The chart Lagrangian is smooth over the target of the chart. -/
lemma LagrangianSystem.contDiffAt_chartLagrangian [I.Boundaryless] (S : LagrangianSystem I M)
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
  exact contMDiffAt_prod_self_iff.1 (S.contMDiff.contMDiffAt.comp p hφ)

/-- A chart Lagrangian agrees with a globally smooth one near a compact set of positions. -/
lemma LagrangianSystem.exists_contDiff_chartLagrangian_eq [I.Boundaryless] [FiniteDimensional ℝ E]
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

/-!
## B. Curves read in a chart
-/

/-- The tangent map of a curve read in a chart is the chart Lagrangian's input. -/
private lemma tangentMap_chart_curve [I.Boundaryless] (x : M) {c : Time → E} (t₀ : Time) (s : ℝ)
    (hc : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c (s +ᵥ t₀))
    (hcx : c (s +ᵥ t₀) ∈ (extChartAt I x).target) :
    tangentMap 𝓘(ℝ, ℝ) I ((extChartAt I x).symm ∘ c) ⟨s +ᵥ t₀, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, E) I (extChartAt I x).symm
        (⟨c (s +ᵥ t₀), deriv (fun τ : ℝ ↦ c (τ +ᵥ t₀)) s⟩ : TangentBundle 𝓘(ℝ, E) E) := by
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I x).symm (c (s +ᵥ t₀)) :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt (extChartAt_target_mem_nhds' hcx)
  have h := tangentMap_comp_at (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E)) (I'' := I) (f := c)
    (g := (extChartAt I x).symm) (⟨s +ᵥ t₀, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) Time)
    (hsymm.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))
  rw [h, Time.tangentMap_eq_deriv_vadd]

/-- A chart-read curve is smooth at times at which the curve is in the chart. -/
lemma contDiffAt_chart_curve (x : M) {γ : Time → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (t₀ : Time) {σ : ℝ}
    (hσ : γ (σ +ᵥ t₀) ∈ (extChartAt I x).source) :
    ContDiffAt ℝ ∞ (fun σ' : ℝ ↦ extChartAt I x (γ (σ' +ᵥ t₀))) σ :=
  contMDiffAt_iff_contDiffAt.1 <| ContMDiffAt.comp (g := extChartAt I x)
    (f := fun σ' : ℝ ↦ γ (σ' +ᵥ t₀)) σ
    (contMDiffAt_extChartAt' (by rwa [extChartAt_source] at hσ))
    ((hγ _).comp σ (Time.contMDiff_vadd t₀ ∞).contMDiffAt)

/-!
## C. The action integrand
-/

/-- Near a chart-read curve the action integrand is the chart Lagrangian. -/
lemma LagrangianSystem.integrand_eq_chartLagrangian [I.Boundaryless] (S : LagrangianSystem I M)
    (x : M) (t₀ : Time) {γ' : Time → M} {c : Time → E} {τ : ℝ}
    (hev : γ' =ᶠ[𝓝 (τ +ᵥ t₀)] (extChartAt I x).symm ∘ c)
    (hc : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c (τ +ᵥ t₀))
    (hcx : c (τ +ᵥ t₀) ∈ (extChartAt I x).target) :
    S (τ +ᵥ t₀, tangentMap 𝓘(ℝ, ℝ) I γ' ⟨τ +ᵥ t₀, (1 : ℝ)⟩) =
      S.chartLagrangian x t₀ (τ, c (τ +ᵥ t₀), deriv (fun σ : ℝ ↦ c (σ +ᵥ t₀)) τ) := by
  rw [hev.tangentMap_eq (I := 𝓘(ℝ, ℝ)) (I' := I) (p := ⟨τ +ᵥ t₀, (1 : ℝ)⟩),
    tangentMap_chart_curve x t₀ τ hc hcx]
  rfl

/-- The action integrand along a curve that is a chart-read curve near `τ` is a Lagrangian `L`
agreeing with the chart Lagrangian near `c τ`. -/
lemma LagrangianSystem.integrand_eq_of_germ [I.Boundaryless] (S : LagrangianSystem I M) (x : M)
    (t₀ : Time) {γ' : Time → M} {c : ℝ → E} {τ : ℝ} {L : ℝ × E × E → ℝ} {N : Set E}
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
  have hcx : c ((τ +ᵥ t₀) -ᵥ t₀) ∈ (extChartAt I x).target := by
    rw [vadd_vsub]
    exact hN hcN
  rw [S.integrand_eq_chartLagrangian x t₀ hev hc' hcx, hLN _ hcN]
  simp

/-- The action integrand of a smooth curve is the chart Lagrangian at times in the chart. -/
private lemma LagrangianSystem.integrand_eq_chartLagrangian_of_mem_source [I.Boundaryless]
    (S : LagrangianSystem I M) (x : M) (t₀ : Time) {γ' : Time → M}
    (hγ' : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ') {τ : ℝ} (h : γ' (τ +ᵥ t₀) ∈ (extChartAt I x).source) :
    S (τ +ᵥ t₀, tangentMap 𝓘(ℝ, ℝ) I γ' ⟨τ +ᵥ t₀, (1 : ℝ)⟩) = S.chartLagrangian x t₀
      (τ, extChartAt I x (γ' (τ +ᵥ t₀)),
        deriv (fun σ : ℝ ↦ extChartAt I x (γ' (σ +ᵥ t₀))) τ) :=
  S.integrand_eq_chartLagrangian x t₀ (c := fun t ↦ extChartAt I x (γ' t))
    ((hγ'.continuous.continuousAt.eventually_mem
      ((isOpen_extChartAt_source x).mem_nhds h)).mono
        fun _ ht ↦ ((extChartAt I x).left_inv ht).symm)
    ((contMDiffAt_extChartAt' (by rwa [extChartAt_source] at h)).comp _ (hγ' _))
    ((extChartAt I x).map_source h)

/-- The action integrand of a smooth curve is continuous. -/
lemma LagrangianSystem.continuousAt_integrand [I.Boundaryless]
    (S : LagrangianSystem I M) (t₀ : Time) {γ' : Time → M} (hγ' : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ')
    (τ : ℝ) : ContinuousAt (fun τ : ℝ ↦
      S (τ +ᵥ t₀, tangentMap 𝓘(ℝ, ℝ) I γ' ⟨τ +ᵥ t₀, (1 : ℝ)⟩)) τ := by
  -- read `γ'` in the chart at its value at `τ`, where the integrand is the smooth chart Lagrangian
  set x := γ' (τ +ᵥ t₀)
  have h0 : γ' (τ +ᵥ t₀) ∈ (extChartAt I x).source := mem_extChartAt_source x
  have hg := contDiffAt_chart_curve x hγ' t₀ h0
  exact ((S.contDiffAt_chartLagrangian x t₀
    ((extChartAt I x).map_source h0)).continuousAt.comp_of_eq
    (continuousAt_id.prodMk (hg.continuousAt.prodMk
      (hg.derivWithin (m := 0) (by simp)).continuousAt)) rfl).congr_of_eventuallyEq
    ((hγ'.continuous.comp (Time.contMDiff_vadd t₀ ∞).continuous).continuousAt.eventually_mem
      ((isOpen_extChartAt_source x).mem_nhds h0) |>.mono
        fun _ h ↦ S.integrand_eq_chartLagrangian_of_mem_source x t₀ hγ' h)

end ClassicalMechanics
