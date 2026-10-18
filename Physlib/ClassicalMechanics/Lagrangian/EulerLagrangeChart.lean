/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Physlib.ClassicalMechanics.Lagrangian.ChartVariation

/-!
# Euler-Lagrange equations in charts

Critical points of the action satisfy the Euler-Lagrange equations in every chart.

## i. Overview

The converse is not yet formalised.

## ii. Key results

- `LagrangianSystem.eulerLagrange_coord_of_isCriticalPoint`

## iii. Table of contents

- A. Critical points

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
## A. Critical points
-/

/-- A critical point satisfies the Euler-Lagrange equations in every chart containing it. -/
lemma LagrangianSystem.eulerLagrange_coord_of_isCriticalPoint [I.Boundaryless]
    [FiniteDimensional ℝ E] (S : LagrangianSystem I M) {γ : Time → M} {t₀ t₁ : Time}
    (hc : S.IsCriticalPoint γ t₀ t₁) (x : M) {τ₀ : ℝ} (hτ : τ₀ ∈ Ioo 0 (t₁ -ᵥ t₀))
    (hx : γ (τ₀ +ᵥ t₀) ∈ (extChartAt I x).source) :
    eulerLagrange (S.coord x t₀) (fun σ : ℝ ↦ extChartAt I x (γ (σ +ᵥ t₀))) τ₀ = 0 := by
  have hγ := hc.1
  set T := t₁ -ᵥ t₀
  have hT : 0 < T := hτ.1.trans hτ.2
  set q : ℝ → E := fun σ ↦ extChartAt I x (γ (σ +ᵥ t₀))
  set O : Set ℝ := Ioo 0 T ∩ (fun σ : ℝ ↦ γ (σ +ᵥ t₀)) ⁻¹' (extChartAt I x).source
  have hOo : IsOpen O := isOpen_Ioo.inter ((isOpen_extChartAt_source x).preimage
    (hγ.continuous.comp (Time.contMDiff_vadd t₀ ∞).continuous))
  have hqO : ∀ σ ∈ O, ContDiffAt ℝ ∞ q σ := fun σ hσ ↦ contDiffAt_chart_curve x hγ t₀ hσ.2
  have hτ₀O : τ₀ ∈ O := ⟨hτ, hx⟩
  obtain ⟨δ, hδ, hCO⟩ := exists_Icc_subset hOo hτ₀O
  set C : Set ℝ := Icc (τ₀ - δ) (τ₀ + δ)
  have hCc : IsCompact C := isCompact_Icc
  set U : Set ℝ := Ioo (τ₀ - δ) (τ₀ + δ)
  have hUC : U ⊆ C := Ioo_subset_Icc_self
  have hUT : U ⊆ Ioo 0 T := fun σ hσ ↦ (hCO (hUC hσ)).1
  have hKc : IsCompact (q '' C) :=
    hCc.image_of_continuousOn fun σ hσ ↦ (hqO σ (hCO hσ)).continuousAt.continuousWithinAt
  have hKt : q '' C ⊆ (extChartAt I x).target := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact (extChartAt I x).map_source (hCO hσ).2
  obtain ⟨L, N, hNo, hKN, hNt, hL, hLN⟩ := S.exists_contDiff_coord_eq x t₀ hKc hKt
  obtain ⟨q', hq', hq'q⟩ := exists_contDiff_eq_nhds hOo hqO hCc hCO
  have hf : Continuous (eulerLagrange L q') := (contDiff_eulerLagrange hL hq').continuous
  have hτ₀U : τ₀ ∈ U := ⟨by linarith, by linarith⟩
  have hzero : ∀ τ ∈ U, eulerLagrange L q' τ = 0 := by
    refine eq_zero_of_integral_smul_eq_zero_of_isOpen hf isOpen_Ioo hUT ?_
    intro ψ hψ hψc hψs w
    obtain ⟨B, hB⟩ := hψc.exists_bound_of_continuous hψ.continuous
    obtain ⟨ε, hε, hεN⟩ := exists_eps_add_smul_mem hKc hNo hKN (B * ‖w‖)
    obtain ⟨h, hh⟩ := S.exists_hasDerivAt_action_chart x hγ hT hL hNt hLN hq'
      (fun τ hτ ↦ (hCO hτ).2) hq'q hψ (hψs.trans hUT) (hψs.trans hUC) w hε
      (fun τ hτC r hr' ↦ by
        rw [(hq'q τ hτC).eq_of_nhds]
        exact hεN _ ⟨τ, hτC, rfl⟩ _ (by
          calc ‖ψ τ • w‖ = ‖ψ τ‖ * ‖w‖ := norm_smul _ _
            _ ≤ B * ‖w‖ := by gcongr; exact hB τ) r hr')
    exact hh.unique (hc.2 h)
  have hqN : ∀ᶠ σ in 𝓝 τ₀, q σ ∈ N :=
    (hqO τ₀ hτ₀O).continuousAt.eventually_mem
      (hNo.mem_nhds (hKN ⟨τ₀, hUC hτ₀U, rfl⟩))
  rw [eulerLagrange_congr_lagrangian hNo hqN (fun p hp ↦ (hLN p hp).symm),
    eulerLagrange_congr (hq'q τ₀ (hUC hτ₀U)).symm]
  exact hzero τ₀ hτ₀U

end ClassicalMechanics
