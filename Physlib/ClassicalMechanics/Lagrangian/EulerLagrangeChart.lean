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

open Set
open scoped ContDiff
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
  -- `O`: open set of times in `(0, T)` where `γ` stays in the chart domain
  set O : Set ℝ := Ioo 0 (t₁ -ᵥ t₀) ∩ (fun σ : ℝ ↦ γ (σ +ᵥ t₀)) ⁻¹' (extChartAt I x).source
  have hOo : IsOpen O := isOpen_Ioo.inter ((isOpen_extChartAt_source x).preimage
    (hc.1.continuous.comp (Time.contMDiff_vadd t₀ ∞).continuous))
  have hqO := fun σ (hσ : σ ∈ O) ↦ contDiffAt_chart_curve x hc.1 t₀ hσ.2
  obtain ⟨δ, hδ, hCO⟩ := exists_Icc_subset hOo ⟨hτ, hx⟩
  -- smooth `q'` agreeing with `q` near the compact `Icc (τ₀ - δ) (τ₀ + δ)`
  obtain ⟨q', hq', hq'q⟩ := exists_contDiff_eq_nhds hOo hqO isCompact_Icc hCO
  have hKt : q' '' Icc (τ₀ - δ) (τ₀ + δ) ⊆ (extChartAt I x).target := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact (hq'q σ hσ).eq_of_nhds ▸ (extChartAt I x).map_source (hCO hσ).2
  -- smooth global Lagrangian `L` agreeing with the chart one near the image of `q'`
  obtain ⟨L, N, hNo, hKN, hNt, hL, hLN⟩ :=
    S.exists_contDiff_coord_eq x t₀ (isCompact_Icc.image hq'.continuous) hKt
  have hτ₀U : τ₀ ∈ Ioo (τ₀ - δ) (τ₀ + δ) := ⟨by linarith, by linarith⟩
  -- criticality kills the weak form of the equation, so the continuous integrand vanishes
  have hzero := eq_zero_of_integral_smul_eq_zero_of_isOpen
    (contDiff_eulerLagrange hL hq').continuous isOpen_Ioo
    (fun σ hσ ↦ (hCO (Ioo_subset_Icc_self hσ)).1) fun ψ hψ hψc hψs w ↦
    S.integral_eulerLagrange_eq_zero x hc (hτ.1.trans hτ.2) hL hNo hNt hLN hq' isCompact_Icc
      (fun τ hτ ↦ (hCO hτ).2) hq'q (fun τ hτ ↦ hKN ⟨τ, hτ, rfl⟩) hψ hψc
      (hψs.trans fun σ hσ ↦ (hCO (Ioo_subset_Icc_self hσ)).1) (hψs.trans Ioo_subset_Icc_self) w
  rw [← eulerLagrange_congr (hq'q τ₀ (Ioo_subset_Icc_self hτ₀U)),
    eulerLagrange_congr_lagrangian hNo
      (hq'.continuous.continuousAt.eventually_mem
        (hNo.mem_nhds (hKN ⟨τ₀, Ioo_subset_Icc_self hτ₀U, rfl⟩)))
      fun p hp ↦ (hLN p hp).symm]
  exact hzero τ₀ hτ₀U

end ClassicalMechanics
