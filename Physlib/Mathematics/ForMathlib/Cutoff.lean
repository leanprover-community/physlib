/-
Copyright (c) 2026 Michal Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Mogielnicki
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Cutoff functions

Smooth cutoffs around a compact set.

## i. Overview

A compact subset of an open set in a finite-dimensional space has a smooth cutoff, `1` near the
subset and `0` near every point outside the open set.

## ii. Key results

- `exists_cutoff`
- `contDiff_smul_of_cutoff`
- `exists_contDiff_eq_nhds`

## iii. Table of contents

- A. Cutoff functions
- B. Small perturbations

## iv. References

* None.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-!
## A. Cutoff functions
-/

/-- A smooth cutoff which is `1` on a neighbourhood `N` of a compact set `K` inside an open set `U`
and vanishes near every point outside `U`. -/
lemma exists_cutoff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (χ : X → ℝ) (N : Set X), ContDiff ℝ ∞ χ ∧ IsOpen N ∧ K ⊆ N ∧ N ⊆ U ∧
      (∀ y ∈ N, χ y = 1) ∧ ∀ y ∉ U, ∀ᶠ z in 𝓝 y, χ z = 0 := by
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
    fun y hy ↦ ?_⟩
  filter_upwards [isClosed_cthickening.isOpen_compl.mem_nhds fun h ↦ hy (hδU h)] with z hz
  exact (hχ0 _).1 fun h' ↦ hz (thickening_subset_cthickening _ _ h')

/-- A smooth cutoff times a function smooth on the set where the cutoff is not locally zero is
smooth. -/
lemma contDiff_smul_of_cutoff {Y F : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ρ : Y → ℝ} (hρ : ContDiff ℝ ∞ ρ) {W : Set Y}
    (hρ0 : ∀ y ∉ W, ∀ᶠ z in 𝓝 y, ρ z = 0) {f : Y → F} (hf : ∀ y ∈ W, ContDiffAt ℝ ∞ f y) :
    ContDiff ℝ ∞ fun y ↦ ρ y • f y := by
  refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
  by_cases hy : y ∈ W
  · exact hρ.contDiffAt.smul (hf y hy)
  · refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [hρ0 y hy] with z hz
    simp [hz]

/-- A function smooth on an open set agrees near a compact subset with a globally smooth one. -/
lemma exists_contDiff_eq_nhds {f : ℝ → E} {O : Set ℝ} (hO : IsOpen O)
    (hf : ∀ τ ∈ O, ContDiffAt ℝ ∞ f τ) {C : Set ℝ} (hC : IsCompact C) (hCO : C ⊆ O) :
    ∃ g : ℝ → E, ContDiff ℝ ∞ g ∧ ∀ τ ∈ C, g =ᶠ[𝓝 τ] f := by
  obtain ⟨ρ, N, hρ, hNo, hCN, -, hρ1, hρ0⟩ := exists_cutoff hC hO hCO
  exact ⟨fun τ ↦ ρ τ • f τ, contDiff_smul_of_cutoff hρ hρ0 hf, fun τ hτ ↦ by
    filter_upwards [hNo.mem_nhds (hCN hτ)] with q hq
    simp [hρ1 _ hq]⟩

/-!
## B. Small perturbations
-/

/-- Small multiples of bounded vectors keep a compact subset of an open set inside it. -/
lemma exists_eps_add_smul_mem {K N : Set E} (hK : IsCompact K) (hN : IsOpen N) (hKN : K ⊆ N)
    (B : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ K, ∀ v : E, ‖v‖ ≤ B → ∀ r : ℝ, r ∈ Icc (-ε) ε → y + r • v ∈ N := by
  obtain ⟨δ, hδ, hδN⟩ := hK.exists_thickening_subset_open hN hKN
  refine ⟨δ / (|B| + 1), by positivity, fun y hy v hv r hr ↦ hδN ?_⟩
  rw [mem_thickening_iff]
  refine ⟨y, hy, ?_⟩
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  have hr' : |r| ≤ δ / (|B| + 1) := abs_le.2 ⟨by linarith [hr.1], hr.2⟩
  have hB : ‖v‖ ≤ |B| := hv.trans (le_abs_self B)
  calc |r| * ‖v‖ ≤ δ / (|B| + 1) * |B| := by gcongr
    _ < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg B]
