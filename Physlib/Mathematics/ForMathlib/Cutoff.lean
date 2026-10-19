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

- `IsCompact.exists_cutoff`
- `contDiff_smul_of_cutoff`
- `exists_contDiff_eq_nhds`
- `IsCompact.exists_eps_add_smul_mem`

## iii. Table of contents

- A. Cutoff functions
- B. Small perturbations

## iv. References

* None.
-/

@[expose] public section

open Set Topology Metric
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-!
## A. Cutoff functions
-/

/-- A smooth cutoff which is `1` on a neighbourhood `N` of a compact set `K` inside an open set `U`
and has topological support inside `U`. -/
lemma IsCompact.exists_cutoff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
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
lemma contDiff_smul_of_cutoff {Y F : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ρ : Y → ℝ} (hρ : ContDiff ℝ ∞ ρ) {W : Set Y}
    (hρ0 : tsupport ρ ⊆ W) {f : Y → F} (hf : ∀ y ∈ W, ContDiffAt ℝ ∞ f y) :
    ContDiff ℝ ∞ fun y ↦ ρ y • f y := by
  refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
  by_cases hy : y ∈ tsupport ρ
  · exact hρ.contDiffAt.smul (hf y (hρ0 hy))
  · refine (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hy] with z hz
    simp [hz]

/-- A function smooth on an open set agrees near a compact subset with a globally smooth one. -/
lemma exists_contDiff_eq_nhds {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {f : X → E} {O : Set X} (hO : IsOpen O)
    (hf : ∀ x ∈ O, ContDiffAt ℝ ∞ f x) {C : Set X} (hC : IsCompact C) (hCO : C ⊆ O) :
    ∃ g : X → E, ContDiff ℝ ∞ g ∧ ∀ x ∈ C, g =ᶠ[𝓝 x] f := by
  obtain ⟨ρ, N, hρ, hNo, hCN, -, hρ1, hρ0⟩ := hC.exists_cutoff hO hCO
  exact ⟨fun x ↦ ρ x • f x, contDiff_smul_of_cutoff hρ hρ0 hf, fun x hx ↦ by
    filter_upwards [hNo.mem_nhds (hCN hx)] with q hq
    simp [hρ1 _ hq]⟩

/-!
## B. Small perturbations
-/

/-- Small multiples of bounded vectors keep a compact subset of an open set inside it. -/
lemma IsCompact.exists_eps_add_smul_mem {K N : Set E} (hK : IsCompact K) (hN : IsOpen N)
    (hKN : K ⊆ N) (B : ℝ) :
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
