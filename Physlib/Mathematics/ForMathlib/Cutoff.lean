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

## iii. Table of contents

- A. Cutoff functions

## iv. References

* None.
-/

@[expose] public section

open Set Topology Metric
open scoped ContDiff

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
