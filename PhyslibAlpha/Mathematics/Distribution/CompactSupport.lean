/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Distribution.Support
public import PhyslibAlpha.Mathematics.Distribution.TestFunction

/-!

# Compactly supported distributions and cutoffs

## i. Overview

A compactly supported distribution is unchanged by a cutoff that equals one near its support.

## ii. Key results

- `compactDistributions` : Compactly supported native distributions, defined by annihilation outside
  a compact bound.
- `compactDistributionBound` : A chosen compact support bound for a native compact distributional
  source.
- `multiplyDistribution` : Smooth multiplication of a distribution is the transpose of native test
  multiplication.
- `compactCutoffRadius` : A positive radius containing a compact set in its open ball.
- `compactCutoffBump` : The canonical support-bound cutoff is a smooth compact bump.
- `compactCutoff` : A native compact test cutoff equal to one in a neighborhood of the compact set.

## iii. Table of contents

- A. Compact distributional sources
- B. Localization of native distributions

## iv. References

None.

## A. Compact distributional sources

- `compactDistributions` : Compactly supported native distributions, defined by annihilation outside
  a compact bound.
- `compactDistributionBound` : A chosen compact support bound for a native compact distributional
  source.

Lemmas: `compactDistributionBound_vanishes`.

## B. Localization of native distributions

- `multiplyDistribution` : Smooth multiplication of a distribution is the transpose of native test
  multiplication.
- `compactCutoffRadius` : A positive radius containing a compact set in its open ball.
- `compactCutoffBump` : The canonical support-bound cutoff is a smooth compact bump.
- `compactCutoff` : A native compact test cutoff equal to one in a neighborhood of the compact set.

Lemmas: `multiplyDistribution_apply`, `multiplyDistribution_eq_self`, `compactCutoff_one_near`.

-/

@[expose] public section

noncomputable section

open scoped ContDiff
open TestFunction Topology TopologicalSpace

namespace Distribution

section
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace
    ℝ V]

/-- Compactly supported native distributions, defined by annihilation outside a compact bound. -/
def compactDistributions (E V : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] :
    Submodule ℝ (Distribution (⊤ : Opens E) V ⊤) where
  carrier := {T | ∃ K : Set E, IsCompact K ∧ Distribution.IsVanishingOn T Kᶜ}
  zero_mem' := ⟨∅, isCompact_empty, fun _ _ => rfl⟩
  add_mem' := by
    rintro T S ⟨K, hK, hT⟩ ⟨L, hL, hS⟩
    refine ⟨K ∪ L, hK.union hL, ?_⟩
    intro φ hφ
    change T φ + S φ = 0
    rw [hT φ (hφ.trans (Set.compl_subset_compl.mpr Set.subset_union_left)),
      hS φ (hφ.trans (Set.compl_subset_compl.mpr Set.subset_union_right)), add_zero]
  smul_mem' := by
    rintro a T ⟨K, hK, hT⟩
    refine ⟨K, hK, ?_⟩
    intro φ hφ
    change a • T φ = 0
    rw [hT φ hφ, smul_zero]

/-- A chosen compact support bound for a native compact distributional source. -/
def compactDistributionBound (T : compactDistributions E V) : Compacts E :=
  ⟨Classical.choose T.property, (Classical.choose_spec T.property).1⟩

/-- The chosen compact bound has the source's native test annihilation property. -/
lemma compactDistributionBound_vanishes (T : compactDistributions E V) :
    Distribution.IsVanishingOn T.val (compactDistributionBound T : Set E)ᶜ :=
  (Classical.choose_spec T.property).2

/-- Smooth multiplication of a distribution is the transpose of native test multiplication. -/
def multiplyDistribution (w : E → ℝ) (hw : ContDiff ℝ ∞ w) :
    Distribution (⊤ : Opens E) V ⊤ →L[ℝ] Distribution (⊤ : Opens E) V ⊤ :=
  (smoothWeightTest w hw).precompCompactConvergenceCLM V

/-- Multiplication of native distributions is defined by moving the weight onto the test. -/
lemma multiplyDistribution_apply (w : E → ℝ) (hw : ContDiff ℝ ∞ w)
    (T : Distribution (⊤ : Opens E) V ⊤) (φ : _root_.TestFunction (⊤ : Opens E) ℝ ⊤) :
    multiplyDistribution w hw T φ = T (smoothWeightTest w hw φ) := rfl

/-- A weight equal to one near a compact support bound leaves the source unchanged. -/
lemma multiplyDistribution_eq_self (w : E → ℝ) (hw : ContDiff ℝ ∞ w)
    (T : Distribution (⊤ : Opens E) V ⊤) (K : Set E)
    (hT : Distribution.IsVanishingOn T Kᶜ)
    (hnear : ∀ p ∈ K, w =ᶠ[𝓝 p] (1 : E → ℝ)) : multiplyDistribution w hw T = T := by
  ext φ
  let ψ := smoothWeightTest w hw φ - φ
  have hs : tsupport (ψ : E → ℝ) ⊆ Kᶜ := by
    intro p hp hpK
    have hn : p ∉ tsupport (ψ : E → ℝ) := by
      apply notMem_tsupport_iff_eventuallyEq.mpr
      filter_upwards [hnear p hpK] with q hq
      change w q • φ q - φ q = 0
      rw [hq]
      simp
    exact hn hp
  have hz := hT ψ hs
  have hsub := map_sub T (smoothWeightTest w hw φ) φ
  change T (smoothWeightTest w hw φ) = T φ
  exact sub_eq_zero.mp (hsub.symm.trans hz)

/-- A positive radius containing a compact set in its open ball. -/
def compactCutoffRadius (K : Compacts E) : ℝ :=
  Classical.choose K.isCompact.isBounded.exists_pos_norm_lt

/-- The canonical support-bound cutoff is a smooth compact bump. -/
def compactCutoffBump (K : Compacts E) : ContDiffBump (0 : E) where
  rIn := compactCutoffRadius K
  rOut := compactCutoffRadius K + 1
  rIn_pos := (Classical.choose_spec K.isCompact.isBounded.exists_pos_norm_lt).1
  rIn_lt_rOut := lt_add_one _

/-- A native compact test cutoff equal to one in a neighborhood of the compact set. -/
def compactCutoff [FiniteDimensional ℝ E] (K : Compacts E) :
    _root_.TestFunction (⊤ : Opens E) ℝ ⊤ :=
  ⟨compactCutoffBump K, (compactCutoffBump K).contDiff,
    (compactCutoffBump K).hasCompactSupport, Set.subset_univ _⟩

/-- The support-bound cutoff equals one as a germ at every point in its compact bound. -/
lemma compactCutoff_one_near [FiniteDimensional ℝ E] (K : Compacts E) {p : E} (hp : p ∈ K) :
    (compactCutoff K : E → ℝ) =ᶠ[𝓝 p] (1 : E → ℝ) := by
  apply (compactCutoffBump K).eventuallyEq_one_of_mem_ball
  rw [Metric.mem_ball, dist_zero_right]
  exact (Classical.choose_spec K.isCompact.isBounded.exists_pos_norm_lt).2 p hp
end

end Distribution
