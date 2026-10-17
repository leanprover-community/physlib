/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.State.Convex
public import Physlib.ProbabilisticTheory.Effect.Metric
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# The metric space of states

The operator-norm distance between states and their distance to the set of pure states.

## i. Overview

A state is just a positive linear functional — no continuity is assumed. It turns out to be
automatically bounded: `|ω A| ≤ ‖A‖`. Physically, a state can never predict
an expectation value bigger than what the observable itself can read.

That bound induces a genuine operator-norm distance between states, `dist`, making `𝓢[ℝ, E]` a
`MetricSpace`. It also defines `distToPure`, the infimum distance to the set of pure states.

## ii. Key results

- `UnitalPositiveLinearMap.abs_apply_le_orderUnitNorm` : a state's values are bounded by the
  order-unit norm.
- `UnitalPositiveLinearMap.dist` : the operator-norm distance between states.
- `UnitalPositiveLinearMap.distToPure` : a state's infimum distance to the set of pure states.

## iii. Table of contents

- A. States are bounded by the order-unit norm
- B. The state metric
- C. Distance to pure states

## iv. References

-/

@[expose] public section

open ProbabilisticTheory

open ArchimedeanOrderUnitSpace Effect

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

namespace UnitalPositiveLinearMap

/-!

## A. States are bounded by the order-unit norm

-/

/-- A state takes values at most `1` on observables bounded by the unit. -/
lemma apply_le_one {F : Type*} [OrderUnitSpace F] (ω : 𝓢[ℝ, F]) {A : F} (hA : A ≤ 1) :
    ω A ≤ 1 :=
  (ω.monotone' hA).trans_eq (map_one ω)

/-- A state never overshoots the order-unit norm. -/
lemma apply_le_orderUnitNorm (ω : 𝓢[ℝ, E]) (A : E) : ω A ≤ orderUnitNorm A := by
  simpa using ω.monotone' (le_orderUnitNorm_smul_one A)

/-- A state's values are bounded by the order-unit norm in both directions. -/
lemma abs_apply_le_orderUnitNorm (ω : 𝓢[ℝ, E]) (A : E) : |ω A| ≤ orderUnitNorm A := by
  exact abs_le.mpr ⟨neg_le.mp (by simpa using apply_le_orderUnitNorm ω (-A)),
    apply_le_orderUnitNorm ω A⟩

/-- Two states' predictions on any observable of order-unit norm at most `1` never differ by more
than `2`. -/
lemma abs_apply_sub_apply_le_two (ω φ : 𝓢[ℝ, E]) {A : E} (hA : orderUnitNorm A ≤ 1) :
    |ω A - φ A| ≤ 2 := by
  linarith [abs_sub (ω A) (φ A), abs_apply_le_orderUnitNorm ω A, abs_apply_le_orderUnitNorm φ A]

/-!

## B. The state metric

-/

/-- The values `|ω A - φ A|` of two states, restricted to the order-unit-norm unit ball, are
bounded by `2`. -/
lemma dist_bddAbove (ω φ : 𝓢[ℝ, E]) :
    BddAbove (Set.range fun A : {A : E // orderUnitNorm A ≤ 1} => |ω A - φ A|) :=
  ⟨2, by rintro _ ⟨A, rfl⟩; exact abs_apply_sub_apply_le_two ω φ A.2⟩

instance instNonemptyOrderUnitBall : Nonempty {A : E // orderUnitNorm A ≤ 1} := ⟨0, by simp⟩

/-- The operator-norm distance between two states: how far apart their predictions can get on an
observable of order-unit norm at most `1`. -/
noncomputable def dist (ω φ : 𝓢[ℝ, E]) : ℝ :=
  ⨆ A : {A : E // orderUnitNorm A ≤ 1}, |ω A - φ A|

/-- Distances between states are nonnegative. -/
lemma dist_nonneg (ω φ : 𝓢[ℝ, E]) : 0 ≤ dist ω φ :=
  le_trans (abs_nonneg _) (le_ciSup (dist_bddAbove ω φ) ⟨0, by simp⟩)

/-- The whole state space has diameter at most `2`: it's a bounded metric space. -/
lemma dist_le_two (ω φ : 𝓢[ℝ, E]) : dist ω φ ≤ 2 :=
  ciSup_le fun A => abs_apply_sub_apply_le_two ω φ A.2

@[simp]
lemma dist_self (ω : 𝓢[ℝ, E]) : dist ω ω = 0 := by
  simp [dist]

/-- The state distance is symmetric. -/
lemma dist_comm (ω φ : 𝓢[ℝ, E]) : dist ω φ = dist φ ω := by
  simp only [dist, abs_sub_comm]

/-- The state distance satisfies the triangle inequality. -/
lemma dist_triangle (ω φ ψ : 𝓢[ℝ, E]) : dist ω ψ ≤ dist ω φ + dist φ ψ :=
  ciSup_le fun A => (abs_sub_le _ _ _).trans
    (add_le_add (le_ciSup (dist_bddAbove ω φ) A) (le_ciSup (dist_bddAbove φ ψ) A))

/-- `dist` separates states: two states at distance `0` are equal. -/
lemma eq_of_dist_eq_zero {ω φ : 𝓢[ℝ, E]} (h : dist ω φ = 0) : ω = φ := by
  refine DFunLike.ext _ _ fun A => ?_
  rcases eq_or_ne (orderUnitNorm A) 0 with hr | hr
  · simp [orderUnitNorm_eq_zero_iff.mp hr]
  · obtain ⟨B, hB1, hAB⟩ := exists_orderUnitNorm_le_one_smul_eq hr
    have hB : |ω B - φ B| ≤ 0 := (le_ciSup (dist_bddAbove ω φ) ⟨B, hB1⟩).trans h.le
    rw [← hAB, map_smul, map_smul, sub_eq_zero.mp (abs_nonpos_iff.mp hB)]

/-- A state's value at a doubled, re-centered effect (`effectEquiv`) is twice its value at
the effect, minus one. -/
lemma apply_effectEquiv (ψ : 𝓢[ℝ, E]) (e : Effect E) :
    ψ (effectEquiv e) = 2 * ψ e - 1 := by
  simp [effectEquiv]

/-- States, metrized by the operator norm induced by the order-unit norm on `E`. -/
noncomputable instance instMetricSpace : MetricSpace (𝓢[ℝ, E]) where
  dist := dist
  dist_self := dist_self
  dist_comm := dist_comm
  dist_triangle := dist_triangle
  eq_of_dist_eq_zero := eq_of_dist_eq_zero

/-!

## C. Distance to pure states

-/

/-- The infimum distance to the set of pure states, using `Metric.infDist`. -/
noncomputable def distToPure (ω : 𝓢[ℝ, E]) : ℝ :=
  Metric.infDist ω {φ : 𝓢[ℝ, E] | IsPure φ}

/-- The distance to the set of pure states is nonnegative. -/
lemma distToPure_nonneg (ω : 𝓢[ℝ, E]) : 0 ≤ distToPure ω :=
  Metric.infDist_nonneg

/-- A pure state is at distance `0` from the set of pure states. -/
lemma distToPure_eq_zero_of_isPure {ω : 𝓢[ℝ, E]} (h : IsPure ω) : distToPure ω = 0 :=
  Metric.infDist_zero_of_mem h

end UnitalPositiveLinearMap
