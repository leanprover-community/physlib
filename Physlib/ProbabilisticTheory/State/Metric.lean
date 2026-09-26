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

## i. Overview

A state is just a positive linear functional — no continuity is assumed. It turns out to be
automatically bounded: `|ω A| ≤ ‖A‖`. Physically, a state can never predict
an expectation value bigger than what the observable itself can read.

That bound induces a genuine operator-norm distance between states, `dist`, making `𝓢[ℝ, E]` a
`MetricSpace`. That in turn gives a notion of how mixed a state is: `distToPure`, its infimum
distance to the set of pure states.

## ii. Key results

- `UnitalPositiveLinearMap.abs_apply_le_orderUnitNorm` : a state's values are bounded by the
  order-unit norm.
- `UnitalPositiveLinearMap.dist` : the operator-norm distance between states.
- `UnitalPositiveLinearMap.distToPure` : a state's infimum distance to the set of pure states.

## iii. Table of contents

- A. States are bounded by the order-unit norm
- B. The state metric
- C. Distance to pure states

-/

@[expose] public section

open ArchimedeanOrderUnitSpace

variable {E : Type*} [ArchimedeanOrderUnitSpace E]

namespace UnitalPositiveLinearMap

/-!

## A. States are bounded by the order-unit norm

-/

/-- A state never overshoots the order-unit norm. -/
lemma apply_le_orderUnitNorm (ω : 𝓢[ℝ, E]) (A : E) : ω A ≤ orderUnitNorm A := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r, hr, hrε⟩ := exists_orderUnitBound_lt A hε
  have hpos : 0 ≤ ω (r • (1 : E) - A) := map_nonneg ω (sub_nonneg.mpr hr.2.2)
  simp only [map_sub, map_smul, smul_eq_mul, map_one, mul_one] at hpos
  linarith

/-- A state's values are bounded by the order-unit norm in both directions. -/
lemma abs_apply_le_orderUnitNorm (ω : 𝓢[ℝ, E]) (A : E) : |ω A| ≤ orderUnitNorm A := by
  have h1 : ω A ≤ orderUnitNorm A := apply_le_orderUnitNorm ω A
  have h2 : ω (-A) ≤ orderUnitNorm (-A) := apply_le_orderUnitNorm ω (-A)
  rw [_root_.map_neg, orderUnitNorm_neg] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

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

instance : Nonempty {A : E // orderUnitNorm A ≤ 1} := ⟨0, by simp⟩

/-- The operator-norm distance between two states: how far apart their predictions can get on an
observable of order-unit norm at most `1`. -/
noncomputable def dist (ω φ : 𝓢[ℝ, E]) : ℝ :=
  ⨆ A : {A : E // orderUnitNorm A ≤ 1}, |ω A - φ A|

lemma dist_nonneg (ω φ : 𝓢[ℝ, E]) : 0 ≤ dist ω φ :=
  le_trans (abs_nonneg _) (le_ciSup (dist_bddAbove ω φ) ⟨0, by simp⟩)

/-- The whole state space has diameter at most `2`: it's a bounded metric space. -/
lemma dist_le_two (ω φ : 𝓢[ℝ, E]) : dist ω φ ≤ 2 :=
  ciSup_le fun A => abs_apply_sub_apply_le_two ω φ A.2

@[simp]
lemma dist_self (ω : 𝓢[ℝ, E]) : dist ω ω = 0 := by
  simp [dist]

lemma dist_comm (ω φ : 𝓢[ℝ, E]) : dist ω φ = dist φ ω := by
  unfold dist
  simp_rw [abs_sub_comm]

lemma dist_triangle (ω φ ψ : 𝓢[ℝ, E]) : dist ω ψ ≤ dist ω φ + dist φ ψ := by
  apply ciSup_le
  intro A
  calc |ω A - ψ A| ≤ |ω A - φ A| + |φ A - ψ A| := abs_sub_le _ _ _
    _ ≤ dist ω φ + dist φ ψ :=
      add_le_add (le_ciSup (dist_bddAbove ω φ) A) (le_ciSup (dist_bddAbove φ ψ) A)

/-- `dist` separates states: two states at distance `0` are equal. -/
lemma eq_of_dist_eq_zero {ω φ : 𝓢[ℝ, E]} (h : dist ω φ = 0) : ω = φ := by
  apply ext
  intro A
  rcases eq_or_ne (orderUnitNorm A) 0 with hr | hr
  · simp [orderUnitNorm_eq_zero_iff.mp hr]
  · obtain ⟨B, hB1, hAB⟩ := exists_orderUnitNorm_le_one_smul_eq hr
    have hB : |ω B - φ B| ≤ 0 := (le_ciSup (dist_bddAbove ω φ) ⟨B, hB1⟩).trans h.le
    rw [← hAB, map_smul, map_smul, sub_eq_zero.mp (abs_nonpos_iff.mp hB)]

/-- A state's value at a doubled, re-centered effect (`Effect.equivBall`) is twice its value at
the effect, minus one. -/
lemma apply_equivBall (ψ : 𝓢[ℝ, E]) (e : Effect E) :
    ψ ((Effect.equivBall e : E)) = 2 * ψ (e : E) - 1 := by
  show ψ ((2 : ℝ) • (e : E) - 1) = _
  rw [map_sub, map_smul, map_one, smul_eq_mul]

/-- States, metrized by the operator norm induced by the order-unit norm on `E`. -/
noncomputable instance : MetricSpace (𝓢[ℝ, E]) where
  dist := dist
  dist_self := dist_self
  dist_comm := dist_comm
  dist_triangle := dist_triangle
  eq_of_dist_eq_zero := eq_of_dist_eq_zero

/-!

## C. Distance to pure states

-/

/-- How mixed a state is: its infimum distance to the set of pure states. -/
noncomputable def distToPure (ω : 𝓢[ℝ, E]) : ℝ :=
  Metric.infDist ω {φ : 𝓢[ℝ, E] | IsPure φ}

lemma distToPure_nonneg (ω : 𝓢[ℝ, E]) : 0 ≤ distToPure ω :=
  Metric.infDist_nonneg

/-- A pure state is at distance `0` from the set of pure states. -/
lemma distToPure_eq_zero_of_isPure {ω : 𝓢[ℝ, E]} (h : IsPure ω) : distToPure ω = 0 :=
  Metric.infDist_zero_of_mem h

/-- `distToPure` is `1`-Lipschitz: states close in `dist` are similarly mixed. -/
lemma lipschitzWith_distToPure : LipschitzWith 1 (distToPure (E := E)) :=
  Metric.lipschitz_infDist_pt {φ : 𝓢[ℝ, E] | IsPure φ}

end UnitalPositiveLinearMap
