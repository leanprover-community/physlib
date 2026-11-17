/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Dimensionless Hohmann parameters

The reciprocal radius ratio determines the normalized Hohmann cost.

## i. Overview

Use the inner radius and its circular speed as units. The Hohmann invariant pair lies at the
intersection of two inequalities for the squared radial speeds.

## ii. Key results

- `Shape.corner_feasible` gives the main result of this module.

## iii. Table of contents

- A. Normalized invariants and feasibility

## iv. References

- [ref: hohmann_prussing_1992]. Prussing studies the two-impulse global comparison.
-/

@[expose] public noncomputable section

namespace ClassicalMechanics.HohmannOptimality

/-!
## A. Normalized invariants and feasibility
-/

/-- Reciprocal radius ratio. Length unit is r₁; speed unit is √(μ/r₁). -/
structure Shape where
  /-- The inner circular radius divided by the outer circular radius. -/
  alpha : ℝ
  /-- The radius ratio is positive. -/
  alpha_pos : 0 < alpha
  /-- The radius ratio is less than one. -/
  alpha_lt_one : alpha < 1

namespace Shape

/-- The outer circular speed in units of the inner circular speed. -/
def circularOuter (s : Shape) : ℝ := Real.sqrt s.alpha
/-- The signed angular momentum of the normalized Hohmann coast. -/
def hH (s : Shape) : ℝ := Real.sqrt (2 / (1 + s.alpha))
/-- Twice the normalized specific energy of the Hohmann coast. -/
def energyH (s : Shape) : ℝ := s.hH ^ 2 - 2
/-- The conserved energy variable is twice specific energy in speed units. -/
def burnH₁ (s : Shape) : ℝ := s.hH - 1
/-- The normalized magnitude of the Hohmann arrival impulse. -/
def burnH₂ (s : Shape) : ℝ := s.circularOuter - s.alpha * s.hH
/-- The sum of the two normalized Hohmann impulse magnitudes. -/
def costH (s : Shape) : ℝ := s.burnH₁ + s.burnH₂

lemma sum_pos (s : Shape) : 0 < 1 + s.alpha := by linarith [s.alpha_pos]
lemma c_pos (s : Shape) : 0 < s.circularOuter := Real.sqrt_pos.2 s.alpha_pos
lemma c_sq (s : Shape) : s.circularOuter ^ 2 = s.alpha :=
  Real.sq_sqrt (le_of_lt s.alpha_pos)
lemma c_lt_one (s : Shape) : s.circularOuter < 1 := by
  nlinarith [s.c_sq, s.alpha_lt_one, s.c_pos]
lemma h_pos (s : Shape) : 0 < s.hH :=
  Real.sqrt_pos.2 (div_pos (by norm_num) s.sum_pos)
lemma h_sq (s : Shape) : s.hH ^ 2 = 2 / (1 + s.alpha) :=
  Real.sq_sqrt (le_of_lt (div_pos (by norm_num) s.sum_pos))
lemma h_sq_mul (s : Shape) : s.hH ^ 2 * (1 + s.alpha) = 2 := by
  rw [s.h_sq]
  field_simp [ne_of_gt s.sum_pos]
lemma one_lt_h_sq (s : Shape) : 1 < s.hH ^ 2 := by
  rw [s.h_sq]
  apply (lt_div_iff₀ s.sum_pos).2
  linarith [s.alpha_lt_one]
lemma one_lt_h (s : Shape) : 1 < s.hH := by
  nlinarith [s.one_lt_h_sq, s.h_pos]
lemma alpha_h_sq_lt_one (s : Shape) : s.alpha * s.hH ^ 2 < 1 := by
  nlinarith [s.h_sq_mul, s.one_lt_h_sq]
lemma alpha_h_lt_c (s : Shape) : s.alpha * s.hH < s.circularOuter := by
  have hmul := mul_lt_mul_of_pos_left s.alpha_h_sq_lt_one s.alpha_pos
  have hp : 0 < s.alpha * s.hH := mul_pos s.alpha_pos s.h_pos
  nlinarith [s.c_sq, s.c_pos]
lemma alpha_c_lt_one (s : Shape) : s.alpha * s.circularOuter < 1 := by
  have h := mul_lt_mul_of_pos_right s.alpha_lt_one s.c_pos
  nlinarith [s.c_lt_one]
lemma alpha_sq_h_lt_one (s : Shape) : s.alpha ^ 2 * s.hH < 1 := by
  have h := mul_lt_mul_of_pos_left s.alpha_h_lt_c s.alpha_pos
  nlinarith [s.alpha_c_lt_one]
lemma alpha_c_lt_h (s : Shape) : s.alpha * s.circularOuter < s.hH :=
  lt_trans s.alpha_c_lt_one s.one_lt_h
lemma corner_inner (s : Shape) : s.energyH + 2 = s.hH ^ 2 := by
  unfold energyH
  ring
lemma corner_outer (s : Shape) : s.energyH + 2 * s.alpha = s.alpha ^ 2 * s.hH ^ 2 := by
  have h := congrArg (fun z : ℝ => (s.alpha - 1) * z) s.h_sq_mul
  unfold energyH
  nlinarith
lemma corner_relation (s : Shape) :
    s.alpha ^ 2 * s.hH ^ 2 - 2 * s.alpha = s.hH ^ 2 - 2 := by
  have h := s.corner_outer
  dsimp [energyH] at h
  linarith
lemma burnH₁_pos (s : Shape) : 0 < s.burnH₁ := sub_pos.mpr s.one_lt_h
lemma burnH₂_pos (s : Shape) : 0 < s.burnH₂ := sub_pos.mpr s.alpha_h_lt_c
lemma costH_pos (s : Shape) : 0 < s.costH := add_pos s.burnH₁_pos s.burnH₂_pos

/-- Both radial-speed squares must be nonnegative. h is signed: retrograde
coasts are not silently excluded. This is a relaxation, not a trajectory. -/
def Feasible (s : Shape) (w h : ℝ) : Prop :=
  h ^ 2 ≤ w + 2 ∧ s.alpha ^ 2 * h ^ 2 ≤ w + 2 * s.alpha

lemma corner_feasible (s : Shape) : s.Feasible s.energyH s.hH := by
  constructor
  · exact le_of_eq s.corner_inner.symm
  · exact le_of_eq s.corner_outer.symm

/-- The first squared impulse expressed in the normalized invariant pair. -/
def burnSquare₁ (_s : Shape) (w h : ℝ) : ℝ := w + 3 - 2 * h
/-- The second squared impulse expressed in the normalized invariant pair. -/
def burnSquare₂ (s : Shape) (w h : ℝ) : ℝ :=
  w + 3 * s.alpha - 2 * s.alpha * s.circularOuter * h

end Shape
end ClassicalMechanics.HohmannOptimality
