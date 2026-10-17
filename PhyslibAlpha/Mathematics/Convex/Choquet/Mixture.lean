/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.UnitInterval
public import Mathlib.Tactic.Module

/-!
# Mixtures in a convex set

Mixtures of points in a convex set, convex functions, and extreme points as non-midpoints.

## i. Overview

In a convex set `S` any two points can be mixed: `t x + (1 - t) y` lies in `S` for `0 ≤ t ≤ 1`. For
states this means preparing `x` with probability `t` and `y` otherwise. A function on `S` is convex
when its value at a mixture is at most the mixture of its values.

A point of `S` is extreme when it is not a mixture of other points. For states, the extreme points
are the pure states. A point that is not extreme is the midpoint of two different points of `S`.

## ii. Key results

- `Choquet.mix` is the mixture of two points of a convex set.
- `Choquet.IsConvexFunction` states that a function on `S` lies below its chords.
- `Choquet.exists_mixHalf_eq_of_notMem_extremePoints` proves that a point that is not extreme is the
  midpoint of two different points.

## iii. Table of contents

- A. Mixtures
- B. Convex functions
- C. Extreme points as non-midpoints

## iv. References

* None.

-/

@[expose] public section

open Set

namespace Choquet

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {S : Set V} (hS : Convex ℝ S)

/-!

## A. Mixtures

-/

/-- The mixture `t x + (1 - t) y` of two points of a convex set. -/
def mix (x y : S) (t : unitInterval) : S :=
  ⟨(t : ℝ) • (x : V) + (1 - (t : ℝ)) • (y : V), hS x.2 y.2 t.2.1 (sub_nonneg.2 t.2.2) (by ring)⟩

@[simp] lemma coe_mix (x y : S) (t : unitInterval) :
    (mix hS x y t : V) = (t : ℝ) • (x : V) + (1 - (t : ℝ)) • (y : V) := rfl

/-- The weight `1/2`. -/
noncomputable def half : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

@[simp] lemma half_coe : (half : ℝ) = 1 / 2 := rfl

/-- The midpoint of a pair of points. -/
noncomputable def mixHalf (p : S × S) : S := mix hS p.1 p.2 half

lemma continuous_mixHalf [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] :
    Continuous (mixHalf hS) :=
  continuous_induced_rng.2 <| by
    change Continuous fun p : S × S => (1 / 2 : ℝ) • (p.1 : V) + (1 - 1 / 2 : ℝ) • (p.2 : V)
    fun_prop

/-!

## B. Convex functions

-/

/-- A function on `S` lying below the chord of every mixture. -/
def IsConvexFunction (f : S → ℝ) : Prop :=
  ∀ x y t, f (mix hS x y t) ≤ (t : ℝ) * f x + (1 - (t : ℝ)) * f y

/-- Continuous linear functionals are convex on `S`. -/
lemma isConvexFunction_apply [TopologicalSpace V] (ℓ : V →L[ℝ] ℝ) :
    IsConvexFunction hS fun y => ℓ y := fun x y t => by simp

/-!

## C. Extreme points as non-midpoints

-/

/-- The midpoint of two distinct points is not extreme. -/
lemma mixHalf_notMem_extremePoints {p q : S} (hpq : p ≠ q) :
    (mixHalf hS (p, q) : V) ∉ S.extremePoints ℝ := fun h => by
  have := (mem_extremePoints.1 h).2 p p.2 q q.2
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by simp [mixHalf]; norm_num⟩
  exact hpq (Subtype.ext (this.1.trans this.2.symm))

/-- Two points of `S` on either side of `a x₁ + b x₂` at weight distance `min a b`. -/
lemma sub_smul_eq_of_mixHalf {x₁ x₂ : V} {a b r : ℝ} :
    ((a + r) • x₁ + (b - r) • x₂) - ((a - r) • x₁ + (b + r) • x₂) = (2 * r) • (x₁ - x₂) := by
  module

/-- A non-extreme point of `S` is the midpoint of two distinct points of `S`. -/
lemma exists_mixHalf_eq_of_notMem_extremePoints {x : S} (hx : (x : V) ∉ S.extremePoints ℝ) :
    ∃ p q : S, p ≠ q ∧ mixHalf hS (p, q) = x := by
  simp only [mem_extremePoints, x.2, true_and, not_forall] at hx
  obtain ⟨x₁, h₁, x₂, h₂, ⟨a, b, ha, hb, hab, hx'⟩, hne⟩ := hx
  have h12 : x₁ ≠ x₂ := by
    rintro rfl
    rw [← add_smul, hab, one_smul] at hx'
    exact hne ⟨hx', hx'⟩
  have hr : 0 < min a b := lt_min ha hb
  refine ⟨⟨(a + min a b) • x₁ + (b - min a b) • x₂, hS h₁ h₂ (by positivity)
      (sub_nonneg.2 (min_le_right a b)) (by linarith)⟩,
    ⟨(a - min a b) • x₁ + (b + min a b) • x₂, hS h₁ h₂ (sub_nonneg.2 (min_le_left a b))
      (by positivity) (by linarith)⟩, fun h => h12 ?_, Subtype.ext ?_⟩
  · have := sub_smul_eq_of_mixHalf (x₁ := x₁) (x₂ := x₂) (a := a) (b := b) (r := min a b)
    have hv : (a + min a b) • x₁ + (b - min a b) • x₂ = (a - min a b) • x₁ + (b + min a b) • x₂ :=
      congrArg Subtype.val h
    rw [hv, sub_self, eq_comm, smul_eq_zero] at this
    exact sub_eq_zero.1 (this.resolve_left (by positivity))
  · simp only [mixHalf, coe_mix, half_coe, ← hx']
    module

end Choquet
