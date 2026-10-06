/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Convex.Cone.Extension

/-!
# Linear minorants of sublinear functionals

A sublinear functional has a linear minorant attaining it at any given point (Hahn–Banach).

## i. Overview

A sublinear functional is the largest of the linear functionals below it. At every point the
Hahn–Banach theorem gives a linear functional below it that agrees with it there.

## ii. Key results

- `exists_linearMap_le_eq_of_sublinear` proves that a linear functional below a sublinear functional
  can be chosen to agree with it at a given point.

## iii. Table of contents

- A. Linear minorants

## iv. References

* None.

-/

@[expose] public section

/-!

## A. Linear minorants

-/

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {N : V → ℝ}
  (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x) (N_add : ∀ x y, N (x + y) ≤ N x + N y)

include N_hom in
lemma map_zero_of_sublinear : N 0 = 0 := by
  have := N_hom 2 two_pos 0
  rw [smul_zero] at this
  linarith

include N_hom N_add in
/-- A sublinear functional dominates the multiples of its value at a point. -/
lemma smul_le_of_sublinear (c : ℝ) (x : V) : c * N x ≤ N (c • x) := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · have h0 := N_add x (-x)
    rw [add_neg_cancel, map_zero_of_sublinear N_hom] at h0
    have := N_hom (-c) (neg_pos.2 hc) (-x)
    rw [smul_neg, neg_smul, neg_neg] at this
    nlinarith
  · simp [map_zero_of_sublinear N_hom]
  · exact (N_hom c hc x).ge

include N_hom N_add in
/-- **Hahn–Banach**: a sublinear functional has a linear minorant attaining it at `x`. -/
lemma exists_linearMap_le_eq_of_sublinear (x : V) :
    ∃ g : V →ₗ[ℝ] ℝ, (∀ y, g y ≤ N y) ∧ g x = N x := by
  have H : ∀ c : ℝ, c • x = 0 → (RingHom.id ℝ) c • N x = 0 := fun c hc => by
    rcases smul_eq_zero.1 hc with rfl | rfl <;> simp [map_zero_of_sublinear N_hom]
  obtain ⟨g, hg, hgN⟩ := exists_extension_of_le_sublinear (LinearPMap.mkSpanSingleton' x (N x) H)
    N N_hom N_add fun ⟨z, hz⟩ => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
      rw [LinearPMap.mkSpanSingleton'_apply]
      exact smul_le_of_sublinear N_hom N_add c x
  exact ⟨g, hgN, (hg ⟨x, Submodule.mem_span_singleton_self x⟩).trans
    (LinearPMap.mkSpanSingleton'_apply_self _ _ _ _)⟩
