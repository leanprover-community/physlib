/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Sublinear
public import Mathlib.Basic.Real.Pointwise

/-!
# Separation from dominated cones

Hahn–Banach separation of vectors from a convex cone dominated by a vector.

## i. Overview

A convex cone `C` in a real vector space is dominated by `u ∈ C` when every vector plus some
multiple of `u` lies in `C`, as the positive cone of an order-unit space is dominated by its unit.
The least such multiple is a sublinear gauge. Whenever some linear functional is nonnegative on `C`
and positive at `u`, the gauge is finite and Hahn–Banach turns it into separating functionals: a
vector `v` with `v + ε • u ∉ C` is sent to a negative number by a functional nonnegative on `C`.
No topology is involved.

## ii. Key results

- `IsDominatedCone` : a convex cone dominated by a vector.
- `IsDominatedCone.gauge` : the gauge of the cone relative to the dominating vector.
- `IsDominatedCone.exists_apply_neg` : separation of a vector from a dominated cone.

## iii. Table of contents

- A. Dominated cones and their gauge
- B. Separation

## iv. References

* None.

-/

@[expose] public section

open scoped Pointwise

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ## A. Dominated cones and their gauge -/

/-- A convex cone with a dominating element `u`: every vector plus a multiple of `u` lies in it. -/
structure IsDominatedCone (C : Set V) (u : V) : Prop where
  zero_mem : (0 : V) ∈ C
  add_mem : ∀ a ∈ C, ∀ b ∈ C, a + b ∈ C
  smul_mem : ∀ c : ℝ, 0 ≤ c → ∀ a ∈ C, c • a ∈ C
  mem : u ∈ C
  dominates : ∀ v, ∃ t : ℝ, v + t • u ∈ C

namespace IsDominatedCone

variable {C : Set V} {u : V} (hC : IsDominatedCone C u) {Λ₀ : V →ₗ[ℝ] ℝ}
  (hΛ₀ : ∀ c ∈ C, 0 ≤ Λ₀ c) (hΛ₀u : 0 < Λ₀ u)
include hC

/-- The multiples `t` of `u` with `t • u - w` in the cone. -/
def gaugeSet (C : Set V) (u w : V) : Set ℝ := {t | t • u - w ∈ C}

omit hC in
lemma gaugeSet_nonempty (hC : IsDominatedCone C u) (w : V) : (gaugeSet C u w).Nonempty := by
  obtain ⟨t, ht⟩ := hC.dominates (-w)
  exact ⟨t, by rwa [gaugeSet, Set.mem_ofPred_eq, sub_eq_neg_add]⟩

include hΛ₀ hΛ₀u

omit hC in
lemma bddBelow_gaugeSet (w : V) : BddBelow (gaugeSet C u w) :=
  ⟨Λ₀ w / Λ₀ u, fun t ht => by
    have := hΛ₀ _ ht
    rw [map_sub, map_smul, smul_eq_mul, sub_nonneg] at this
    rwa [div_le_iff₀ hΛ₀u]⟩

omit hΛ₀ hΛ₀u in
lemma add_mem_gaugeSet {w w' : V} {t t' : ℝ} (ht : t ∈ gaugeSet C u w)
    (ht' : t' ∈ gaugeSet C u w') : t + t' ∈ gaugeSet C u (w + w') := by
  have := hC.add_mem _ ht _ ht'
  simp only [gaugeSet, Set.mem_ofPred_eq, add_smul] at this ⊢
  convert this using 1; abel

omit hΛ₀ hΛ₀u in
lemma gaugeSet_smul {c : ℝ} (hc : 0 < c) (w : V) :
    gaugeSet C u (c • w) = c • gaugeSet C u w := by
  ext t
  constructor
  · intro ht
    refine ⟨c⁻¹ * t, ?_, by simp [hc.ne']⟩
    have := hC.smul_mem c⁻¹ (inv_nonneg.2 hc.le) _ ht
    simp only [gaugeSet, Set.mem_ofPred_eq, smul_sub, smul_smul, inv_mul_cancel₀ hc.ne',
      one_smul] at this ⊢
    exact this
  · rintro ⟨t, ht, rfl⟩
    have := hC.smul_mem c hc.le _ ht
    simp only [gaugeSet, Set.mem_ofPred_eq, smul_sub, smul_smul, smul_eq_mul] at this ⊢
    exact this

/-- The gauge of the cone with respect to `u`. -/
noncomputable def gauge (C : Set V) (u w : V) : ℝ := sInf (gaugeSet C u w)

omit hC in
lemma gauge_le {w : V} {t : ℝ} (ht : t ∈ gaugeSet C u w) : gauge C u w ≤ t :=
  csInf_le (bddBelow_gaugeSet hΛ₀ hΛ₀u w) ht

lemma gauge_add_le (w w' : V) : gauge C u (w + w') ≤ gauge C u w + gauge C u w' := by
  have h₁ : ∀ t' ∈ gaugeSet C u w', gauge C u (w + w') - t' ≤ gauge C u w := fun t' ht' =>
    le_csInf (hC.gaugeSet_nonempty w) fun t ht => by
      linarith [gauge_le hΛ₀ hΛ₀u (hC.add_mem_gaugeSet ht ht')]
  have h₂ : gauge C u (w + w') - gauge C u w ≤ gauge C u w' :=
    le_csInf (hC.gaugeSet_nonempty w') fun t' ht' => by linarith [h₁ t' ht']
  linarith

omit hΛ₀ hΛ₀u in
lemma gauge_smul {c : ℝ} (hc : 0 < c) (w : V) : gauge C u (c • w) = c * gauge C u w := by
  rw [gauge, hC.gaugeSet_smul hc, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]; rfl

lemma gauge_zero : gauge C u 0 = 0 := by
  refine le_antisymm (gauge_le hΛ₀ hΛ₀u (by simpa [gaugeSet] using hC.zero_mem))
    (le_csInf (hC.gaugeSet_nonempty 0) fun t ht => ?_)
  have := hΛ₀ _ ht
  simp only [sub_zero, map_smul, smul_eq_mul] at this
  exact nonneg_of_mul_nonneg_left this hΛ₀u

/-! ## B. Separation -/

/-- **Separation from a cone.** If `v + ε • u` is outside the cone, a linear functional that is
nonnegative on the cone is negative at `v`. -/
lemma exists_apply_neg {v : V} {ε : ℝ} (hε : 0 < ε) (hv : v + ε • u ∉ C) :
    ∃ Λ : V →ₗ[ℝ] ℝ, (∀ c ∈ C, 0 ≤ Λ c) ∧ Λ v < 0 := by
  obtain ⟨Λ, hΛ, hΛv⟩ := exists_linearMap_le_eq_of_sublinear (N := gauge C u)
    (fun _ hc w => hC.gauge_smul hc w) (hC.gauge_add_le hΛ₀ hΛ₀u) (-v)
  refine ⟨Λ, fun c hc => ?_, ?_⟩
  · have := (hΛ (-c)).trans (gauge_le hΛ₀ hΛ₀u (t := 0) (by simpa [gaugeSet] using hc))
    rw [map_neg] at this; linarith
  · have hge : ε ≤ gauge C u (-v) := le_csInf (hC.gaugeSet_nonempty _) fun t ht => by
      by_contra! htε
      refine hv ?_
      have := hC.add_mem _ ht _ (hC.smul_mem (ε - t) (by linarith) _ hC.mem)
      simp only [sub_neg_eq_add] at this
      convert this using 1
      rw [sub_smul]; abel
    rw [map_neg] at hΛv
    linarith

end IsDominatedCone
