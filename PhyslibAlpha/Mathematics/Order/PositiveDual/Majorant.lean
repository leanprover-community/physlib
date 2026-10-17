/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Order.PositiveDual.Basic
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Basic.Real.Pointwise

/-!
# Positive majorants

A positive functional of weight at most m at u that dominates P - N, via Hahn–Banach.

## i. Overview

Fix an order unit `u` and two positive functionals `P` and `N`. If `P - N` is at most
`m` on the order interval `[0, u]`, then `P` lies below `π + N` for a positive functional `π` with
`π u ≤ m`. The functional `π` comes from Hahn–Banach, applied to a gauge that measures how much
`P - N` can exceed `m` times the multiple of `u` needed to dominate an element.

## ii. Key results

- `PositiveLinearMap.majorant` : the majorant gauge.
- `PositiveLinearMap.exists_le_add_of_forall_le` : a positive functional of weight at most `m` at
  `u` that makes up for `P - N`.

## iii. Table of contents

- A. The majorant gauge
- B. Positive majorants

## iv. References

* None.

-/

@[expose] public section

open scoped Pointwise

namespace PositiveLinearMap

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E]
  [PosSMulMono ℝ E] {u : E} (P N : E →ₚ[ℝ] ℝ) {m : ℝ}

/-! ## A. The majorant gauge -/

variable (u) in
/-- The values `m t - P a + N a` over all `t ≥ 0` and `a ≥ 0` with `x + a ≤ t • u`. -/
def majorantSet (m : ℝ) (x : E) : Set ℝ :=
  {r | ∃ t : ℝ, 0 ≤ t ∧ ∃ a : E, 0 ≤ a ∧ x + a ≤ t • u ∧ r = m * t - P a + N a}

variable (u) in
/-- The majorant gauge. -/
noncomputable def majorant (m : ℝ) (x : E) : ℝ := sInf (majorantSet u P N m x)

variable (hu : IsOrderUnit u) (hm : ∀ a : E, 0 ≤ a → a ≤ u → P a - N a ≤ m)
include hu hm

omit hm [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
lemma majorantSet_nonempty (x : E) : (majorantSet u P N m x).Nonempty := by
  obtain ⟨n, hn⟩ := hu.isStrongUnit x
  exact ⟨_, n, n.cast_nonneg, 0, le_rfl, by simpa [Nat.cast_smul_eq_nsmul] using hn, rfl⟩

omit hu [IsOrderedAddMonoid E] in
lemma sub_le_smul {a : E} {s : ℝ} (hs : 0 ≤ s) (ha : 0 ≤ a) (has : a ≤ s • u) :
    P a - N a ≤ s * m := by
  rcases hs.eq_or_lt with rfl | hs
  · obtain rfl : a = 0 := le_antisymm (by simpa using has) ha
    simp
  have := hm (s⁻¹ • a) (smul_nonneg (inv_nonneg.2 hs.le) ha)
    (by rw [inv_smul_le_iff_of_pos hs]; exact has)
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_sub, inv_mul_le_iff₀ hs] at this
  exact this

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
lemma m_nonneg : 0 ≤ m := by simpa using hm 0 le_rfl hu.nonneg

lemma bddBelow_majorantSet (x : E) : BddBelow (majorantSet u P N m x) := by
  obtain ⟨n, hlo, -⟩ := hu.exists_two_sided x
  refine ⟨-(n * m), ?_⟩
  rintro _ ⟨t, ht, a, ha, hxa, rfl⟩
  have hle : a ≤ (t + n) • u := by
    rw [add_smul, Nat.cast_smul_eq_nsmul]
    calc a = (x + a) - x := by abel
      _ ≤ t • u - -(n • u) := sub_le_sub hxa hlo
      _ = _ := by abel
  have := sub_le_smul P N hm (by positivity) ha hle
  nlinarith

lemma majorant_le {x : E} {r : ℝ} (hr : r ∈ majorantSet u P N m x) : majorant u P N m x ≤ r :=
  csInf_le (bddBelow_majorantSet P N hu hm x) hr

lemma majorant_add_le (x y : E) :
    majorant u P N m (x + y) ≤ majorant u P N m x + majorant u P N m y := by
  have key : ∀ r ∈ majorantSet u P N m x, ∀ r' ∈ majorantSet u P N m y,
      majorant u P N m (x + y) ≤ r + r' := by
    rintro _ ⟨t, ht, a, ha, hxa, rfl⟩ _ ⟨t', ht', a', ha', hya, rfl⟩
    refine majorant_le P N hu hm ⟨t + t', by positivity, a + a', add_nonneg ha ha', ?_, ?_⟩
    · rw [add_smul]
      calc x + y + (a + a') = (x + a) + (y + a') := by abel
        _ ≤ _ := add_le_add hxa hya
    · simp only [map_add]; ring
  have h₁ : ∀ r' ∈ majorantSet u P N m y, majorant u P N m (x + y) - r' ≤ majorant u P N m x :=
    fun r' hr' => le_csInf (majorantSet_nonempty P N hu x) fun r hr => by
      linarith [key r hr r' hr']
  have h₂ : majorant u P N m (x + y) - majorant u P N m x ≤ majorant u P N m y :=
    le_csInf (majorantSet_nonempty P N hu y) fun r' hr' => by linarith [h₁ r' hr']
  linarith

omit hu hm [IsOrderedAddMonoid E] in
lemma majorantSet_smul {c : ℝ} (hc : 0 < c) (x : E) :
    majorantSet u P N m (c • x) = c • majorantSet u P N m x := by
  ext r
  constructor
  · rintro ⟨t, ht, a, ha, hxa, rfl⟩
    refine ⟨m * (c⁻¹ * t) - P (c⁻¹ • a) + N (c⁻¹ • a), ⟨c⁻¹ * t, by positivity, c⁻¹ • a,
      smul_nonneg (inv_nonneg.2 hc.le) ha, ?_, rfl⟩, ?_⟩
    · have := smul_le_smul_of_nonneg_left hxa (inv_nonneg.2 hc.le)
      rwa [smul_add, inv_smul_smul₀ hc.ne', smul_smul] at this
    · simp only [map_smul, smul_eq_mul]
      field_simp
  · rintro ⟨_, ⟨t, ht, a, ha, hxa, rfl⟩, rfl⟩
    refine ⟨c * t, by positivity, c • a, smul_nonneg hc.le ha, ?_, ?_⟩
    · rw [← smul_add, ← smul_smul]; exact smul_le_smul_of_nonneg_left hxa hc.le
    · simp only [map_smul, smul_eq_mul]; ring

omit hu hm [IsOrderedAddMonoid E] in
lemma majorant_smul {c : ℝ} (hc : 0 < c) (x : E) :
    majorant u P N m (c • x) = c * majorant u P N m x := by
  rw [majorant, majorantSet_smul P N hc, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul]
  rfl

/-! ## B. Positive majorants -/

/-- A linear functional below the majorant gauge. -/
lemma exists_le_majorant : ∃ g : E →ₗ[ℝ] ℝ, ∀ x, g x ≤ majorant u P N m x := by
  obtain ⟨g, -, hg⟩ := exists_extension_of_le_sublinear ⟨⊥, 0⟩ (majorant u P N m)
    (fun _ hc x => majorant_smul P N hc x) (majorant_add_le P N hu hm) fun x => by
      obtain ⟨_, hx⟩ := x
      obtain rfl := Submodule.mem_bot ℝ |>.1 hx
      show (0 : ℝ) ≤ _
      refine le_csInf (majorantSet_nonempty P N hu 0) ?_
      rintro _ ⟨t, ht, a, ha, hxa, rfl⟩
      have := sub_le_smul P N hm ht ha (by simpa using hxa)
      linarith
  exact ⟨g, hg⟩

/-- If `P - N` is at most `m` on `[0, u]`, then `P ≤ π + N` for a positive functional `π` with
`π u ≤ m`. -/
lemma exists_le_add_of_forall_le : ∃ π : E →ₚ[ℝ] ℝ, (∀ f, 0 ≤ f → P f ≤ π f + N f) ∧ π u ≤ m := by
  obtain ⟨g, hg⟩ := exists_le_majorant P N hu hm
  have hneg {f : E} {a : E} (ha : 0 ≤ a) (haf : a ≤ f) : g (-f) ≤ -P a + N a :=
    (hg _).trans (majorant_le P N hu hm ⟨0, le_rfl, a, ha, by simpa using haf, by ring⟩)
  refine ⟨mk₀ g fun f hf => ?_, fun f hf => ?_, ?_⟩
  · have := hneg le_rfl hf
    rw [map_zero, map_zero, map_neg] at this
    linarith
  · have := hneg hf le_rfl
    rw [map_neg] at this
    change P f ≤ g f + N f
    linarith
  · exact (hg u).trans (majorant_le P N hu hm ⟨1, zero_le_one, 0, le_rfl, by simp, by simp⟩)

end PositiveLinearMap
