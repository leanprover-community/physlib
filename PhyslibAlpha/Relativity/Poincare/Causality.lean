/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Relativity.Poincare.Basic
public import PhyslibAlpha.Relativity.Causality.LightCone

/-!

# The causal structure is Poincaré invariant

Orthochronous Poincaré transformations preserve causal futures and pasts.

## i. Overview

An event `q` causally follows `p` when the difference lies in the closed future light cone.
A Lorentz transformation preserves the Minkowski product. An orthochronous one also preserves the
direction of time, so it maps the future light cone to itself. A translation does not change
differences. So an orthochronous Poincaré transformation maps the causal future of a set to the
causal future of the image. A transformation that reverses time exchanges causal future and past.

## ii. Key results

- `causallyFollows_zero_smul` : orthochronous Lorentz maps preserve the future light cone.
- `causallyFollows_smul_iff` : orthochronous Poincaré maps preserve causal order.
- `causalFuture_smul` : the causal future of the image is the image of the causal future.
- `causalFuture_smul_of_not` : a time-reversing map sends the causal future to the causal past.

## iii. Table of contents

- A. The future light cone
- B. The causal order
- C. Causal futures and pasts of sets

## iv. References

None.

## A. The future light cone

- `causallyFollows_zero_smul` : orthochronous Lorentz maps preserve the future light cone.

## B. The causal order

- `causallyFollows_smul_iff` : orthochronous Poincaré maps preserve causal order.

## C. Causal futures and pasts of sets

- `causalFuture_smul` : the causal future of the image is the image of the causal future.
-/

@[expose] public section

noncomputable section

open Lorentz.Vector Minkowski CausalRelation
open scoped Pointwise

namespace PoincareGroup

variable {d : ℕ}

section Cone

/-- The time component is the Minkowski product with the unit time vector. -/
lemma timeComponent_eq_minkowski (p : SpaceTime d) :
    p.timeComponent = ⟪p, Lorentz.Vector.basis (Sum.inl 0)⟫ₘ := by
  rw [minkowskiProduct_basis_right]
  simp [minkowskiMatrix.inl_0_inl_0]

/-- An orthochronous Lorentz transformation maps the closed future light cone into itself. -/
lemma causallyFollows_zero_smul {Λ : LorentzGroup d} (hΛ : LorentzGroup.IsOrthochronous Λ)
    {u : SpaceTime d} (hu : causallyFollows 0 u) : causallyFollows 0 (Λ • u) := by
  have hu' := hu
  rw [causallyFollows_zero_iff] at hu ⊢
  obtain ⟨h1, h2⟩ := hu
  refine ⟨by rw [minkowskiProduct_invariant]; exact h1, ?_⟩
  set e : SpaceTime d := Lorentz.Vector.basis (Sum.inl 0) with he
  have hv : causallyFollows 0 (Λ⁻¹ • e) := by
    rw [causallyFollows_zero_iff]
    refine ⟨?_, ?_⟩
    · rw [minkowskiProduct_invariant, he, minkowskiProduct_basis_left]
      simp [minkowskiMatrix.inl_0_inl_0]
    · have hΛ' : 0 ≤ (Λ⁻¹).1 (Sum.inl 0) (Sum.inl 0) :=
        LorentzGroup.isOrthochronous_inv_iff.mpr hΛ
      change 0 ≤ (Λ⁻¹ • e) (Sum.inl 0)
      rw [Lorentz.Vector.smul_eq_sum, Finset.sum_eq_single (Sum.inl 0)]
      · simpa [he] using hΛ'
      · intro j _ hj
        simp [he, Lorentz.Vector.basis_apply, Ne.symm hj]
      · intro h; exact absurd (Finset.mem_univ _) h
  have hge := sqrt_mul_sqrt_le_minkowskiProduct_of_causallyFollows hu' hv
  have hnn : 0 ≤ ⟪u, Λ⁻¹ • e⟫ₘ := le_trans (by positivity) hge
  rw [timeComponent_eq_minkowski]
  calc (0 : ℝ) ≤ ⟪u, Λ⁻¹ • e⟫ₘ := hnn
    _ = ⟪Λ • u, Λ • (Λ⁻¹ • e)⟫ₘ := (minkowskiProduct_invariant _ _ Λ).symm
    _ = ⟪Λ • u, e⟫ₘ := by rw [smul_inv_smul]

/-- The vectors between two transformed events are the Lorentz image of the original vector. -/
lemma smul_sub_smul (g : PoincareGroup d) (p q : SpaceTime d) :
    g • q - g • p = g.lorentz • (q - p) := by
  rw [smul_def, smul_def, Lorentz.Vector.smul_sub]
  abel

end Cone

section Order

/-- An orthochronous Lorentz transformation preserves the closed future light cone. -/
lemma causallyFollows_zero_smul_iff {Λ : LorentzGroup d} (hΛ : LorentzGroup.IsOrthochronous Λ)
    (u : SpaceTime d) : causallyFollows 0 (Λ • u) ↔ causallyFollows 0 u := by
  refine ⟨fun h => ?_, causallyFollows_zero_smul hΛ⟩
  simpa using causallyFollows_zero_smul (LorentzGroup.isOrthochronous_inv_iff.mpr hΛ) h

/-- An orthochronous Poincaré transformation preserves the causal order. -/
lemma causallyFollows_smul_iff {g : PoincareGroup d} (hg : g.IsOrthochronous) (p q : SpaceTime d) :
    causallyFollows (g • p) (g • q) ↔ causallyFollows p q := by
  have hg' : LorentzGroup.IsOrthochronous g.lorentz := hg
  rw [causallyFollows_iff_displacement (g • p) (g • q), causallyFollows_iff_displacement p q,
    smul_sub_smul]
  exact causallyFollows_zero_smul_iff hg' (q - p)

/-- A Poincaré transformation that reverses time reverses the causal order. -/
lemma causallyFollows_smul_iff_of_not {g : PoincareGroup d} (hg : ¬ g.IsOrthochronous)
    (p q : SpaceTime d) : causallyFollows (g • p) (g • q) ↔ causallyFollows q p := by
  have hg' : ¬ LorentzGroup.IsOrthochronous g.lorentz := hg
  rw [causallyFollows_iff_displacement (g • p) (g • q), causallyFollows_iff_displacement q p,
    smul_sub_smul]
  have h : g.lorentz • (q - p) = (-g.lorentz) • (p - q) := by
    rw [Lorentz.Vector.neg_smul, ← Lorentz.Vector.smul_neg, neg_sub]
  rw [h]
  exact causallyFollows_zero_smul_iff (LorentzGroup.neg_isOrthochronous_iff_not.mpr hg') (p - q)

end Order

section Sets

/-- An orthochronous Poincaré transformation maps the causal future of a set to the causal
future of its image. -/
lemma causalFuture_smul {g : PoincareGroup d} (hg : g.IsOrthochronous) (K : Set (SpaceTime d)) :
    (causalRelation d).causalFuture (g • K) = g • (causalRelation d).causalFuture K := by
  ext q
  constructor
  · rintro ⟨p, hp, hpq⟩
    obtain ⟨p', hp', rfl⟩ := Set.mem_smul_set.mp hp
    refine Set.mem_smul_set.mpr ⟨g⁻¹ • q, ⟨p', hp', ?_⟩, smul_inv_smul g q⟩
    have : causallyFollows (g • p') (g • (g⁻¹ • q)) := by
      rw [smul_inv_smul]; exact hpq
    exact (causallyFollows_smul_iff hg _ _).mp this
  · rintro hq
    obtain ⟨q', ⟨p', hp', hpq⟩, rfl⟩ := Set.mem_smul_set.mp hq
    exact ⟨g • p', Set.smul_mem_smul_set hp', (causallyFollows_smul_iff hg _ _).mpr hpq⟩

/-- An orthochronous Poincaré transformation maps the causal past of a set to the causal past of
its image. -/
lemma causalPast_smul {g : PoincareGroup d} (hg : g.IsOrthochronous) (K : Set (SpaceTime d)) :
    (causalRelation d).causalPast (g • K) = g • (causalRelation d).causalPast K := by
  ext p
  constructor
  · rintro ⟨q, hq, hpq⟩
    obtain ⟨q', hq', rfl⟩ := Set.mem_smul_set.mp hq
    refine Set.mem_smul_set.mpr ⟨g⁻¹ • p, ⟨q', hq', ?_⟩, smul_inv_smul g p⟩
    have : causallyFollows (g • (g⁻¹ • p)) (g • q') := by
      rw [smul_inv_smul]; exact hpq
    exact (causallyFollows_smul_iff hg _ _).mp this
  · rintro hp
    obtain ⟨p', ⟨q', hq', hpq⟩, rfl⟩ := Set.mem_smul_set.mp hp
    exact ⟨g • q', Set.smul_mem_smul_set hq', (causallyFollows_smul_iff hg _ _).mpr hpq⟩

/-- A Poincaré transformation that reverses time maps the causal future of a set to the causal
past of its image. -/
lemma causalFuture_smul_of_not {g : PoincareGroup d} (hg : ¬ g.IsOrthochronous)
    (K : Set (SpaceTime d)) :
    (causalRelation d).causalFuture (g • K) = g • (causalRelation d).causalPast K := by
  ext q
  constructor
  · rintro ⟨p, hp, hpq⟩
    obtain ⟨p', hp', rfl⟩ := Set.mem_smul_set.mp hp
    refine Set.mem_smul_set.mpr ⟨g⁻¹ • q, ⟨p', hp', ?_⟩, smul_inv_smul g q⟩
    have : causallyFollows (g • p') (g • (g⁻¹ • q)) := by
      rw [smul_inv_smul]; exact hpq
    exact (causallyFollows_smul_iff_of_not hg _ _).mp this
  · rintro hq
    obtain ⟨q', ⟨p', hp', hpq⟩, rfl⟩ := Set.mem_smul_set.mp hq
    exact ⟨g • p', Set.smul_mem_smul_set hp', (causallyFollows_smul_iff_of_not hg _ _).mpr hpq⟩

/-- A Poincaré transformation that reverses time maps the causal past of a set to the causal
future of its image. -/
lemma causalPast_smul_of_not {g : PoincareGroup d} (hg : ¬ g.IsOrthochronous)
    (K : Set (SpaceTime d)) :
    (causalRelation d).causalPast (g • K) = g • (causalRelation d).causalFuture K := by
  ext p
  constructor
  · rintro ⟨q, hq, hpq⟩
    obtain ⟨q', hq', rfl⟩ := Set.mem_smul_set.mp hq
    refine Set.mem_smul_set.mpr ⟨g⁻¹ • p, ⟨q', hq', ?_⟩, smul_inv_smul g p⟩
    have : causallyFollows (g • (g⁻¹ • p)) (g • q') := by
      rw [smul_inv_smul]; exact hpq
    exact (causallyFollows_smul_iff_of_not hg _ _).mp this
  · rintro hp
    obtain ⟨p', ⟨q', hq', hpq⟩, rfl⟩ := Set.mem_smul_set.mp hp
    exact ⟨g • q', Set.smul_mem_smul_set hq', (causallyFollows_smul_iff_of_not hg _ _).mpr hpq⟩

/-- A Poincaré transformation maps the causal hull of a set to the causal hull of its image. -/
lemma causalHull_smul (g : PoincareGroup d) (K : Set (SpaceTime d)) :
    (causalRelation d).causalHull (g • K) = g • (causalRelation d).causalHull K := by
  unfold CausalRelation.causalHull
  by_cases hg : g.IsOrthochronous
  · rw [causalFuture_smul hg, causalPast_smul hg, Set.smul_set_union]
  · rw [causalFuture_smul_of_not hg, causalPast_smul_of_not hg, Set.smul_set_union,
      Set.union_comm]

end Sets

end PoincareGroup
