/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.Mathematics.Order.PositiveDual.Basic
public import PhyslibAlpha.Mathematics.Sublinear

/-!
# Upper envelopes

Splittings of a positive functional attain the upper envelope of a finite family.

## i. Overview

Take finitely many elements `A₁, …, Aₙ` of a directed ordered real vector space and a positive
functional `φ`. Their upper envelope at `φ` is the smallest value `φ B` over all common upper
bounds `B` of the `Aᵢ`.

Split `φ` into positive pieces `φ₁ + … + φₙ` and let each piece evaluate its own element. The
total `φ₁ A₁ + … + φₙ Aₙ` never exceeds the upper envelope, and by the Hahn–Banach theorem some
splitting reaches it.

## ii. Key results

- `PositiveLinearMap.upperEnvelope` is the upper envelope of finitely many elements.
- `PositiveLinearMap.sum_apply_le_upperEnvelope` proves that splittings stay below the upper
  envelope.
- `PositiveLinearMap.exists_sum_eq_upperEnvelope` proves that some splitting reaches it.

## iii. Table of contents

- A. Upper envelopes
- B. Splittings attain the upper envelope

## iv. References

- E. M. Alfsen, *Compact Convex Sets and Boundary Integrals*, Springer, 1971, ch. I.3, II.3.

-/

@[expose] public section

open Set

/-!

## A. Upper envelopes

-/

namespace PositiveLinearMap

variable {E : Type*} [AddCommGroup E] [PartialOrder E] [IsOrderedAddMonoid E] [Module ℝ E]
  [PosSMulMono ℝ E] [IsDirectedOrder E] {ι : Type*} [Fintype ι]

/-- The upper envelope of a finite family at a positive functional: the least value
of the functional on a common upper bound of the family. -/
noncomputable def upperEnvelope (s : ι → E) (α : E →ₚ[ℝ] ℝ) : ℝ :=
  sInf ((fun b => α b) '' upperBounds (range s))

omit [IsOrderedAddMonoid E] [Module ℝ E] [PosSMulMono ℝ E] in
/-- A finite family in a directed order has an upper bound. -/
lemma upperBounds_nonempty (s : ι → E) : (upperBounds (range s)).Nonempty :=
  (Set.finite_range s).bddAbove

variable {s : ι → E} {α : E →ₚ[ℝ] ℝ}

omit [Fintype ι] [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsDirectedOrder E] in
lemma upperEnvelope_le [Nonempty ι] {b : E} (hb : b ∈ upperBounds (range s)) :
    upperEnvelope s α ≤ α b := by
  refine csInf_le ⟨α (s (Classical.arbitrary ι)), ?_⟩ ⟨b, hb, rfl⟩
  rintro _ ⟨b', hb', rfl⟩
  exact OrderHomClass.mono α (hb' ⟨_, rfl⟩)

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
lemma le_upperEnvelope {r : ℝ} (h : ∀ b ∈ upperBounds (range s), r ≤ α b) :
    r ≤ upperEnvelope s α :=
  le_csInf ((upperBounds_nonempty s).image _) fun _ ⟨b, hb, e⟩ => e ▸ h b hb

omit [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
lemma exists_mem_upperBounds_lt {r : ℝ} (h : upperEnvelope s α < r) :
    ∃ b ∈ upperBounds (range s), α b < r := by
  obtain ⟨_, ⟨b, hb, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt ((upperBounds_nonempty s).image _) h
  exact ⟨b, hb, hlt⟩

omit [Fintype ι] [Module ℝ E] [PosSMulMono ℝ E] [IsDirectedOrder E] in
lemma add_mem_upperBounds {c c' : ι → E} {b b' : E} (hb : b ∈ upperBounds (range c))
    (hb' : b' ∈ upperBounds (range c')) : b + b' ∈ upperBounds (range (c + c')) := by
  rintro _ ⟨i, rfl⟩
  exact add_le_add (hb ⟨i, rfl⟩) (hb' ⟨i, rfl⟩)

omit [Fintype ι] [IsOrderedAddMonoid E] [IsDirectedOrder E] in
lemma smul_mem_upperBounds {c : ι → E} {b : E} {t : ℝ} (ht : 0 ≤ t)
    (hb : b ∈ upperBounds (range c)) : t • b ∈ upperBounds (range (t • c)) := by
  rintro _ ⟨i, rfl⟩
  exact smul_le_smul_of_nonneg_left (hb ⟨i, rfl⟩) ht

variable [Nonempty ι]

omit [PosSMulMono ℝ E] in
lemma upperEnvelope_add_family_le (c c' : ι → E) :
    upperEnvelope (c + c') α ≤ upperEnvelope c α + upperEnvelope c' α := by
  have key : ∀ b' ∈ upperBounds (range c'), upperEnvelope (c + c') α - α b' ≤ upperEnvelope c α :=
    fun b' hb' => le_upperEnvelope fun b hb => by
      have := upperEnvelope_le (α := α) (add_mem_upperBounds hb hb')
      rw [map_add] at this
      linarith
  linarith [le_upperEnvelope (s := c') (α := α)
    (r := upperEnvelope (c + c') α - upperEnvelope c α) fun b' hb' => by linarith [key b' hb']]

omit [IsOrderedAddMonoid E] in
lemma upperEnvelope_smul_family {t : ℝ} (ht : 0 < t) (c : ι → E) :
    upperEnvelope (t • c) α = t * upperEnvelope c α := by
  refine le_antisymm ?_ (le_upperEnvelope fun b hb => ?_)
  · rw [← div_le_iff₀' ht]
    refine le_upperEnvelope fun b hb => ?_
    rw [div_le_iff₀' ht, ← smul_eq_mul, ← map_smul]
    exact upperEnvelope_le (smul_mem_upperBounds ht.le hb)
  · have := upperEnvelope_le (α := α) (smul_mem_upperBounds (inv_nonneg.2 ht.le) hb)
    rw [inv_smul_smul₀ ht.ne', map_smul, smul_eq_mul] at this
    calc t * upperEnvelope c α ≤ t * (t⁻¹ * α b) := by gcongr
      _ = α b := by field_simp

omit [Fintype ι] [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsDirectedOrder E] in
lemma upperEnvelope_const_le (x : E) : upperEnvelope (fun _ : ι => x) α ≤ α x :=
  upperEnvelope_le (by rintro _ ⟨i, rfl⟩; exact le_rfl)

omit [Fintype ι] [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [IsDirectedOrder E] in
lemma upperEnvelope_single_le [DecidableEq ι] (i : ι) {x : E} (hx : x ≤ 0) :
    upperEnvelope (Pi.single i x) α ≤ 0 :=
  (upperEnvelope_le (b := 0) (by rintro _ ⟨j, rfl⟩; rcases eq_or_ne j i with rfl | h <;> simp [*]))
    |>.trans_eq (map_zero α)

/-!

## B. Splittings attain the upper envelope

-/

omit [Nonempty ι] [IsOrderedAddMonoid E] [PosSMulMono ℝ E] in
/-- Splitting a functional and letting each piece evaluate its own element stays below the
upper envelope. -/
lemma sum_apply_le_upperEnvelope {ψ : ι → E →ₚ[ℝ] ℝ} (hψ : ∑ i, ψ i = α) :
    ∑ i, ψ i (s i) ≤ upperEnvelope s α :=
  le_upperEnvelope fun b hb => by
    rw [← hψ, sum_apply]
    exact Finset.sum_le_sum fun i _ => OrderHomClass.mono (ψ i) (hb ⟨i, rfl⟩)

/-- A linear functional on families below the upper envelope, seen on one member. -/
noncomputable def piece [DecidableEq ι] (g : (ι → E) →ₗ[ℝ] ℝ)
    (hg : ∀ c, g c ≤ upperEnvelope c α) (i : ι) : E →ₚ[ℝ] ℝ :=
  .mk₀ (g.comp (LinearMap.single ℝ (fun _ => E) i)) fun x hx => by
    have := (hg _).trans (upperEnvelope_single_le (α := α) i (neg_nonpos.2 hx))
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single] at this ⊢
    rw [Pi.single_neg, map_neg] at this
    linarith

omit [PosSMulMono ℝ E] [IsDirectedOrder E] in
lemma sum_piece [DecidableEq ι] (g : (ι → E) →ₗ[ℝ] ℝ) (hg : ∀ c, g c ≤ upperEnvelope c α) :
    ∑ i, piece g hg i = α := by
  refine ext fun x => ?_
  have hx : g (fun _ => x) = α x := le_antisymm ((hg _).trans (upperEnvelope_const_le x)) (by
    have := (hg (fun _ => -x)).trans (upperEnvelope_const_le (-x))
    rw [show (fun _ : ι => -x) = -fun _ => x from rfl, map_neg, map_neg] at this
    linarith)
  rw [sum_apply, ← hx,
    ← LinearMap.sum_single_apply (φ := fun _ => E) (v := fun _ : ι => x), map_sum]
  rfl

/-- **Duality**: some splitting of the functional attains the upper envelope. -/
lemma exists_sum_eq_upperEnvelope (s : ι → E) (α : E →ₚ[ℝ] ℝ) :
    ∃ ψ : ι → E →ₚ[ℝ] ℝ, ∑ i, ψ i = α ∧ ∑ i, ψ i (s i) = upperEnvelope s α := by
  classical
  obtain ⟨g, hg, hgs⟩ := exists_linearMap_le_eq_of_sublinear
    (N := fun c : ι → E => upperEnvelope c α) (fun t ht c => upperEnvelope_smul_family ht c)
    upperEnvelope_add_family_le s
  refine ⟨piece g hg, sum_piece g hg, ?_⟩
  rw [← hgs]
  conv_rhs => rw [← LinearMap.sum_single_apply (φ := fun _ => E) (v := s), map_sum]
  rfl

end PositiveLinearMap
