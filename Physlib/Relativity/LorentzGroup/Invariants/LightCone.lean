/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.Fin
public import Physlib.Relativity.LorentzGroup.Invariants.Basic
/-!
# The light-cone basis of a boost axis over the integers and the rationals

`lightConeCoeff` and `lightConeCoeffInv` of `LightConeDeriv` change a spacetime index into the
light-cone basis of a spatial axis `i`: the two directions `D₀ - Dᵢ` and `D₀ + Dᵢ` of the plane
the boost along `i` moves, and the two transverse directions. Their entries are `0`, `±1` and
`±1/2`, so both matrices have integer or rational mirrors, and the rank-two and rank-four
classifications compute with a mirror rather than with `ℂ`: the kernel evaluates `ℤ` and `ℚ`
and does not evaluate `ℂ`. The Weyl classifications carry their own weight bases and use none
of this. This file holds the mirrors and what is proved about them at an arbitrary number of
indices; the rank-specific files contract them against as many slots as they have.

The change of basis one way is `lightConeCoeffZ`, an exact integer copy. The other way needs
the halves: `lightConeCoeffInvQ` keeps them, and `lightConeCoeffInvZ` clears them, so it is
twice the true inverse and a contraction over `n` slots carries a factor `2 ^ n` that the
rank-specific file divides out. That is the only normalization in play, and
`coe_lightConeCoeffInvZ_eq_two_mul` and `coe_lightConeCoeffInvZ` record it against `ℂ` and `ℚ`.

Three groupings of the four light-cone directions are used. `InBoostPlane` separates the two
directions of weight `±2` from the two transverse ones, one index at a time. `sectorIndex`
sorts the four into the three sectors of distinct boost weight, raising, lowering and
transverse, `sectorWeight` records those weights, and `slotTransition` and `slotTransitionZ`
sum one slot of the change of basis over a sector. `slotZ` keeps the four directions apart
instead, and `transitionZ` composes it over `n` slots into `2 ^ n` times the map keeping the
light-cone components of total weight `m`; `transitionZ_eq_sum` unfolds that recursion into a
single sum over the multi-indices of that weight.
-/

@[expose] public section

namespace Lorentz

open Matrix MatrixGroups SL2C

namespace Invariants

/-!

## A. The change of basis over the integers and the rationals

-/

/-- The four light-cone directions of axis `i`, as integers. -/
def lightConeCoeffZ (i : Fin 3) (κ : Fin 4) (μ : Fin 1 ⊕ Fin 3) : ℤ :=
  if κ = 0 then (if μ = Sum.inl 0 then 1 else if μ = Sum.inr i then -1 else 0)
  else if κ = 1 then (if μ = Sum.inl 0 then 1 else if μ = Sum.inr i then 1 else 0)
  else if κ = 2 then (if μ = Sum.inr (i + 1) then 1 else 0)
  else (if μ = Sum.inr (i + 2) then 1 else 0)

/-- The integer copy casts to `lightConeCoeff`. -/
lemma coe_lightConeCoeffZ (i : Fin 3) (κ : Fin 4) (μ : Fin 1 ⊕ Fin 3) :
    ((lightConeCoeffZ i κ μ : ℤ) : ℂ) = lightConeCoeff i κ μ := by
  rw [lightConeCoeffZ, lightConeCoeff]
  split_ifs <;> norm_num

/-- Twice the coordinate directions in the light-cone basis, the `2` clearing the halves. -/
def lightConeCoeffInvZ (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) : ℤ :=
  if μ = Sum.inl 0 then (if κ = 0 then 1 else if κ = 1 then 1 else 0)
  else if μ = Sum.inr i then (if κ = 0 then -1 else if κ = 1 then 1 else 0)
  else if μ = Sum.inr (i + 1) then (if κ = 2 then 2 else 0)
  else (if κ = 3 then 2 else 0)

/-- The integer copy is exactly twice `lightConeCoeffInv`. -/
lemma coe_lightConeCoeffInvZ_eq_two_mul (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) :
    ((lightConeCoeffInvZ i μ κ : ℤ) : ℂ) = 2 * lightConeCoeffInv i μ κ := by
  rw [lightConeCoeffInvZ, lightConeCoeffInv]
  split_ifs <;> norm_num

/-- The inverse light-cone coefficients over `ℚ`, with the halves kept as halves. -/
def lightConeCoeffInvQ (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) : ℚ :=
  if μ = Sum.inl 0 then (if κ = 0 then 2⁻¹ else if κ = 1 then 2⁻¹ else 0)
  else if μ = Sum.inr i then (if κ = 0 then -2⁻¹ else if κ = 1 then 2⁻¹ else 0)
  else if μ = Sum.inr (i + 1) then (if κ = 2 then 1 else 0)
  else (if κ = 3 then 1 else 0)

/-- The rational mirror casts to the inverse light-cone coefficients. -/
lemma coe_lightConeCoeffInvQ (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) :
    ((lightConeCoeffInvQ i μ κ : ℚ) : ℂ) = lightConeCoeffInv i μ κ := by
  rw [lightConeCoeffInvQ, lightConeCoeffInv]
  split_ifs <;> norm_num

/-- The integer mirror is twice the rational one. -/
lemma coe_lightConeCoeffInvZ (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) (κ : Fin 4) :
    ((lightConeCoeffInvZ i μ κ : ℤ) : ℚ) = 2 * lightConeCoeffInvQ i μ κ := by
  rw [lightConeCoeffInvZ, lightConeCoeffInvQ]
  split_ifs <;> norm_num

/-!

## B. The boost plane

The boost along axis `i` moves time and the axis and fixes the two transverse directions, so
the light-cone directions of weight `±2` are supported in the first pair and the two of weight
`0` in the second. Either half of that statement kills half of `lightConeCoeffInvZ`.

-/

/-- The boost plane of axis `i`: time and the axis, the two directions the boost moves. -/
def InBoostPlane (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) : Prop := μ = Sum.inl 0 ∨ μ = Sum.inr i

instance (i : Fin 3) (μ : Fin 1 ⊕ Fin 3) : Decidable (InBoostPlane i μ) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- A direction in the boost plane has no transverse light-cone components. -/
lemma lightConeCoeffInvZ_eq_zero_of_inBoostPlane {i : Fin 3} {μ : Fin 1 ⊕ Fin 3}
    (hμ : InBoostPlane i μ) {κ : Fin 4} (hκ : κ = 2 ∨ κ = 3) :
    lightConeCoeffInvZ i μ κ = 0 := by
  rcases hμ with rfl | rfl <;> rcases hκ with rfl | rfl <;> simp [lightConeCoeffInvZ]

/-- A transverse direction has no light-cone components in the boost plane. -/
lemma lightConeCoeffInvZ_eq_zero_of_not_inBoostPlane {i : Fin 3} {μ : Fin 1 ⊕ Fin 3}
    (hμ : ¬InBoostPlane i μ) {κ : Fin 4} (hκ : κ = 0 ∨ κ = 1) :
    lightConeCoeffInvZ i μ κ = 0 := by
  simp only [InBoostPlane, not_or] at hμ
  rcases hκ with rfl | rfl <;> simp [lightConeCoeffInvZ, hμ.1, hμ.2]

/-!

## C. The three sectors of the light-cone directions

The four light-cone directions carry only three distinct boost weights, `2`, `-2` and `0` twice,
and a sum over multi-indices of a given total weight only sees that much: `sectorIndex` sorts
the directions accordingly, and summing one slot of the change of basis over a sector gives
`slotTransition` over `ℚ` and `slotTransitionZ` over `ℤ`, again twice as large.

-/

/-- The sector of each light-cone direction: `0` raising, `1` lowering, `2` and `3` transverse. -/
def sectorIndex : Fin 4 → Fin 3 := ![0, 1, 2, 2]

/-- The boost weight of each sector: `2` raising, `-2` lowering, `0` transverse. -/
def sectorWeight : Fin 3 → ℤ := ![2, -2, 0]

/-- The light-cone weight of a direction is the weight of its sector. -/
lemma lightConeWeight_eq_sectorWeight (κ : Fin 4) :
    lightConeWeight κ = sectorWeight (sectorIndex κ) := by
  fin_cases κ <;> rfl

/-- The slot factor summed over the directions of one sector, over `ℚ`. -/
def slotTransition (i : Fin 3) (κ : Fin 3) (μ ν : Fin 1 ⊕ Fin 3) : ℚ :=
  ∑ κ' ∈ Finset.univ.filter (fun κ' : Fin 4 => sectorIndex κ' = κ),
    lightConeCoeffInvQ i μ κ' * (lightConeCoeffZ i κ' ν : ℚ)

/-- The slot factor summed over one sector, in closed form over `ℤ`: on the boost plane the
  raising sector carries `[[1, -1], [-1, 1]]` and the lowering sector the all-ones matrix, and
  the transverse sector is twice the identity on the transverse directions. -/
def slotTransitionZ (i : Fin 3) (κ : Fin 3) (μ ν : Fin 1 ⊕ Fin 3) : ℤ :=
  if κ = 2 then (if μ = ν ∧ μ ≠ Sum.inl 0 ∧ μ ≠ Sum.inr i then 2 else 0)
  else if (μ = Sum.inl 0 ∨ μ = Sum.inr i) ∧ (ν = Sum.inl 0 ∨ ν = Sum.inr i) then
    (if κ = 0 then (if μ = Sum.inr i then -1 else 1) * (if ν = Sum.inr i then -1 else 1)
    else 1)
  else 0

/-- The closed form is the sector sum of the slot factors. -/
lemma slotTransitionZ_eq_sum (i : Fin 3) (κ : Fin 3) (μ ν : Fin 1 ⊕ Fin 3) :
    slotTransitionZ i κ μ ν
      = ∑ κ' ∈ Finset.univ.filter (fun κ' : Fin 4 => sectorIndex κ' = κ),
        lightConeCoeffInvZ i μ κ' * lightConeCoeffZ i κ' ν := by
  rw [Finset.sum_filter, Fin.sum_univ_four]
  rcases μ with a | j <;> rcases ν with b | l
  · simp only [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]
    fin_cases κ <;> simp [slotTransitionZ, lightConeCoeffInvZ, lightConeCoeffZ, sectorIndex]
  · simp only [Fin.fin_one_eq_zero a]
    fin_cases κ <;> fin_cases i <;> fin_cases l <;>
      simp [slotTransitionZ, lightConeCoeffInvZ, lightConeCoeffZ, sectorIndex]
  · simp only [Fin.fin_one_eq_zero b]
    fin_cases κ <;> fin_cases i <;> fin_cases j <;>
      simp [slotTransitionZ, lightConeCoeffInvZ, lightConeCoeffZ, sectorIndex]
  · fin_cases κ <;> fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp [slotTransitionZ, lightConeCoeffInvZ, lightConeCoeffZ, sectorIndex]

/-- The integer sector matrix is twice the rational one, which is what the two names promise. -/
lemma coe_slotTransitionZ (i : Fin 3) (κ : Fin 3) (μ ν : Fin 1 ⊕ Fin 3) :
    ((slotTransitionZ i κ μ ν : ℤ) : ℚ) = 2 * slotTransition i κ μ ν := by
  rw [slotTransitionZ_eq_sum, slotTransition, Finset.mul_sum]
  push_cast
  exact Finset.sum_congr rfl fun κ' _ => by rw [coe_lightConeCoeffInvZ]; ring

/-!

## D. The weight-keeping transition over any number of slots

Keeping the four directions apart instead of their three sectors, one slot of the change of
basis is `slotZ`, and composing it over `n` slots while tracking the weight left to distribute
gives `transitionZ`. The recursion follows B: a slot whose direction lies in the boost plane
takes weight `2` or `-2` and leaves `m - 2` or `m + 2`, and a transverse slot takes either
direction of weight `0`, which is why those two are added, and leaves `m`.

Unfolding the recursion into a single sum splits into two independent steps. The case split of
the recursion is the boost-plane support argument of B and nothing else: once it is resolved,
one slot is a plain sum over the four directions, each taking its own weight out of `m`
(`transitionZ_succ`). What is left has no light-cone content at all, the peeling of the first
slot off a weight-constrained sum over tuples, which is `Physlib.Fin.sum_filter_weight_succ`.
`transitionZ_eq_sum` is the induction that composes them.

-/

/-- One slot's factor: twice the coefficient of `κ` in `μ`, times that of `ν` in `κ`. -/
def slotZ (i : Fin 3) (κ : Fin 4) (μ ν : Fin 1 ⊕ Fin 3) : ℤ :=
  lightConeCoeffInvZ i μ κ * lightConeCoeffZ i κ ν

/-- Two to the number of slots times the entry, at `d` and `e`, of the map keeping the light-cone
  components of total weight `m` along axis `i`; the factor is the one `lightConeCoeffInvZ`
  carries, one per slot. A slot of `d` in the boost plane takes weight `2` or `-2`, leaving
  `m - 2` or `m + 2`; a transverse slot takes weight `0` and leaves `m`. -/
def transitionZ (i : Fin 3) : {n : ℕ} → (d e : Fin n → Fin 1 ⊕ Fin 3) → ℤ → ℤ
  | 0, _, _, m => if m = 0 then 1 else 0
  | _ + 1, d, e, m =>
    if InBoostPlane i (d 0) then
      slotZ i 0 (d 0) (e 0) * transitionZ i (Fin.tail d) (Fin.tail e) (m - 2)
        + slotZ i 1 (d 0) (e 0) * transitionZ i (Fin.tail d) (Fin.tail e) (m + 2)
    else (slotZ i 2 (d 0) (e 0) + slotZ i 3 (d 0) (e 0))
      * transitionZ i (Fin.tail d) (Fin.tail e) m

/-- One slot of the transition, with the case split of the recursion resolved: the first slot
  runs over all four light-cone directions, each taking its own weight out of `m`. The two
  directions of the boost plane drop out of a transverse slot and the two transverse ones drop
  out of a slot in the boost plane, which is what the two branches of `transitionZ` record. -/
lemma transitionZ_succ (i : Fin 3) {n : ℕ} (d e : Fin (n + 1) → Fin 1 ⊕ Fin 3) (m : ℤ) :
    transitionZ i d e m
      = ∑ κ : Fin 4, slotZ i κ (d 0) (e 0)
          * transitionZ i (Fin.tail d) (Fin.tail e) (m - lightConeWeight κ) := by
  rw [Fin.sum_univ_four, transitionZ]
  simp only [show lightConeWeight 0 = 2 from rfl, show lightConeWeight 1 = -2 from rfl,
    show lightConeWeight 2 = 0 from rfl, show lightConeWeight 3 = 0 from rfl,
    sub_neg_eq_add, sub_zero]
  by_cases h : InBoostPlane i (d 0)
  · rw [ite_eq_left h]
    simp [slotZ, lightConeCoeffInvZ_eq_zero_of_inBoostPlane h]
  · rw [ite_eq_right h]
    simp [slotZ, lightConeCoeffInvZ_eq_zero_of_not_inBoostPlane h]
    ring

/-- The recursion unfolded, as a sum over the multi-indices of total weight `m`. -/
lemma transitionZ_eq_sum (i : Fin 3) :
    ∀ {n : ℕ} (d e : Fin n → Fin 1 ⊕ Fin 3) (m : ℤ),
    transitionZ i d e m
      = ∑ κ ∈ Finset.univ.filter
          (fun κ : Fin n → Fin 4 => (∑ s, lightConeWeight (κ s)) = m),
        ∏ s, slotZ i (κ s) (d s) (e s)
  | 0, d, e, m => by
    rw [Finset.sum_filter, Fintype.sum_unique]
    simp [transitionZ, eq_comm]
  | n + 1, d, e, m => by
    rw [transitionZ_succ,
      Physlib.Fin.sum_filter_weight_succ lightConeWeight fun s κ => slotZ i κ (d s) (e s)]
    refine Finset.sum_congr rfl fun κ₀ _ => ?_
    rw [transitionZ_eq_sum i (Fin.tail d) (Fin.tail e)]
    rfl

end Invariants

end Lorentz
