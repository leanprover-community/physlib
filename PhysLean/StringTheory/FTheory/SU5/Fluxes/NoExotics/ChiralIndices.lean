/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.StringTheory.FTheory.SU5.Fluxes.Basic
public import Mathlib.Tactic.FinCases
/-!

# Constraints on chiral indices from the condition of no chiral exotics

## i. Overview

The chiral indices of each of the standard model representations
satisfy certain constraints if there are no chiral exotics in the spectrum.
We give prove these constraints in this file.

## ii. Key results

Each of the following results holds for each of the standard model representations,
we state them for the representation `D = (bar 3,1)_{1/3}` only:
- Each chiral index is non-negative, `FluxesFive.chiralIndicesOfD_noneg_of_noExotics`.
- The sum of the chiral indices is equal to three,
  `FluxesFive.chiralIndicesOfD_sum_eq_three_of_noExotics`.
- Each chiral index is less then or equal to three,
  `FluxesFive.chiralIndicesOfD_le_three_of_noExotics`.
- Each chiral index is `0`, `1`, `2` or `3`,
  `FluxesFive.mem_chiralIndicesOfD_mem_of_noExotics`
- The sum of a subset of the chiral indices is less then or equal to three,
  `FluxesFive.chiralIndicesOfD_subset_sum_le_three_of_noExotics`.

## iii. Table of contents

- A. Positivity of the chiral indices given no exotics
- B. Chiral indices sum to three given no exotics
- C. Each chiral index is less then or equal to three given no exotics
- D. Each chiral index is 0, 1, 2, or 3 given no exotics
- E. Sum of a subset of chiral indices is less then or equal to 3 given no exotics

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section
namespace FTheory

namespace SU5

/-!

## A. Positivity of the chiral indices given no exotics

The chiral indices of all the SM representations are non-negative if there are no chiral exotics.

-/

/-- The chiral indices of the representations `D = (bar 3,1)_{1/3}` are all non-negative if
  there are no chiral exotics in the spectrum. -/
lemma FluxesFive.chiralIndicesOfD_noneg_of_noExotics (F : FluxesFive) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfD) : 0 ≤ ci := by
  have hF1 := hF.2.2.2
  simp [numAntiChiralD] at hF1
  by_contra hn
  simp at hn
  have h1 : (Multiset.filter (fun x => x < 0) F.chiralIndicesOfD).sum < 0 := by
    let s := (Multiset.filter (fun x => x < 0) F.chiralIndicesOfD)
    apply lt_of_eq_of_lt (b := (Multiset.map id s).sum)
    · simp [s]
    apply lt_of_lt_of_eq (b := (Multiset.map (fun x => 0) s).sum)
    swap
    · simp [s]
    apply Multiset.sum_lt_sum_of_nonempty
    · simp [s]
      use ci
    · intro i hi
      simp [s] at hi
      exact hi.2
  omega

/-- The chiral indices of the representations `L = (1,2)_{-1/2}` are all non-negative if
  there are no chiral exotics in the spectrum. -/
lemma FluxesFive.chiralIndicesOfL_noneg_of_noExotics (F : FluxesFive) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfL) : 0 ≤ ci := by
  have hF1 := hF.2.1
  simp [numAntiChiralL] at hF1
  by_contra hn
  simp at hn
  have h1 : (Multiset.filter (fun x => x < 0) F.chiralIndicesOfL).sum < 0 := by
    let s := (Multiset.filter (fun x => x < 0) F.chiralIndicesOfL)
    apply lt_of_eq_of_lt (b := (Multiset.map id s).sum)
    · simp [s]
    apply lt_of_lt_of_eq (b := (Multiset.map (fun x => 0) s).sum)
    swap
    · simp [s]
    apply Multiset.sum_lt_sum_of_nonempty
    · simp [s]
      use ci
    · intro i hi
      simp [s] at hi
      exact hi.2
  omega

/-- The chiral indices of the representations `Q = (3,2)_{1/6}` are all non-negative if
  there are no chiral exotics in the spectrum. -/
lemma FluxesTen.chiralIndicesOfQ_noneg_of_noExotics (F : FluxesTen) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfQ) : 0 ≤ ci := by
  have hF1 := hF.2.1
  simp [numAntiChiralQ] at hF1
  by_contra hn
  simp at hn
  have h1 : (Multiset.filter (fun x => x < 0) F.chiralIndicesOfQ).sum < 0 := by
    let s := (Multiset.filter (fun x => x < 0) F.chiralIndicesOfQ)
    apply lt_of_eq_of_lt (b := (Multiset.map id s).sum)
    · simp [s]
    apply lt_of_lt_of_eq (b := (Multiset.map (fun x => 0) s).sum)
    swap
    · simp [s]
    apply Multiset.sum_lt_sum_of_nonempty
    · simp [s]
      use ci
    · intro i hi
      simp [s] at hi
      exact hi.2
  omega

/-- The chiral indices of the representations `U = (bar 3,1)_{-2/3}` are all non-negative if
  there are no chiral exotics in the spectrum. -/
lemma FluxesTen.chiralIndicesOfU_noneg_of_noExotics (F : FluxesTen) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfU) : 0 ≤ ci := by
  have hF1 := hF.2.2.2
  simp [numAntiChiralU] at hF1
  by_contra hn
  simp at hn
  have h1 : (Multiset.filter (fun x => x < 0) F.chiralIndicesOfU).sum < 0 := by
    let s := (Multiset.filter (fun x => x < 0) F.chiralIndicesOfU)
    apply lt_of_eq_of_lt (b := (Multiset.map id s).sum)
    · simp [s]
    apply lt_of_lt_of_eq (b := (Multiset.map (fun x => 0) s).sum)
    swap
    · simp [s]
    apply Multiset.sum_lt_sum_of_nonempty
    · simp [s]
      use ci
    · intro i hi
      simp [s] at hi
      exact hi.2
  omega

lemma FluxesTen.chiralIndicesOfE_noneg_of_noExotics (F : FluxesTen) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfE) : 0 ≤ ci := by
  have hF1 := hF.2.2.2.2.2
  simp [numAntiChiralE] at hF1
  by_contra hn
  simp at hn
  have h1 : (Multiset.filter (fun x => x < 0) F.chiralIndicesOfE).sum < 0 := by
    let s := (Multiset.filter (fun x => x < 0) F.chiralIndicesOfE)
    apply lt_of_eq_of_lt (b := (Multiset.map id s).sum)
    · simp [s]
    apply lt_of_lt_of_eq (b := (Multiset.map (fun x => 0) s).sum)
    swap
    · simp [s]
    apply Multiset.sum_lt_sum_of_nonempty
    · simp [s]
      use ci
    · intro i hi
      simp [s] at hi
      exact hi.2
  omega

/-!

## B. Chiral indices sum to three given no exotics

The sum of the chiral indices of each representation is equal to three if
there are no chiral exotics.

-/

/-- The sum of the chiral indices of the representations `D = (bar 3,1)_{1/3}` is equal
  to `3` in the presences of no exotics. -/
lemma FluxesFive.chiralIndicesOfD_sum_eq_three_of_noExotics (F : FluxesFive) (hF : NoExotics F) :
    F.chiralIndicesOfD.sum = 3 := by
  trans (Multiset.filter (fun x => 0 ≤ x) F.chiralIndicesOfD +
    (Multiset.filter (fun x => ¬ 0 ≤ x) F.chiralIndicesOfD)).sum
  · congr
    exact Eq.symm (Multiset.filter_add_not (fun x => 0 ≤ x) F.chiralIndicesOfD)
  rw [Multiset.sum_add]
  simp only [not_le]
  change F.numChiralD + F.numAntiChiralD = 3
  rw [hF.2.2.2, hF.2.2.1]
  simp

/-- The sum of the chiral indices of the representations `L = (1,2)_{-1/2}` is equal
  to `3` in the presences of no exotics. -/
lemma FluxesFive.chiralIndicesOfL_sum_eq_three_of_noExotics (F : FluxesFive) (hF : NoExotics F) :
    F.chiralIndicesOfL.sum = 3 := by
  trans (Multiset.filter (fun x => 0 ≤ x) F.chiralIndicesOfL +
    (Multiset.filter (fun x => ¬ 0 ≤ x) F.chiralIndicesOfL)).sum
  · congr
    exact Eq.symm (Multiset.filter_add_not (fun x => 0 ≤ x) F.chiralIndicesOfL)
  rw [Multiset.sum_add]
  simp only [not_le]
  change F.numChiralL + F.numAntiChiralL = 3
  rw [hF.2.1, hF.1]
  simp

/-- The sum of the chiral indices of the representations `Q = (3,2)_{1/6}` is equal
  to `3` in the presences of no exotics. -/
lemma FluxesTen.chiralIndicesOfQ_sum_eq_three_of_noExotics (F : FluxesTen) (hF : NoExotics F) :
    F.chiralIndicesOfQ.sum = 3 := by
  trans (Multiset.filter (fun x => 0 ≤ x) F.chiralIndicesOfQ +
    (Multiset.filter (fun x => ¬ 0 ≤ x) F.chiralIndicesOfQ)).sum
  · congr
    exact Eq.symm (Multiset.filter_add_not (fun x => 0 ≤ x) F.chiralIndicesOfQ)
  rw [Multiset.sum_add]
  simp only [not_le]
  change F.numChiralQ + F.numAntiChiralQ = 3
  rw [hF.2.1, hF.1]
  simp

/-- The sum of the chiral indices of the representations `U = (bar 3,1)_{-2/3}` is equal
  to `3` in the presences of no exotics. -/
lemma FluxesTen.chiralIndicesOfU_sum_eq_three_of_noExotics (F : FluxesTen) (hF : NoExotics F) :
    F.chiralIndicesOfU.sum = 3 := by
  trans (Multiset.filter (fun x => 0 ≤ x) F.chiralIndicesOfU +
    (Multiset.filter (fun x => ¬ 0 ≤ x) F.chiralIndicesOfU)).sum
  · congr
    exact Eq.symm (Multiset.filter_add_not (fun x => 0 ≤ x) F.chiralIndicesOfU)
  rw [Multiset.sum_add]
  simp only [not_le]
  change F.numChiralU + F.numAntiChiralU = 3
  rw [hF.2.2.2.1, hF.2.2.1]
  simp

/-- The sum of the chiral indices of the representations `E = (1,1)_{1}` is equal
  to `3` in the presences of no exotics. -/
lemma FluxesTen.chiralIndicesOfE_sum_eq_three_of_noExotics (F : FluxesTen) (hF : NoExotics F) :
    F.chiralIndicesOfE.sum = 3 := by
  trans (Multiset.filter (fun x => 0 ≤ x) F.chiralIndicesOfE +
    (Multiset.filter (fun x => ¬ 0 ≤ x) F.chiralIndicesOfE)).sum
  · congr
    exact Eq.symm (Multiset.filter_add_not (fun x => 0 ≤ x) F.chiralIndicesOfE)
  rw [Multiset.sum_add]
  simp only [not_le]
  change F.numChiralE + F.numAntiChiralE = 3
  rw [hF.2.2.2.2.1, hF.2.2.2.2.2]
  simp

/-!

## C. Each chiral index is less then or equal to three given no exotics

-/

/-- The chiral indices of the representation `D = (bar 3,1)_{1/3}` are less then
  or equal to `3`. -/
lemma FluxesFive.chiralIndicesOfD_le_three_of_noExotics (F : FluxesFive) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfD) : ci ≤ 3 := by
  by_contra hn
  simp at hn
  let s := (Multiset.filter (fun x => 3 < x) F.chiralIndicesOfD)
  let s' := (Multiset.filter (fun x => x ≤ 3) F.chiralIndicesOfD)
  have hmems : 0 < s.card := by
    refine Multiset.card_pos_iff_exists_mem.mpr ?_
    use ci
    simp [s]
    exact ⟨hci, hn⟩
  have hsum : s.card • 4 ≤ s.sum := by
    apply Multiset.card_nsmul_le_sum
    simp [s]
    omega
  have hsumle4 : 4 ≤ s.sum := by
    simp at hsum
    omega
  have hs'sum : 0 ≤ s'.sum := by
    apply Multiset.sum_nonneg
    simp [s']
    exact fun i hi _ => chiralIndicesOfD_noneg_of_noExotics F hF i hi
  have hsum' : s.sum + s'.sum = F.chiralIndicesOfD.sum := by
    rw [← Multiset.sum_add]
    congr
    conv_rhs => rw [← Multiset.filter_add_not (fun x => 3 < x) F.chiralIndicesOfD]
    simp [s, s']
  rw [F.chiralIndicesOfD_sum_eq_three_of_noExotics hF] at hsum'
  omega

/-- The chiral indices of the representation `L = (1,2)_{-1/2}` are less then
  or equal to `3`. -/
lemma FluxesFive.chiralIndicesOfL_le_three_of_noExotics (F : FluxesFive) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfL) : ci ≤ 3 := by
  by_contra hn
  simp at hn
  let s := (Multiset.filter (fun x => 3 < x) F.chiralIndicesOfL)
  let s' := (Multiset.filter (fun x => x ≤ 3) F.chiralIndicesOfL)
  have hmems : 0 < s.card := by
    refine Multiset.card_pos_iff_exists_mem.mpr ?_
    use ci
    simp [s]
    exact ⟨hci, hn⟩
  have hsum : s.card • 4 ≤ s.sum := by
    apply Multiset.card_nsmul_le_sum
    simp [s]
    omega
  have hsumle4 : 4 ≤ s.sum := by
    simp at hsum
    omega
  have hs'sum : 0 ≤ s'.sum := by
    apply Multiset.sum_nonneg
    simp [s']
    exact fun i hi _ => chiralIndicesOfL_noneg_of_noExotics F hF i hi
  have hsum' : s.sum + s'.sum = F.chiralIndicesOfL.sum := by
    rw [← Multiset.sum_add]
    congr
    conv_rhs => rw [← Multiset.filter_add_not (fun x => 3 < x) F.chiralIndicesOfL]
    simp [s, s']
  rw [F.chiralIndicesOfL_sum_eq_three_of_noExotics hF] at hsum'
  omega

/-- The chiral indices of the representation `Q = (3,2)_{1/6}` are less then
  or equal to `3`. -/
lemma FluxesTen.chiralIndicesOfQ_le_three_of_noExotics (F : FluxesTen) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfQ) : ci ≤ 3 := by
  by_contra hn
  simp at hn
  let s := (Multiset.filter (fun x => 3 < x) F.chiralIndicesOfQ)
  let s' := (Multiset.filter (fun x => x ≤ 3) F.chiralIndicesOfQ)
  have hmems : 0 < s.card := by
    refine Multiset.card_pos_iff_exists_mem.mpr ?_
    use ci
    simp [s]
    exact ⟨hci, hn⟩
  have hsum : s.card • 4 ≤ s.sum := by
    apply Multiset.card_nsmul_le_sum
    simp [s]
    omega
  have hsumle4 : 4 ≤ s.sum := by
    simp at hsum
    omega
  have hs'sum : 0 ≤ s'.sum := by
    apply Multiset.sum_nonneg
    simp [s']
    exact fun i hi _ => chiralIndicesOfQ_noneg_of_noExotics F hF i hi
  have hsum' : s.sum + s'.sum = F.chiralIndicesOfQ.sum := by
    rw [← Multiset.sum_add]
    congr
    conv_rhs => rw [← Multiset.filter_add_not (fun x => 3 < x) F.chiralIndicesOfQ]
    simp [s, s']
  rw [F.chiralIndicesOfQ_sum_eq_three_of_noExotics hF] at hsum'
  omega

/-- The chiral indices of the representation `U = (bar 3,1)_{-2/3}` are less then
  or equal to `3`. -/
lemma FluxesTen.chiralIndicesOfU_le_three_of_noExotics (F : FluxesTen) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfU) : ci ≤ 3 := by
  by_contra hn
  simp at hn
  let s := (Multiset.filter (fun x => 3 < x) F.chiralIndicesOfU)
  let s' := (Multiset.filter (fun x => x ≤ 3) F.chiralIndicesOfU)
  have hmems : 0 < s.card := by
    refine Multiset.card_pos_iff_exists_mem.mpr ?_
    use ci
    simp [s]
    exact ⟨hci, hn⟩
  have hsum : s.card • 4 ≤ s.sum := by
    apply Multiset.card_nsmul_le_sum
    simp [s]
    omega
  have hsumle4 : 4 ≤ s.sum := by
    simp at hsum
    omega
  have hs'sum : 0 ≤ s'.sum := by
    apply Multiset.sum_nonneg
    simp [s']
    exact fun i hi _ => chiralIndicesOfU_noneg_of_noExotics F hF i hi
  have hsum' : s.sum + s'.sum = F.chiralIndicesOfU.sum := by
    rw [← Multiset.sum_add]
    congr
    conv_rhs => rw [← Multiset.filter_add_not (fun x => 3 < x) F.chiralIndicesOfU]
    simp [s, s']
  rw [F.chiralIndicesOfU_sum_eq_three_of_noExotics hF] at hsum'
  omega

/-- The chiral indices of the representation `E = (1,1)_{1}` are less then
  or equal to `3`. -/
lemma FluxesTen.chiralIndicesOfE_le_three_of_noExotics (F : FluxesTen) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfE) : ci ≤ 3 := by
  by_contra hn
  simp at hn
  let s := (Multiset.filter (fun x => 3 < x) F.chiralIndicesOfE)
  let s' := (Multiset.filter (fun x => x ≤ 3) F.chiralIndicesOfE)
  have hmems : 0 < s.card := by
    refine Multiset.card_pos_iff_exists_mem.mpr ?_
    use ci
    simp [s]
    exact ⟨hci, hn⟩
  have hsum : s.card • 4 ≤ s.sum := by
    apply Multiset.card_nsmul_le_sum
    simp [s]
    omega
  have hsumle4 : 4 ≤ s.sum := by
    simp at hsum
    omega
  have hs'sum : 0 ≤ s'.sum := by
    apply Multiset.sum_nonneg
    simp [s']
    exact fun i hi _ => chiralIndicesOfE_noneg_of_noExotics F hF i hi
  have hsum' : s.sum + s'.sum = F.chiralIndicesOfE.sum := by
    rw [← Multiset.sum_add]
    congr
    conv_rhs => rw [← Multiset.filter_add_not (fun x => 3 < x) F.chiralIndicesOfE]
    simp [s, s']
  rw [F.chiralIndicesOfE_sum_eq_three_of_noExotics hF] at hsum'
  omega

/-!

## D. Each chiral index is 0, 1, 2, or 3 given no exotics

-/

lemma FluxesFive.mem_chiralIndicesOfD_mem_of_noExotics (F : FluxesFive)
    (hF : NoExotics F) (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfD) :
    ci ∈ ({0, 1, 2, 3} : Finset ℤ) := by
  have h0 := F.chiralIndicesOfD_le_three_of_noExotics hF ci hci
  have h1 := chiralIndicesOfD_noneg_of_noExotics F hF ci hci
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

lemma FluxesFive.mem_chiralIndicesOfL_mem_of_noExotics (F : FluxesFive)
    (hF : NoExotics F) (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfL) :
    ci ∈ ({0, 1, 2, 3} : Finset ℤ) := by
  have h0 := F.chiralIndicesOfL_le_three_of_noExotics hF ci hci
  have h1 := chiralIndicesOfL_noneg_of_noExotics F hF ci hci
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

lemma FluxesTen.mem_chiralIndicesOfQ_mem_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfQ) :
    ci ∈ ({0, 1, 2, 3} : Finset ℤ) := by
  have h0 := F.chiralIndicesOfQ_le_three_of_noExotics hF ci hci
  have h1 := chiralIndicesOfQ_noneg_of_noExotics F hF ci hci
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

lemma FluxesTen.mem_chiralIndicesOfU_mem_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfU) :
    ci ∈ ({0, 1, 2, 3} : Finset ℤ) := by
  have h0 := F.chiralIndicesOfU_le_three_of_noExotics hF ci hci
  have h1 := chiralIndicesOfU_noneg_of_noExotics F hF ci hci
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

lemma FluxesTen.mem_chiralIndicesOfE_mem_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfE) :
    ci ∈ ({0, 1, 2, 3} : Finset ℤ) := by
  have h0 := F.chiralIndicesOfE_le_three_of_noExotics hF ci hci
  have h1 := chiralIndicesOfE_noneg_of_noExotics F hF ci hci
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-!

## E. Sum of a subset of chiral indices is less then or equal to 3 given no exotics

-/

lemma FluxesFive.chiralIndicesOfD_subset_sum_le_three_of_noExotics (F : FluxesFive)
    (hF : NoExotics F) (S : Multiset Fluxes)
    (hSle : S ≤ F) : (S.map (fun x => x.1)).sum ≤ 3 := by
  have hpos : 0 ≤ ((F - S).map (fun x => x.1)).sum := by
    refine Multiset.sum_nonneg (fun x hx => ?_)
    simp at hx
    obtain ⟨f, h, rfl⟩ := hx
    have hl : f ∈ F := by
      apply Multiset.mem_of_subset (t := F) at h
      exact h
      refine Multiset.subset_of_le ?_
      rw [@Multiset.sub_le_iff_le_add']
      simp
    exact chiralIndicesOfD_noneg_of_noExotics F hF f.M (Multiset.mem_map.mpr ⟨f, hl, rfl⟩)
  rw [← F.chiralIndicesOfD_sum_eq_three_of_noExotics hF,
    chiralIndicesOfD, ← add_tsub_cancel_of_le hSle, Multiset.map_add, Multiset.sum_add]
  omega

lemma FluxesFive.chiralIndicesOfL_subset_sum_le_three_of_noExotics (F : FluxesFive)
    (hF : NoExotics F) (S : Multiset Fluxes)
    (hSle : S ≤ F) : (S.map (fun x => (x.1 + x.2))).sum ≤ 3 := by
  have hpos : 0 ≤ ((F - S).map (fun x => (x.1 + x.2))).sum := by
    refine Multiset.sum_nonneg (fun x hx => ?_)
    simp at hx
    obtain ⟨f, h, rfl⟩ := hx
    exact chiralIndicesOfL_noneg_of_noExotics F hF (f.M + f.N)
      (Multiset.mem_map.mpr ⟨f, Multiset.mem_of_subset (Multiset.subset_of_le (by simp)) h, rfl⟩)
  rw [← F.chiralIndicesOfL_sum_eq_three_of_noExotics hF,
    chiralIndicesOfL, ← add_tsub_cancel_of_le hSle, Multiset.map_add, Multiset.sum_add]
  omega

lemma FluxesTen.chiralIndicesOfQ_subset_sum_le_three_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) (S : Multiset Fluxes)
    (hSle : S ≤ F) : (S.map (fun x => x.1)).sum ≤ 3 := by
  have hpos : 0 ≤ ((F - S).map (fun x => x.1)).sum := by
    refine Multiset.sum_nonneg (fun x hx => ?_)
    simp at hx
    obtain ⟨f, h, rfl⟩ := hx
    have hl : f ∈ F := by
      apply Multiset.mem_of_subset (t := F) at h
      exact h
      refine Multiset.subset_of_le ?_
      rw [@Multiset.sub_le_iff_le_add']
      simp
    exact chiralIndicesOfQ_noneg_of_noExotics F hF f.M (Multiset.mem_map.mpr ⟨f, hl, rfl⟩)
  rw [← F.chiralIndicesOfQ_sum_eq_three_of_noExotics hF,
    chiralIndicesOfQ, ← add_tsub_cancel_of_le hSle, Multiset.map_add, Multiset.sum_add]
  omega

lemma FluxesTen.chiralIndicesOfU_subset_sum_le_three_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) (S : Multiset Fluxes)
    (hSle : S ≤ F) : (S.map (fun x => (x.1 - x.2))).sum ≤ 3 := by
  have hpos : 0 ≤ ((F - S).map (fun x => (x.1 - x.2))).sum := by
    refine Multiset.sum_nonneg (fun x hx => ?_)
    simp at hx
    obtain ⟨f, h, rfl⟩ := hx
    have hl : f ∈ F := Multiset.mem_of_subset (Multiset.subset_of_le (by simp)) h
    exact chiralIndicesOfU_noneg_of_noExotics F hF (f.M - f.N) (Multiset.mem_map.mpr ⟨f, hl, rfl⟩)
  rw [← F.chiralIndicesOfU_sum_eq_three_of_noExotics hF,
    chiralIndicesOfU, ← add_tsub_cancel_of_le hSle, Multiset.map_add, Multiset.sum_add]
  omega

lemma FluxesTen.chiralIndicesOfE_subset_sum_le_three_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) (S : Multiset Fluxes)
    (hSle : S ≤ F) : (S.map (fun x => (x.1 + x.2))).sum ≤ 3 := by
  have hpos : 0 ≤ ((F - S).map (fun x => (x.1 + x.2))).sum := by
    refine Multiset.sum_nonneg (fun x hx => ?_)
    simp at hx
    obtain ⟨f, h, rfl⟩ := hx
    have hl : f ∈ F := Multiset.mem_of_subset (Multiset.subset_of_le (by simp)) h
    exact chiralIndicesOfE_noneg_of_noExotics F hF (f.M + f.N) (Multiset.mem_map.mpr ⟨f, hl, rfl⟩)
  rw [← F.chiralIndicesOfE_sum_eq_three_of_noExotics hF, chiralIndicesOfE,
    ← add_tsub_cancel_of_le hSle, Multiset.map_add, Multiset.sum_add]
  omega

end SU5

end FTheory
