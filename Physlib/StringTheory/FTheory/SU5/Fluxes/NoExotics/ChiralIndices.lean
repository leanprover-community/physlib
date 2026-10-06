/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.StringTheory.FTheory.SU5.Fluxes.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Multiset.OrderedMonoid
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

* None.
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
  by_contra hn
  simp only [not_le] at hn
  have hF1 := hF.2.2.2
  simp [numAntiChiralD] at hF1
  have h1 := Multiset.sum_le_card_nsmul
    (Multiset.filter (fun x => x < 0) F.chiralIndicesOfD) (-1)
    (fun x hx => by
      have := (Multiset.mem_filter.mp hx).2
      omega)
  rw [nsmul_eq_mul] at h1
  have h2 : 0 < Multiset.card (Multiset.filter (fun x => x < 0) F.chiralIndicesOfD) :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨ci, Multiset.mem_filter.mpr ⟨hci, hn⟩⟩
  omega

/-- The chiral indices of the representations `L = (1,2)_{-1/2}` are all non-negative if
  there are no chiral exotics in the spectrum. -/
lemma FluxesFive.chiralIndicesOfL_noneg_of_noExotics (F : FluxesFive) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfL) : 0 ≤ ci := by
  by_contra hn
  simp only [not_le] at hn
  have hF1 := hF.2.1
  simp [numAntiChiralL] at hF1
  have h1 := Multiset.sum_le_card_nsmul
    (Multiset.filter (fun x => x < 0) F.chiralIndicesOfL) (-1)
    (fun x hx => by
      have := (Multiset.mem_filter.mp hx).2
      omega)
  rw [nsmul_eq_mul] at h1
  have h2 : 0 < Multiset.card (Multiset.filter (fun x => x < 0) F.chiralIndicesOfL) :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨ci, Multiset.mem_filter.mpr ⟨hci, hn⟩⟩
  omega

/-- The chiral indices of the representations `Q = (3,2)_{1/6}` are all non-negative if
  there are no chiral exotics in the spectrum. -/
lemma FluxesTen.chiralIndicesOfQ_noneg_of_noExotics (F : FluxesTen) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfQ) : 0 ≤ ci := by
  by_contra hn
  simp only [not_le] at hn
  have hF1 := hF.2.1
  simp [numAntiChiralQ] at hF1
  have h1 := Multiset.sum_le_card_nsmul
    (Multiset.filter (fun x => x < 0) F.chiralIndicesOfQ) (-1)
    (fun x hx => by
      have := (Multiset.mem_filter.mp hx).2
      omega)
  rw [nsmul_eq_mul] at h1
  have h2 : 0 < Multiset.card (Multiset.filter (fun x => x < 0) F.chiralIndicesOfQ) :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨ci, Multiset.mem_filter.mpr ⟨hci, hn⟩⟩
  omega

/-- The chiral indices of the representations `U = (bar 3,1)_{-2/3}` are all non-negative if
  there are no chiral exotics in the spectrum. -/
lemma FluxesTen.chiralIndicesOfU_noneg_of_noExotics (F : FluxesTen) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfU) : 0 ≤ ci := by
  by_contra hn
  simp only [not_le] at hn
  have hF1 := hF.2.2.2
  simp [numAntiChiralU] at hF1
  have h1 := Multiset.sum_le_card_nsmul
    (Multiset.filter (fun x => x < 0) F.chiralIndicesOfU) (-1)
    (fun x hx => by
      have := (Multiset.mem_filter.mp hx).2
      omega)
  rw [nsmul_eq_mul] at h1
  have h2 : 0 < Multiset.card (Multiset.filter (fun x => x < 0) F.chiralIndicesOfU) :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨ci, Multiset.mem_filter.mpr ⟨hci, hn⟩⟩
  omega

lemma FluxesTen.chiralIndicesOfE_noneg_of_noExotics (F : FluxesTen) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfE) : 0 ≤ ci := by
  by_contra hn
  simp only [not_le] at hn
  have hF1 := hF.2.2.2.2.2
  simp [numAntiChiralE] at hF1
  have h1 := Multiset.sum_le_card_nsmul
    (Multiset.filter (fun x => x < 0) F.chiralIndicesOfE) (-1)
    (fun x hx => by
      have := (Multiset.mem_filter.mp hx).2
      omega)
  rw [nsmul_eq_mul] at h1
  have h2 : 0 < Multiset.card (Multiset.filter (fun x => x < 0) F.chiralIndicesOfE) :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨ci, Multiset.mem_filter.mpr ⟨hci, hn⟩⟩
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
  have h := F.numChiralD_eq_sum_sub_numAntiChiralD
  rw [hF.2.2.2, hF.2.2.1] at h
  omega

/-- The sum of the chiral indices of the representations `L = (1,2)_{-1/2}` is equal
  to `3` in the presences of no exotics. -/
lemma FluxesFive.chiralIndicesOfL_sum_eq_three_of_noExotics (F : FluxesFive) (hF : NoExotics F) :
    F.chiralIndicesOfL.sum = 3 := by
  have h := F.numChiralL_eq_sum_sub_numAntiChiralL
  rw [hF.2.1, hF.1] at h
  omega

/-- The sum of the chiral indices of the representations `Q = (3,2)_{1/6}` is equal
  to `3` in the presences of no exotics. -/
lemma FluxesTen.chiralIndicesOfQ_sum_eq_three_of_noExotics (F : FluxesTen) (hF : NoExotics F) :
    F.chiralIndicesOfQ.sum = 3 := by
  have h := F.numChiralQ_eq_sum_sub_numAntiChiralQ
  rw [hF.2.1, hF.1] at h
  omega

/-- The sum of the chiral indices of the representations `U = (bar 3,1)_{-2/3}` is equal
  to `3` in the presences of no exotics. -/
lemma FluxesTen.chiralIndicesOfU_sum_eq_three_of_noExotics (F : FluxesTen) (hF : NoExotics F) :
    F.chiralIndicesOfU.sum = 3 := by
  have h := F.numChiralU_eq_sum_sub_numAntiChiralU
  rw [hF.2.2.2.1, hF.2.2.1] at h
  omega

/-- The sum of the chiral indices of the representations `E = (1,1)_{1}` is equal
  to `3` in the presences of no exotics. -/
lemma FluxesTen.chiralIndicesOfE_sum_eq_three_of_noExotics (F : FluxesTen) (hF : NoExotics F) :
    F.chiralIndicesOfE.sum = 3 := by
  have h := F.numChiralE_eq_sum_sub_numAntiChiralE
  rw [hF.2.2.2.2.1, hF.2.2.2.2.2] at h
  omega

/-!

## C. Each chiral index is less then or equal to three given no exotics

-/

/-- The chiral indices of the representation `D = (bar 3,1)_{1/3}` are less then
  or equal to `3`. -/
lemma FluxesFive.chiralIndicesOfD_le_three_of_noExotics (F : FluxesFive) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfD) : ci ≤ 3 := by
  have hle := Multiset.single_le_sum
    (fun x hx => chiralIndicesOfD_noneg_of_noExotics F hF x hx) ci hci
  rwa [F.chiralIndicesOfD_sum_eq_three_of_noExotics hF] at hle

/-- The chiral indices of the representation `L = (1,2)_{-1/2}` are less then
  or equal to `3`. -/
lemma FluxesFive.chiralIndicesOfL_le_three_of_noExotics (F : FluxesFive) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfL) : ci ≤ 3 := by
  have hle := Multiset.single_le_sum
    (fun x hx => chiralIndicesOfL_noneg_of_noExotics F hF x hx) ci hci
  rwa [F.chiralIndicesOfL_sum_eq_three_of_noExotics hF] at hle

/-- The chiral indices of the representation `Q = (3,2)_{1/6}` are less then
  or equal to `3`. -/
lemma FluxesTen.chiralIndicesOfQ_le_three_of_noExotics (F : FluxesTen) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfQ) : ci ≤ 3 := by
  have hle := Multiset.single_le_sum
    (fun x hx => chiralIndicesOfQ_noneg_of_noExotics F hF x hx) ci hci
  rwa [F.chiralIndicesOfQ_sum_eq_three_of_noExotics hF] at hle

/-- The chiral indices of the representation `U = (bar 3,1)_{-2/3}` are less then
  or equal to `3`. -/
lemma FluxesTen.chiralIndicesOfU_le_three_of_noExotics (F : FluxesTen) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfU) : ci ≤ 3 := by
  have hle := Multiset.single_le_sum
    (fun x hx => chiralIndicesOfU_noneg_of_noExotics F hF x hx) ci hci
  rwa [F.chiralIndicesOfU_sum_eq_three_of_noExotics hF] at hle

/-- The chiral indices of the representation `E = (1,1)_{1}` are less then
  or equal to `3`. -/
lemma FluxesTen.chiralIndicesOfE_le_three_of_noExotics (F : FluxesTen) (hF : NoExotics F)
    (ci : ℤ) (hci : ci ∈ F.chiralIndicesOfE) : ci ≤ 3 := by
  have hle := Multiset.single_le_sum
    (fun x hx => chiralIndicesOfE_noneg_of_noExotics F hF x hx) ci hci
  rwa [F.chiralIndicesOfE_sum_eq_three_of_noExotics hF] at hle

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
  have hs : S.map (fun x => x.1) ≤ F.chiralIndicesOfD := Multiset.map_le_map hSle
  have hpos : 0 ≤ (F.chiralIndicesOfD - S.map (fun x => x.1)).sum :=
    Multiset.sum_nonneg fun x hx =>
      chiralIndicesOfD_noneg_of_noExotics F hF x (Multiset.mem_of_le tsub_le_self hx)
  have sum_add_compl_eq_three : (S.map (fun x => x.1)).sum +
      (F.chiralIndicesOfD - S.map (fun x => x.1)).sum = 3 := by
    rw [← Multiset.sum_add, add_tsub_cancel_of_le hs,
      F.chiralIndicesOfD_sum_eq_three_of_noExotics hF]
  omega

lemma FluxesFive.chiralIndicesOfL_subset_sum_le_three_of_noExotics (F : FluxesFive)
    (hF : NoExotics F) (S : Multiset Fluxes)
    (hSle : S ≤ F) : (S.map (fun x => (x.1 + x.2))).sum ≤ 3 := by
  have hs : S.map (fun x => (x.1 + x.2)) ≤ F.chiralIndicesOfL := Multiset.map_le_map hSle
  have hpos : 0 ≤ (F.chiralIndicesOfL - S.map (fun x => (x.1 + x.2))).sum :=
    Multiset.sum_nonneg fun x hx =>
      chiralIndicesOfL_noneg_of_noExotics F hF x (Multiset.mem_of_le tsub_le_self hx)
  have sum_add_compl_eq_three : (S.map (fun x => (x.1 + x.2))).sum +
      (F.chiralIndicesOfL - S.map (fun x => (x.1 + x.2))).sum = 3 := by
    rw [← Multiset.sum_add, add_tsub_cancel_of_le hs,
      F.chiralIndicesOfL_sum_eq_three_of_noExotics hF]
  omega

lemma FluxesTen.chiralIndicesOfQ_subset_sum_le_three_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) (S : Multiset Fluxes)
    (hSle : S ≤ F) : (S.map (fun x => x.1)).sum ≤ 3 := by
  have hs : S.map (fun x => x.1) ≤ F.chiralIndicesOfQ := Multiset.map_le_map hSle
  have hpos : 0 ≤ (F.chiralIndicesOfQ - S.map (fun x => x.1)).sum :=
    Multiset.sum_nonneg fun x hx =>
      chiralIndicesOfQ_noneg_of_noExotics F hF x (Multiset.mem_of_le tsub_le_self hx)
  have sum_add_compl_eq_three : (S.map (fun x => x.1)).sum +
      (F.chiralIndicesOfQ - S.map (fun x => x.1)).sum = 3 := by
    rw [← Multiset.sum_add, add_tsub_cancel_of_le hs,
      F.chiralIndicesOfQ_sum_eq_three_of_noExotics hF]
  omega

lemma FluxesTen.chiralIndicesOfU_subset_sum_le_three_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) (S : Multiset Fluxes)
    (hSle : S ≤ F) : (S.map (fun x => (x.1 - x.2))).sum ≤ 3 := by
  have hs : S.map (fun x => (x.1 - x.2)) ≤ F.chiralIndicesOfU := Multiset.map_le_map hSle
  have hpos : 0 ≤ (F.chiralIndicesOfU - S.map (fun x => (x.1 - x.2))).sum :=
    Multiset.sum_nonneg fun x hx =>
      chiralIndicesOfU_noneg_of_noExotics F hF x (Multiset.mem_of_le tsub_le_self hx)
  have sum_add_compl_eq_three : (S.map (fun x => (x.1 - x.2))).sum +
      (F.chiralIndicesOfU - S.map (fun x => (x.1 - x.2))).sum = 3 := by
    rw [← Multiset.sum_add, add_tsub_cancel_of_le hs,
      F.chiralIndicesOfU_sum_eq_three_of_noExotics hF]
  omega

lemma FluxesTen.chiralIndicesOfE_subset_sum_le_three_of_noExotics (F : FluxesTen)
    (hF : NoExotics F) (S : Multiset Fluxes)
    (hSle : S ≤ F) : (S.map (fun x => (x.1 + x.2))).sum ≤ 3 := by
  have hs : S.map (fun x => (x.1 + x.2)) ≤ F.chiralIndicesOfE := Multiset.map_le_map hSle
  have hpos : 0 ≤ (F.chiralIndicesOfE - S.map (fun x => (x.1 + x.2))).sum :=
    Multiset.sum_nonneg fun x hx =>
      chiralIndicesOfE_noneg_of_noExotics F hF x (Multiset.mem_of_le tsub_le_self hx)
  have sum_add_compl_eq_three : (S.map (fun x => (x.1 + x.2))).sum +
      (F.chiralIndicesOfE - S.map (fun x => (x.1 + x.2))).sum = 3 := by
    rw [← Multiset.sum_add, add_tsub_cancel_of_le hs,
      F.chiralIndicesOfE_sum_eq_three_of_noExotics hF]
  omega

end SU5

end FTheory
