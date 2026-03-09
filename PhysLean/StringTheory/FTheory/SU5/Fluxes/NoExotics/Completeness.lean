/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.StringTheory.FTheory.SU5.Fluxes.NoExotics.ChiralIndices
public import PhysLean.StringTheory.FTheory.SU5.Fluxes.NoExotics.Elems
/-!

# Completeness of `Elems` with regard to the `NoExotics` condition

## i. Overview

In the module:

- `PhysLean.StringTheory.FTheory.SU5.Fluxes.NoExotics.Elems`

we define finite sets of elements of `FluxesFive` and `FluxesTen` which satisfy the
`NoExotics` and `HasNoZero` conditions.

In this module we prove that these sets are complete, in the sense that every
element of `FluxesFive` or `FluxesTen` which satisfies the `NoExotics` and
`HasNoZero` conditions is contained in them.

Our proof follows by building allowed subsets of fluxes by their cardinality, and heavily relies
on the `decide` tactic.

Note that the `10d` fluxes are much more constrained than the 5-bar fluxes. This is because
they are constrained by `3` SM representations `Q`, `U`, and `E`, whereas the 5-bar fluxes
are only constrained by `2` SM representations `D` and `L`.

## ii. Key results

- `FluxesFive.noExotics_iff_mem_elemsNoExotics` : An element of `FluxesFive` satisfies `NoExotics`
  and `HasNoZero` if and only if it is an element of `elemsNoExotics`.
- `FluxesTen.noExotics_iff_mem_elemsNoExotics` : An element of `FluxesTen` satisfies `NoExotics`
  and `HasNoZero` if and only if it is an element of `elemsNoExotics`.

## iii. Table of contents

- A. All terms of `FluxesFive` obeying `NoExotics` and `HasNoZero`
  - A.1. The allowed fluxes in a `FluxesFive` which obeys `NoExotics` and `HasNoZero`
  - A.2. Sufficient condition for a set to contain allowed subsets of card `n.succ` based on `n`
  - A.3. Statement of the allowed subsets of each cardinality
  - A.4. Lemma that stated allowed subsets are complete
  - A.5. Terms of `FluxesFive` obeying `NoExotics` and `HasNoZero` have card ≤ 6
  - A.6. Terms of `FluxesFive` obeying `NoExotics` and `HasNoZero` are in `elemsNoExotics`
  - A.7. Terms of `FluxesFive` obey `NoExotics` and `HasNoZero` if and only if in `elemsNoExotics`
- B. All terms of `FluxesTen` obeying `NoExotics` and `HasNoZero`
  - B.1. The allowed fluxes in a `FluxesTen` which obeys `NoExotics` and `HasNoZero`
  - B.2. Sufficient condition for a set to contain allowed subsets of card `n.succ` based on `n`
  - B.3. Statement of the allowed subsets of each cardinality
  - B.4. Lemma that stated allowed subsets are complete
  - B.5. Terms of `FluxesTen` obeying `NoExotics` and `HasNoZero` have card ≤ 3
  - B.6. Terms of `FluxesTen` obeying `NoExotics` and `HasNoZero` are in `elemsNoExotics`
  - B.7. Terms of `FluxesTen` obey `NoExotics` and `HasNoZero` if and only if in `elemsNoExotics`

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section
namespace FTheory

namespace SU5

/-!

## A. All terms of `FluxesFive` obeying `NoExotics` and `HasNoZero`

-/
namespace FluxesFive

/-!

### A.1. The allowed fluxes in a `FluxesFive` which obeys `NoExotics` and `HasNoZero`

-/

lemma mem_mem_finset_of_noExotics (F : FluxesFive) (hF : F.NoExotics)
    (hnZ : F.HasNoZero) (x : Fluxes) (hx : x ∈ F) :
    x ∈ ({⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 3⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 2⟩,
      ⟨2, -2⟩, ⟨2, -1⟩, ⟨2, 0⟩, ⟨2, 1⟩, ⟨3, -3⟩, ⟨3, -2⟩, ⟨3, -1⟩, ⟨3, 0⟩} : Finset Fluxes) := by
  simp only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton]
  have hL1 := F.mem_chiralIndicesOfL_mem_of_noExotics hF (x.M + x.N)
    (Multiset.mem_map.mpr ⟨x, hx, rfl⟩)
  have hD1 := F.mem_chiralIndicesOfD_mem_of_noExotics hF x.M
    (Multiset.mem_map.mpr ⟨x, hx, rfl⟩)
  have h0 : ¬ x = 0:= by
    by_contra hn
    subst hn
    exact hnZ hx
  have hd : x.N = (x.M + x.N) - x.M := by omega
  generalize x.M + x.N = D' at *
  rcases x with ⟨M, N⟩
  simp_all only [Fluxes.mk.injEq, Int.reduceNeg]
  subst hd
  clear hx
  revert h0
  revert D' M
  decide

/-!

### A.2. Sufficient condition for a set to contain allowed subsets of card `n.succ` based on `n`

-/

lemma subset_le_mem_of_card_eq_succ {n : ℕ} {F : FluxesFive} (hF : F.NoExotics) (hnZ : F.HasNoZero)
    (S : Multiset Fluxes) (hcard : S.card = n.succ) (hS : S ≤ F) {Y X : Finset (Multiset Fluxes)}
    (hY : ∀ (S : Multiset Fluxes), S.card = n → S ≤ F → S ∈ Y)
    (hX : ∀ a ∈ ({⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 3⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 2⟩,
      ⟨2, -2⟩, ⟨2, -1⟩, ⟨2, 0⟩, ⟨2, 1⟩, ⟨3, -3⟩, ⟨3, -2⟩, ⟨3, -1⟩, ⟨3, 0⟩} : Finset Fluxes),
      ∀ y ∈ Y,
      (Multiset.map (fun x => x.M + x.N) (a ::ₘ y)).sum ≤ 3 →
      (Multiset.map (fun x => x.M) (a ::ₘ y)).sum ≤ 3 →
      a ::ₘ y ∈ X) :
    S ∈ X := by
  have hSum1 := chiralIndicesOfL_subset_sum_le_three_of_noExotics F hF S hS
  have hSum2 := chiralIndicesOfD_subset_sum_le_three_of_noExotics F hF S hS
  revert S
  apply Multiset.induction
  · simp
  intro a S ih hcard hle hsum1 hsum2
  have hsub : S ≤ F := (S.le_cons_self a).trans hle
  have ha : a ∈ F := Multiset.mem_of_le hle (S.mem_cons_self a)
  rw [Multiset.card_cons] at hcard
  simp at hcard
  exact hX a (mem_mem_finset_of_noExotics F hF hnZ a ha) S (hY S hcard hsub) hsum1 hsum2

/-!

### A.3. Statement of the allowed subsets of each cardinality

-/

/-- The allowed subsets of a `FluxesFive` which has no exotics or zeros. -/
def noExoticsSubsets : (n : ℕ) → Finset (Multiset Fluxes)
  | 0 => {{}}
  | 1 => {{⟨0, 1⟩}, {⟨0, 2⟩}, {⟨0, 3⟩}, {⟨1, -1⟩}, {⟨1, 0⟩}, {⟨1, 1⟩}, {⟨1, 2⟩},
      {⟨2, -2⟩}, {⟨2, -1⟩}, {⟨2, 0⟩}, {⟨2, 1⟩}, {⟨3, -3⟩}, {⟨3, -2⟩}, {⟨3, -1⟩}, {⟨3, 0⟩}}
  | 2 => {{⟨0, 1⟩, ⟨0, 1⟩}, {⟨0, 1⟩, ⟨1, -1⟩}, {⟨0, 1⟩, ⟨1, 0⟩}, {⟨0, 1⟩, ⟨0, 2⟩},
      {⟨0, 1⟩, ⟨1, 1⟩}, {⟨0, 1⟩, ⟨2, -2⟩}, {⟨0, 1⟩, ⟨2, -1⟩}, {⟨0, 1⟩, ⟨2, 0⟩},
      {⟨0, 1⟩, ⟨3, -3⟩}, {⟨0, 1⟩, ⟨3, -2⟩}, {⟨0, 1⟩, ⟨3, -1⟩},
      {⟨0, 2⟩, ⟨1, -1⟩}, {⟨0, 2⟩, ⟨1, 0⟩}, {⟨0, 2⟩, ⟨2, -2⟩}, {⟨0, 2⟩, ⟨2, -1⟩},
      {⟨0, 2⟩, ⟨3, -3⟩}, {⟨0, 2⟩, ⟨3, -2⟩}, {⟨0, 3⟩, ⟨1, -1⟩}, {⟨0, 3⟩, ⟨2, -2⟩},
      {⟨0, 3⟩, ⟨3, -3⟩}, {⟨1, -1⟩, ⟨1, -1⟩}, {⟨1, -1⟩, ⟨1, 0⟩}, {⟨1, -1⟩, ⟨1, 1⟩},
      {⟨1, -1⟩, ⟨1, 2⟩}, {⟨1, -1⟩, ⟨2, -2⟩}, {⟨1, -1⟩, ⟨2, -1⟩}, {⟨1, -1⟩, ⟨2, 0⟩},
      {⟨1, 0⟩, ⟨1, 0⟩}, {⟨1, -1⟩, ⟨2, 1⟩}, {⟨1, 0⟩, ⟨1, 1⟩}, {⟨1, 0⟩, ⟨2, -2⟩},
      {⟨1, 0⟩, ⟨2, -1⟩}, {⟨1, 0⟩, ⟨2, 0⟩}, {⟨1, 1⟩, ⟨2, -2⟩}, {⟨1, 1⟩, ⟨2, -1⟩},
      {⟨1, 2⟩, ⟨2, -2⟩}}
  | 3 => {{⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩}, {⟨0, 1⟩, ⟨0, 1⟩, ⟨1, -1⟩},
    {⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩}, {⟨0, 1⟩, ⟨0, 1⟩, ⟨2, -2⟩},
    {⟨0, 1⟩, ⟨0, 1⟩, ⟨2, -1⟩}, {⟨0, 1⟩, ⟨0, 1⟩, ⟨3, -3⟩}, {⟨0, 1⟩, ⟨0, 1⟩, ⟨3, -2⟩},
    {⟨0, 1⟩, ⟨0, 2⟩, ⟨1, -1⟩}, {⟨0, 1⟩, ⟨0, 2⟩, ⟨2, -2⟩}, {⟨0, 1⟩, ⟨0, 2⟩, ⟨3, -3⟩},
    {⟨0, 1⟩, ⟨1, -1⟩, ⟨1, -1⟩}, {⟨0, 1⟩, ⟨1, -1⟩, ⟨1, 0⟩}, {⟨0, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩},
    {⟨0, 1⟩, ⟨1, -1⟩, ⟨2, -2⟩}, {⟨0, 1⟩, ⟨1, -1⟩, ⟨2, -1⟩}, {⟨0, 1⟩, ⟨1, -1⟩, ⟨2, 0⟩},
    {⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩}, {⟨0, 1⟩, ⟨1, 0⟩, ⟨2, -2⟩}, {⟨0, 1⟩, ⟨1, 0⟩, ⟨2, -1⟩},
    {⟨0, 1⟩, ⟨1, 1⟩, ⟨2, -2⟩}, {⟨0, 2⟩, ⟨1, -1⟩, ⟨1, -1⟩}, {⟨0, 2⟩, ⟨1, -1⟩, ⟨1, 0⟩},
    {⟨0, 2⟩, ⟨1, -1⟩, ⟨2, -2⟩}, {⟨0, 2⟩, ⟨1, -1⟩, ⟨2, -1⟩}, {⟨0, 2⟩, ⟨1, 0⟩, ⟨2, -2⟩},
    {⟨0, 3⟩, ⟨1, -1⟩, ⟨1, -1⟩}, {⟨0, 3⟩, ⟨1, -1⟩, ⟨2, -2⟩}, {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩},
    {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩}, {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 1⟩}, {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 2⟩},
    {⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩}, {⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩}, {⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩}}
  | 4 => {{⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, -1⟩},
    {⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨2, -2⟩}, {⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨3, -3⟩},
    {⟨0, 1⟩, ⟨0, 1⟩, ⟨1, -1⟩, ⟨1, -1⟩}, {⟨0, 1⟩, ⟨0, 1⟩, ⟨1, -1⟩, ⟨1, 0⟩},
    {⟨0, 1⟩, ⟨0, 1⟩, ⟨1, -1⟩, ⟨2, -2⟩}, {⟨0, 1⟩, ⟨0, 1⟩, ⟨1, -1⟩, ⟨2, -1⟩},
    {⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨2, -2⟩}, {⟨0, 1⟩, ⟨0, 2⟩, ⟨1, -1⟩, ⟨1, -1⟩},
    {⟨0, 1⟩, ⟨0, 2⟩, ⟨1, -1⟩, ⟨2, -2⟩}, {⟨0, 1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩},
    {⟨0, 1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩}, {⟨0, 1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 1⟩},
    {⟨0, 1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩}, {⟨0, 2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩},
    {⟨0, 2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩}, {⟨0, 3⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩}}
  | 5 => {{⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, -1⟩, ⟨1, -1⟩},
    {⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, -1⟩, ⟨2, -2⟩},
    {⟨0, 1⟩, ⟨0, 1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩},
    {⟨0, 1⟩, ⟨0, 1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩},
    {⟨0, 1⟩, ⟨0, 2⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩}}
  | 6 => {{⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩}}
  | _ + 7 => ∅

/-!

### A.4. Lemma that stated allowed subsets are complete

-/

lemma subset_of_fluxesFive_mem_noExoticsSubsets_of_noExotics {F : FluxesFive} (hF : F.NoExotics)
    (hnZ : F.HasNoZero) (S : Multiset Fluxes) (hS : S ≤ F) :
    S ∈ noExoticsSubsets S.card := recS S.card S rfl hS
where recS : (n : ℕ) → (S : Multiset Fluxes) → S.card = n → S ≤ F → S ∈ noExoticsSubsets n
  | 0, S, hcard, hS => by
    rw [Multiset.card_eq_zero] at hcard
    subst hcard
    simp [noExoticsSubsets]
  | 1, S, hcard, hS => subset_le_mem_of_card_eq_succ hF hnZ S hcard hS
    (fun S hc => recS 0 S hc) <| by decide
  | 2, S, hcard, hS => subset_le_mem_of_card_eq_succ hF hnZ S hcard hS
    (fun S hc => recS 1 S hc) <| by decide
  | 3, S, hcard, hS => subset_le_mem_of_card_eq_succ hF hnZ S hcard hS
    (fun S hc => recS 2 S hc) <| by decide
  | 4, S, hcard, hS => subset_le_mem_of_card_eq_succ hF hnZ S hcard hS
    (fun S hc => recS 3 S hc) <| by decide
  | 5, S, hcard, hS => subset_le_mem_of_card_eq_succ hF hnZ S hcard hS
    (fun S hc => recS 4 S hc) <| by decide
  | 6, S, hcard, hS => subset_le_mem_of_card_eq_succ hF hnZ S hcard hS
    (fun S hc => recS 5 S hc) <| by decide
  | 7, S, hcard, hS => subset_le_mem_of_card_eq_succ hF hnZ S hcard hS
    (fun S hc => recS 6 S hc) <| by decide
  | (n + 1) + 7, S, hcard, hS => subset_le_mem_of_card_eq_succ hF hnZ S hcard hS
    (fun S hc => recS (n + 7) S hc) <| by
      simp [noExoticsSubsets]

/-!

### A.5. Terms of `FluxesFive` obeying `NoExotics` and `HasNoZero` have card ≤ 6

-/

lemma card_le_six_of_noExotics {F : FluxesFive} (hF : F.NoExotics) (hnZ : F.HasNoZero) :
    F.card ≤ 6 := by
  have hx := subset_of_fluxesFive_mem_noExoticsSubsets_of_noExotics hF hnZ F
    (Preorder.le_refl F)
  generalize F.card = n at *
  match n with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | 3 => simp
  | 4 => simp
  | 5 => simp
  | 6 => simp
  | _ + 7 => simp [noExoticsSubsets] at hx

lemma card_mem_range_seven_of_noExotics {F : FluxesFive} (hF : F.NoExotics) (hnZ : F.HasNoZero) :
    F.card ∈ Finset.range 7 := by
  rw [Finset.mem_range_succ_iff]
  exact card_le_six_of_noExotics hF hnZ

/-!

### A.6. Terms of `FluxesFive` obeying `NoExotics` and `HasNoZero` are in `elemsNoExotics`

-/

lemma mem_elemsNoExotics_of_noExotics (F : FluxesFive) (hNE : F.NoExotics) (hnZ : F.HasNoZero) :
    F ∈ elemsNoExotics := by
  have h1 := card_mem_range_seven_of_noExotics hNE hnZ
  have hF := subset_of_fluxesFive_mem_noExoticsSubsets_of_noExotics hNE hnZ F
    (Preorder.le_refl F)
  simp only [Finset.range, Multiset.range_succ, Multiset.range_zero, Multiset.cons_zero,
    Finset.mk_cons, Finset.cons_eq_insert, Finset.mem_insert, Finset.mem_mk,
    Multiset.mem_singleton] at h1
  rcases h1 with hr | hr | hr | hr | hr | hr | hr
  all_goals
  · rw [hr] at hF
    clear hr hnZ
    revert hNE
    revert F
    decide

/-!

### A.7. Terms of `FluxesFive` obey `NoExotics` and `HasNoZero` if and only if in `elemsNoExotics`

-/

/-- Completeness of `elemsNoExotics`, that is, every element of `FluxesFive`
  which obeys `NoExotics` is an element of `elemsNoExotics`, and every
  element of `elemsNoExotics` obeys `NoExotics`. -/
lemma noExotics_iff_mem_elemsNoExotics (F : FluxesFive) :
    F.NoExotics ∧ F.HasNoZero ↔ F ∈ elemsNoExotics := by
  constructor
  · exact fun ⟨h1, h2⟩ => mem_elemsNoExotics_of_noExotics F h1 h2
  · exact fun h => ⟨noExotics_of_mem_elemsNoExotics F h, hasNoZero_of_mem_elemsNoExotics F h⟩

end FluxesFive

/-!

## B. All terms of `FluxesTen` obeying `NoExotics` and `HasNoZero`

-/

namespace FluxesTen

/-!

### B.1. The allowed fluxes in a `FluxesTen` which obeys `NoExotics` and `HasNoZero`

-/

lemma mem_mem_finset_of_noExotics (F : FluxesTen) (hF : F.NoExotics) (hnZ : F.HasNoZero)
    (x : Fluxes) (hx : x ∈ F) :
    x ∈ ({⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, -1⟩, ⟨2, 0⟩, ⟨2, 1⟩, ⟨3, 0⟩} : Finset Fluxes) := by
  rcases x with f
  simp only [Int.reduceNeg, Finset.mem_insert, Finset.mem_singleton]
  have hQ1 := F.mem_chiralIndicesOfQ_mem_of_noExotics hF x.M (Multiset.mem_map.mpr ⟨x, hx, rfl⟩)
  have hU1 := F.mem_chiralIndicesOfU_mem_of_noExotics hF (x.M - x.N)
    (Multiset.mem_map.mpr ⟨x, hx, rfl⟩)
  have hE1 := F.mem_chiralIndicesOfE_mem_of_noExotics hF (x.M + x.N)
    (Multiset.mem_map.mpr ⟨x, hx, rfl⟩)
  have h0 : ¬ x = 0 := by
    by_contra hn
    subst hn
    exact hnZ hx
  rcases x with ⟨M, N⟩
  let D := M + N
  have hd : N = D - M := by omega
  generalize D = D' at *
  subst hd
  simp only [add_sub_cancel] at hE1
  simp_all only [Int.reduceNeg, Fluxes.mk.injEq]
  clear hx D
  revert h0 hU1
  revert D'
  revert M
  decide

/-!

### B.2. Sufficient condition for a set to contain allowed subsets of card `n.succ` based on `n`

-/
lemma subset_le_mem_of_card_eq_succ {n : ℕ} {F : FluxesTen} (hF : F.NoExotics) (hnZ : F.HasNoZero)
    (S : Multiset Fluxes) (hcard : S.card = n.succ) (hS : S ≤ F) {Y X : Finset (Multiset Fluxes)}
    (hY : ∀ (S : Multiset Fluxes), S.card = n → S ≤ F → S ∈ Y)
    (hX : ∀ a ∈ ({⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨2, -1⟩, ⟨2, 0⟩, ⟨2, 1⟩, ⟨3, 0⟩} : Finset Fluxes),
      ∀ y ∈ Y,
      (Multiset.map (fun x => x.M) (a ::ₘ y)).sum ≤ 3 →
      (Multiset.map (fun x => x.M - x.N) (a ::ₘ y)).sum ≤ 3 →
      (Multiset.map (fun x => x.M + x.N) (a ::ₘ y)).sum ≤ 3 →
      a ::ₘ y ∈ X) :
    S ∈ X := by
  have hSum1 := chiralIndicesOfQ_subset_sum_le_three_of_noExotics F hF S hS
  have hSum2 := chiralIndicesOfU_subset_sum_le_three_of_noExotics F hF S hS
  have hsum3 := chiralIndicesOfE_subset_sum_le_three_of_noExotics F hF S hS
  revert S
  apply Multiset.induction
  · simp
  intro a S ih hcard hle hsum1 hsum2 hsum3
  have hsub : S ≤ F := (S.le_cons_self a).trans hle
  have ha : a ∈ F := Multiset.mem_of_le hle (S.mem_cons_self a)
  rw [Multiset.card_cons] at hcard
  simp at hcard
  exact hX a (mem_mem_finset_of_noExotics F hF hnZ a ha) S (hY S hcard hsub) hsum1 hsum2 hsum3

/-!

### B.3. Statement of the allowed subsets of each cardinality

-/

/-- The allowed subsets of a `FluxesTen` which has no exotics or zeros. -/
def noExoticsSubsets : (n : ℕ) → Finset (Multiset Fluxes)
  | 0 => {{}}
  | 1 => {{⟨1, -1⟩}, {⟨1, 0⟩}, {⟨1, 1⟩}, {⟨2, -1⟩}, {⟨2, 0⟩}, {⟨2, 1⟩}, {⟨3, 0⟩}}
  | 2 => {{⟨1, -1⟩, ⟨1, 0⟩}, {⟨1, -1⟩, ⟨1, 1⟩}, {⟨1, -1⟩, ⟨2, 1⟩},
      {⟨1, 0⟩, ⟨1, 0⟩}, {⟨1, 0⟩, ⟨1, 1⟩}, {⟨1, 0⟩, ⟨2, 0⟩}, {⟨1, 1⟩, ⟨2, -1⟩}}
  | 3 => {{⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩}, {⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩}}
  | _ + 4 => ∅

/-!

### B.4. Lemma that stated allowed subsets are complete

-/

lemma subset_of_fluxesTen_mem_noExoticsSubsets_of_noExotics {F : FluxesTen} (hF : F.NoExotics)
    (hnZ : F.HasNoZero) (S : Multiset Fluxes) (hS : S ≤ F) :
    S ∈ noExoticsSubsets S.card := recS S.card S rfl hS
where recS : (n : ℕ) → (S : Multiset Fluxes) → S.card = n → S ≤ F → S ∈ noExoticsSubsets n
  | 0, S, hcard, hS => by
    rw [Multiset.card_eq_zero] at hcard
    subst hcard
    simp [noExoticsSubsets]
  | 1, S, hcard, hS => subset_le_mem_of_card_eq_succ hF hnZ S hcard hS
    (fun S hc => recS 0 S hc) <| by decide
  | 2, S, hcard, hS => subset_le_mem_of_card_eq_succ hF hnZ S hcard hS
    (fun S hc => recS 1 S hc) <| by decide
  | 3, S, hcard, hS => subset_le_mem_of_card_eq_succ hF hnZ S hcard hS
    (fun S hc => recS 2 S hc) <| by decide
  | 4, S, hcard, hS => subset_le_mem_of_card_eq_succ hF hnZ S hcard hS
    (fun S hc => recS 3 S hc) <| by decide
  | (n + 1) + 4, S, hcard, hS => subset_le_mem_of_card_eq_succ hF hnZ S hcard hS
    (fun S hc => recS (n + 4) S hc) <| by
      simp [noExoticsSubsets]

/-!

### B.5. Terms of `FluxesTen` obeying `NoExotics` and `HasNoZero` have card ≤ 3

-/

lemma card_le_three_of_noExotics {F : FluxesTen} (hF : F.NoExotics) (hnZ : F.HasNoZero) :
    F.card ≤ 3 := by
  have hx := subset_of_fluxesTen_mem_noExoticsSubsets_of_noExotics hF hnZ F
    (Preorder.le_refl F)
  generalize F.card = n at *
  match n with
  | 0 => simp
  | 1 => simp
  | 2 => simp
  | 3 => simp
  | _ + 4 => simp [noExoticsSubsets] at hx

lemma card_mem_range_four_of_noExotics {F : FluxesTen} (hF : F.NoExotics) (hnZ : F.HasNoZero) :
    F.card ∈ Finset.range 4 := by
  rw [Finset.mem_range_succ_iff]
  exact card_le_three_of_noExotics hF hnZ

/-!

### B.6. Terms of `FluxesTen` obeying `NoExotics` and `HasNoZero` are in `elemsNoExotics`

-/

lemma mem_elemsNoExotics_of_noExotics (F : FluxesTen) (hNE : F.NoExotics) (hnZ : F.HasNoZero) :
    F ∈ elemsNoExotics := by
  have h1 := card_mem_range_four_of_noExotics hNE hnZ
  have hF := subset_of_fluxesTen_mem_noExoticsSubsets_of_noExotics hNE hnZ F
    (Preorder.le_refl F)
  simp only [Finset.range, Multiset.range_succ, Multiset.range_zero, Multiset.cons_zero,
    Finset.mk_cons, Finset.cons_eq_insert, Finset.mem_insert, Finset.mem_mk,
    Multiset.mem_singleton] at h1
  rcases h1 with hr | hr | hr | hr
  all_goals
  · rw [hr] at hF
    clear hr hnZ
    revert hNE
    revert F
    decide

/-!

### B.7. Terms of `FluxesTen` obey `NoExotics` and `HasNoZero` if and only if in `elemsNoExotics`

-/

/-- Completeness of `elemsNoExotics`, that is, every element of `FluxesTen`
  which obeys `NoExotics` is an element of `elemsNoExotics`, and every
  element of `elemsNoExotics` obeys `NoExotics`. -/
lemma noExotics_iff_mem_elemsNoExotics (F : FluxesTen) :
    F.NoExotics ∧ F.HasNoZero ↔ F ∈ elemsNoExotics := by
  constructor
  · exact fun h => mem_elemsNoExotics_of_noExotics F h.1 h.2
  · exact fun h => ⟨noExotics_of_mem_elemsNoExotics F h, hasNoZero_of_mem_elemsNoExotics F h⟩

end FluxesTen
end SU5

end FTheory
