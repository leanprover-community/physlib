/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import PhysLean.StringTheory.FTheory.SU5.Fluxes.Basic
public import Mathlib.Tactic.FinCases
/-!

# Terms of `FluxesFive` and `FluxesTen` with no chiral exotics

## i. Overview

In this module we give the terms of type `FluxesFive` and `FluxesTen`
which obey the `NoExotics` and `HasNoZero` propositions.

In each case, there is only a finite set of such elements, which we give explicitly.
We show that these sets are complete in the module
`StringTheory.FTheory.SU5.Fluxes.NoExotics.Completeness`.

This module is reserved for the explicit sets of elements, and simple lemmas about the
elements of those elements.

## ii. Key results

- `FluxesFive.elemsNoExotics` : The multiset of elements of `FluxesFive` which obey `NoExotics`
  and `HasNoZero`.
- `FluxesTen.elemsNoExotics` : The multiset of elements of `FluxesTen` which obey `NoExotics`
  and `HasNoZero`.

## iii. Table of contents

- A. The multiset sets of `FluxesFive` with no chiral exotics and no zero fluxes
  - A.1. The definition of the multiset
  - A.2. The cardinality of the multiset is 31
  - A.3. The multiset has no duplicates
  - A.4. Every element of the multiset obeys `NoExotics`
  - A.5. Every element of the multiset has at most 4 distinct flux pairs
  - A.6. Every element of the multiset has at most 6 flux pairs
  - A.7. The sum of all flux-pairs in any element of the multiset is (3, 0)
  - A.8. Every element of the multiset obeys `HasNoZero`
  - A.9. A sum relation for subsets of elements of the multiset
- B. The multiset sets of `FluxesFive` with no chiral exotics and no zero fluxes
  - B.1. The definition of the multiset
  - B.2. The cardinality of the multiset is 6
  - B.3. The multiset has no duplicates
  - B.4. Every element of the multiset obeys `NoExotics`
  - B.5. Every element of the multiset has at most 3 distinct flux pairs
  - B.6. The sum of all flux-pairs in any element of the multiset is (3, 0)
  - B.7. Every element of the multiset obeys `HasNoZero`

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section
namespace FTheory

namespace SU5

/-!

## A. The multiset sets of `FluxesFive` with no chiral exotics and no zero fluxes

-/

namespace FluxesFive

/-!

### A.1. The definition of the multiset

-/

/-- The elements of `FluxesFive` for which the `NoExotics` condition holds. -/
def elemsNoExotics : Multiset FluxesFive := {
    {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩},
    {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 1⟩, ⟨0, 2⟩},
    {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩},
    {⟨1, 1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 1⟩},
    {⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 1⟩},
    {⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 2⟩},
    {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 3⟩},
    {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 2⟩},
    {⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩}, {⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩},
    {⟨1, -1⟩, ⟨2, -2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩},
    {⟨1, -1⟩, ⟨2, -2⟩, ⟨0, 1⟩, ⟨0, 2⟩},
    {⟨1, -1⟩, ⟨2, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩},
    {⟨1, 0⟩, ⟨2, -2⟩, ⟨0, 1⟩, ⟨0, 1⟩},
    {⟨1, 1⟩, ⟨2, -2⟩, ⟨0, 1⟩}, {⟨1, 0⟩, ⟨2, -1⟩, ⟨0, 1⟩},
    {⟨1, 0⟩, ⟨2, -2⟩, ⟨0, 2⟩}, {⟨1, -1⟩, ⟨2, 0⟩, ⟨0, 1⟩},
    {⟨1, -1⟩, ⟨2, -1⟩, ⟨0, 2⟩}, {⟨1, -1⟩, ⟨2, -2⟩, ⟨0, 3⟩},
    {⟨1, -1⟩, ⟨2, 1⟩}, {⟨1, 0⟩, ⟨2, 0⟩}, {⟨1, 1⟩, ⟨2, -1⟩},
    {⟨1, 2⟩, ⟨2, -2⟩},
    {⟨3, -3⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩},
    {⟨3, -3⟩, ⟨0, 1⟩, ⟨0, 2⟩}, {⟨3, -2⟩, ⟨0, 1⟩, ⟨0, 1⟩},
    {⟨3, -3⟩, ⟨0, 3⟩}, {⟨3, -2⟩, ⟨0, 2⟩}, {⟨3, -1⟩, ⟨0, 1⟩},
    {⟨3, 0⟩}}

/-!

### A.2. The cardinality of the multiset is 31

-/

lemma elemsNoExotics_card : elemsNoExotics.card = 31 := by
  decide

/-!

### A.3. The multiset has no duplicates

-/

lemma elemsNoExotics_nodup : elemsNoExotics.Nodup := by
  decide

/-!

### A.4. Every element of the multiset obeys `NoExotics`

-/

lemma noExotics_of_mem_elemsNoExotics (F : FluxesFive) (h : F ∈ elemsNoExotics) :
    NoExotics F := by
  revert F
  decide

/-!

### A.5. Every element of the multiset has at most 4 distinct flux pairs

-/

lemma toFinset_card_le_four_mem_elemsNoExotics (F : FluxesFive) (h : F ∈ elemsNoExotics) :
    F.toFinset.card ≤ 4 := by
  revert F h
  decide

/-!

### A.6. Every element of the multiset has at most 6 flux pairs

-/

lemma card_le_six_mem_elemsNoExotics (F : FluxesFive) (h : F ∈ elemsNoExotics) :
    F.card ≤ 6 := by
  revert F h
  decide

/-!

### A.7. The sum of all flux-pairs in any element of the multiset is (3, 0)

-/

lemma sum_of_mem_elemsNoExotics (F : FluxesFive) (h : F ∈ elemsNoExotics) :
    F.sum = ⟨3, 0⟩ := by
  revert F h
  decide

/-!

### A.8. Every element of the multiset obeys `HasNoZero`

-/

lemma hasNoZero_of_mem_elemsNoExotics (F : FluxesFive) (h : F ∈ elemsNoExotics) :
    F.HasNoZero := by
  revert F h
  decide

/-!

### A.9. A sum relation for subsets of elements of the multiset

-/

lemma map_sum_add_of_mem_powerset_elemsNoExotics (F S : FluxesFive)
    (hf : F ∈ FluxesFive.elemsNoExotics)
    (hS: S ∈ Multiset.powerset F) :
    (S.map (fun x => ⟨|x.1|, -|x.1|⟩)).sum +
    (S.map (fun x => ⟨(0 : ℤ), |x.1 + x.2|⟩)).sum = S.sum := by
  fin_cases hf
  all_goals
  · fin_cases hS
    all_goals decide

end FluxesFive

/-!

## B. The multiset sets of `FluxesFive` with no chiral exotics and no zero fluxes

-/
namespace FluxesTen

/-!

### B.1. The definition of the multiset

-/

/-- The elements of `FluxesTen` for which the `NoExotics` condition holds. -/
def elemsNoExotics : Multiset FluxesTen := {{⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩},
  {⟨1, 1⟩, ⟨1, -1⟩, ⟨1, 0⟩}, {⟨1, 0⟩, ⟨2, 0⟩},
  {⟨1, -1⟩, ⟨2, 1⟩}, {⟨1, 1⟩, ⟨2, -1⟩},
  {⟨3, 0⟩}}

/-!

### B.2. The cardinality of the multiset is 6

-/

lemma elemsNoExotics_card : elemsNoExotics.card = 6 := by
  decide

/-!

### B.3. The multiset has no duplicates

-/

lemma elemsNoExotics_nodup : elemsNoExotics.Nodup := by
  decide

/-!

### B.4. Every element of the multiset obeys `NoExotics`

-/

lemma noExotics_of_mem_elemsNoExotics (F : FluxesTen) (h : F ∈ elemsNoExotics) :
    NoExotics F := by
  revert F
  decide

/-!

### B.5. Every element of the multiset has at most 3 distinct flux pairs

-/

lemma toFinset_card_le_three_mem_elemsNoExotics (F : FluxesTen) (h : F ∈ elemsNoExotics) :
    F.toFinset.card ≤ 3 := by
  revert F h
  decide

/-!

### B.6. The sum of all flux-pairs in any element of the multiset is (3, 0)

-/

lemma sum_of_mem_elemsNoExotics (F : FluxesTen) (h : F ∈ elemsNoExotics) :
    F.sum = ⟨3, 0⟩ := by
  revert F h
  decide

/-!

### B.7. Every element of the multiset obeys `HasNoZero`

-/

lemma hasNoZero_of_mem_elemsNoExotics (F : FluxesTen) (h : F ∈ elemsNoExotics) :
    F.HasNoZero := by
  revert F h
  decide

end FluxesTen

end SU5

end FTheory
