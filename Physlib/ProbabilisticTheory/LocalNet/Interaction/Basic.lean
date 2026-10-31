/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Physlib.ProbabilisticTheory.LocalNet.Basic

/-!
# Interactions on a local net

An interaction is a family of local observables, each associated with a region of the net.

## i. Overview

Extensive observables such as energy, magnetization and particle number can be expressed as
sums of local terms. An interaction assigns a supporting region and an observable to each
label. Each term can be included into any larger region and is taken to be zero when its
support is not contained in the region.

## ii. Key results

- `Interaction`: A family of local observables with specified supports.
- `Interaction.termIn`: An interaction term expressed in a given region.
- `Interaction.incl_termIn`: Compatibility with inclusions of regions.
- `Interaction.termIn_add`: Compatibility with addition.
- `Interaction.termIn_smul`: Compatibility with scalar multiplication.

## iii. Table of contents

- A. Interactions
- B. Interaction terms in a region

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory

variable {R : Type*} [Preorder R] {A : R → Type*} [∀ X, OrderUnitSpace (A X)]
  {N : LocalNet R A} {ι : Type*}

/-! ## A. Interactions -/

/-- A family of local observables on `N`, indexed by `ι`, with specified supports. -/
structure Interaction (N : LocalNet R A) (ι : Type*) where
  /-- The supporting region of each term. -/
  supp : ι → R
  /-- The observable associated with each term. -/
  term : ∀ i, A (supp i)

namespace Interaction

variable (Φ : Interaction N ι)

/-! ## B. Interaction terms in a region -/

/-- The labels of terms supported in `Λ`. -/
def labelsIn (Λ : R) : Set ι := {i | Φ.supp i ≤ Λ}

open Classical in
/-- The term `i` expressed in `Λ`, or zero if its support is not contained in `Λ`. -/
noncomputable def termIn (Λ : R) (i : ι) : A Λ :=
  if h : Φ.supp i ≤ Λ then N.incl h (Φ.term i) else 0

/-- Including a term from `Λ` into `Λ'` agrees with evaluating it in `Λ'` whenever
its support is contained in `Λ`, and gives zero otherwise. -/
lemma incl_termIn {Λ Λ' : R} (h : Λ ≤ Λ') (i : ι) :
    N.incl h (Φ.termIn Λ i) = (Φ.labelsIn Λ).indicator (Φ.termIn Λ') i := by
  by_cases h1 : Φ.supp i ≤ Λ
  · simp [termIn, labelsIn, h1, h1.trans h, N.incl_trans_apply h1 h (h1.trans h)]
  · simp [termIn, labelsIn, h1]

/-- Evaluating interaction terms in a region preserves addition. -/
lemma termIn_add (s : ι → R) (t t' : ∀ i, A (s i)) (Λ : R) (i : ι) :
    (⟨s, t + t'⟩ : Interaction N ι).termIn Λ i =
      (⟨s, t⟩ : Interaction N ι).termIn Λ i +
        (⟨s, t'⟩ : Interaction N ι).termIn Λ i := by
  by_cases h : s i ≤ Λ <;> simp [termIn, h]

/-- Evaluating interaction terms in a region preserves scalar multiplication. -/
lemma termIn_smul (s : ι → R) (c : ℝ) (t : ∀ i, A (s i)) (Λ : R) (i : ι) :
    (⟨s, c • t⟩ : Interaction N ι).termIn Λ i =
      c • (⟨s, t⟩ : Interaction N ι).termIn Λ i := by
  by_cases h : s i ≤ Λ <;> simp [termIn, h]

end Interaction

end ProbabilisticTheory
