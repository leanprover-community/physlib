/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

/-!
# The Kadison–Schwarz inequality

Unital completely positive maps satisfy `f a⋆ f a ≤ f (a⋆ a)`.

## i. Overview

A unital completely positive map `f` satisfies the Kadison–Schwarz inequality
`f a⋆ f a ≤ f (a⋆ a)`. A positive map with equality for every `a` is multiplicative.

## ii. Key results

- `CStarMatrix.nonneg_apply_self` : the diagonal entries of a positive matrix are positive.
- `CompletelyPositiveMap.star_map_mul_map_le` : the Kadison–Schwarz inequality.
- `PositiveLinearMap.map_mul_of_map_star_mul_self` : equality in the Kadison–Schwarz inequality
  makes a positive map multiplicative.

## iii. Table of contents

- A. Diagonal entries of positive matrices
- B. The Kadison–Schwarz inequality
- C. Multiplicativity

## iv. References

* None.

-/

@[expose] public section

open scoped CStarAlgebra

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] {n : Type*} [Fintype n]

/-! ## A. Diagonal entries of positive matrices -/

/-- The diagonal entries of a positive matrix over a C⋆-algebra are positive. -/
lemma CStarMatrix.nonneg_apply_self {M : CStarMatrix n n B} (hM : 0 ≤ M) (i : n) :
    0 ≤ M i i := by
  rw [StarOrderedRing.nonneg_iff] at hM
  induction hM using AddSubmonoid.closure_induction with
  | mem M hM =>
    obtain ⟨N, rfl⟩ := hM
    exact Finset.sum_nonneg fun j _ ↦ star_mul_self_nonneg (N j i)
  | zero => exact le_rfl
  | add M N _ _ hM hN => exact add_nonneg hM hN

/-! ## B. The Kadison–Schwarz inequality -/

/-- The Kadison–Schwarz inequality `f a⋆ f a ≤ f (a⋆ a)` for a unital completely positive map. -/
lemma CompletelyPositiveMap.star_map_mul_map_le (f : A →CP B) (hf : f 1 = 1) (a : A) :
    star (f a) * f a ≤ f (star a * a) := by
  have h := CStarMatrix.nonneg_apply_self (star_left_conjugate_nonneg
    (f.map_cstarMatrix_nonneg _ (star_mul_self_nonneg
      (CStarMatrix.ofMatrix !![a, 1; 0, 0] : CStarMatrix (Fin 2) (Fin 2) A)))
    (CStarMatrix.ofMatrix !![1, 0; -f a, 0])) 0
  simpa [CStarMatrix.mul_apply, CStarMatrix.star_apply, CStarMatrix.map_apply, Fin.sum_univ_two,
    hf, map_star] using h

/-! ## C. Multiplicativity -/

/-- A positive linear map with `f (a⋆ a) = f a⋆ f a` for every `a` is multiplicative. -/
lemma PositiveLinearMap.map_mul_of_map_star_mul_self (f : A →ₚ[ℂ] B)
    (h : ∀ a, f (star a * a) = star (f a) * f a) (a b : A) : f (a * b) = f a * f b := by
  have hab := h (star a + b)
  have hia := h (star a + Complex.I • b)
  have ha : f (a * star a) = f a * star (f a) := by simpa [map_star] using h (star a)
  simp only [star_add, star_smul, star_star, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    map_add, map_smul, map_star, Complex.star_def, Complex.conj_I, h, ha] at hab hia
  linear_combination (norm := (match_scalars <;> ring_nf <;> simp [Complex.I_sq]))
    (1 / 2 : ℂ) • hab - (Complex.I / 2) • hia
