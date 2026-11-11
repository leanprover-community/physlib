/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!

# Bounds on iterated derivatives

Norm bounds for iterated Fréchet derivatives of a composition with a continuous linear map and of
a product.

## i. Overview

Composing with a continuous linear map `L` multiplies the `n`th derivative by at most `‖L‖ⁿ`. The
`k`th derivative of a product of two smooth real functions is bounded by `2ᵏ` times the product of
bounds of the factors. These estimates control the seminorms of Schwartz functions under linear
changes of variables and under multiplication with smooth cutoffs.

## ii. Key results

- `IteratedFDerivBounds.norm_iteratedFDeriv_comp_clm_le` : composition with a linear map.
- `IteratedFDerivBounds.norm_iteratedFDeriv_mul_le_two_pow` : the Leibniz bound for a product.

## iii. Table of contents

- A. Composition with a linear map
- B. Products

## iv. References

None.

## A. Composition with a linear map

- `IteratedFDerivBounds.norm_iteratedFDeriv_comp_clm_le` : composition with a linear map.

## B. Products

- `IteratedFDerivBounds.norm_iteratedFDeriv_mul_le_two_pow` : the Leibniz bound for a product.
-/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace IteratedFDerivBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Composing with a continuous linear map costs the operator norm to the order of the
derivative. -/
lemma norm_iteratedFDeriv_comp_clm_le {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (L : G →L[ℝ] E) {f : E → H}
    (hf : ContDiff ℝ ∞ f) (n : ℕ) (y : G) :
    ‖iteratedFDeriv ℝ n (f ∘ L) y‖ ≤ ‖iteratedFDeriv ℝ n f (L y)‖ * ‖L‖ ^ n := by
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right L hf y (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The Leibniz bound.** If the derivatives of order up to `k` of `b` and `v` are bounded by `B`
and `S` at `x` then the `k`th derivative of `b * v` is bounded by `2 ^ k * B * S`. -/
lemma norm_iteratedFDeriv_mul_le_two_pow (b v : E → ℝ) (hb : ContDiff ℝ ∞ b)
    (hv : ContDiff ℝ ∞ v) (x : E) (k : ℕ) {B S : ℝ}
    (hB : ∀ i ≤ k, ‖iteratedFDeriv ℝ i b x‖ ≤ B) (hS : ∀ j ≤ k, ‖iteratedFDeriv ℝ j v x‖ ≤ S) :
    ‖iteratedFDeriv ℝ k (fun y => b y * v y) x‖ ≤ 2 ^ k * B * S := by
  refine (norm_iteratedFDeriv_mul_le hb hv x (by exact_mod_cast le_top)).trans ?_
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _))
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0 (Nat.zero_le _))
  calc _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * B * S := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        gcongr
        · exact hB i hi'
        · exact hS (k - i) (Nat.sub_le _ _)
    _ = 2 ^ k * B * S := by
        simp_rw [mul_assoc, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring

end IteratedFDerivBounds
