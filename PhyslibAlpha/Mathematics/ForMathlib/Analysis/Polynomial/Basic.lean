/-
Copyright (c) 2026 Daniel Leonforte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Leonforte
-/
module

public import Mathlib.Analysis.Polynomial.Basic
/-!
# Polynomial growth of real polynomials

A real polynomial is bounded by a constant times a power of `1 + |t|`.

## i. Overview

The evaluation of a real polynomial `p` grows at most polynomially in `t`: there are `C ≥ 0`
and `k` with `|p.eval t| ≤ C (1 + |t|)^k` for every `t`. This is the form of bound used for
polynomially bounded functions and for integrability against Schwartz maps.

## ii. Key results

- `Polynomial.exists_abs_eval_le` : `|p.eval t| ≤ C (1 + |t|)^k` for some `C ≥ 0` and `k`.

## iii. Table of contents

- A. Polynomial growth

## iv. References

- None.

-/

@[expose] public section

namespace Polynomial

/-!

## A. Polynomial growth

-/

/-- A real polynomial grows at most polynomially: `|p(t)| ≤ C (1 + |t|)^k`. -/
lemma exists_abs_eval_le (p : Polynomial ℝ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ t, |p.eval t| ≤ C * (1 + |t|) ^ k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨C₁, k₁, hC₁, h₁⟩ := hp
    obtain ⟨C₂, k₂, hC₂, h₂⟩ := hq
    refine ⟨C₁ + C₂, max k₁ k₂, by positivity, fun t => ?_⟩
    have ht : 1 ≤ 1 + |t| := le_add_of_nonneg_right (abs_nonneg t)
    rw [Polynomial.eval_add]
    calc |p.eval t + q.eval t| ≤ |p.eval t| + |q.eval t| := abs_add_le _ _
      _ ≤ C₁ * (1 + |t|) ^ max k₁ k₂ + C₂ * (1 + |t|) ^ max k₁ k₂ := by
        gcongr
        · exact (h₁ t).trans (by gcongr; exact le_max_left _ _)
        · exact (h₂ t).trans (by gcongr; exact le_max_right _ _)
      _ = (C₁ + C₂) * (1 + |t|) ^ max k₁ k₂ := by ring
  | monomial n a =>
    refine ⟨|a|, n, abs_nonneg a, fun t => ?_⟩
    rw [Polynomial.eval_monomial, abs_mul, abs_pow]
    gcongr
    linarith [abs_nonneg t]

end Polynomial
