/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith, Lode Vermeulen
-/
import PhysLean.SpaceAndTime.Space.Derivatives.Div
/-!

# The Laplacian operator on `Space d`

## i. Overview

In this module we define the Laplacian operator on functions and vector-valued
functions defined on `Space d`.

## ii. Key results

- `laplacian` : The Laplacian operator on scalar functions on `Space d`.
- `laplacianVec` : The Laplacian operator on vector-valued functions on `Space d`.

## iii. Table of contents

- A. Laplacian on functions to ℝ
  - A.1. Relation between laplacian and divergence of gradient
- B. Laplacian on vector valued functions

## iv. References

-/

namespace Space

/-!

## A. Laplacian on functions to ℝ

-/

/-- The scalar `laplacian` operator. -/
noncomputable def laplacian {d} (f : Space d → ℝ) :
    Space d → ℝ := fun x =>
  -- second derivative of f in i-th coordinate
  -- ∂²f/∂xᵢ²
  let df2 i x := ∂[i] (∂[i] f) x
  ∑ i, df2 i x

@[inherit_doc laplacian]
scoped[Space] notation "Δ" => laplacian

/-!

### A.1. Relation between laplacian and divergence of gradient

-/

lemma laplacian_eq_div_of_grad (f : Space → ℝ) :
    Δ f = ∇ ⬝ ∇ f := by
  unfold laplacian div grad Finset.sum
  simp only [Fin.univ_val_map, List.ofFn_succ, Fin.isValue, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, List.ofFn_zero, Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero]

/-!

## B. Laplacian on vector valued functions

-/

/-- The vector `laplacianVec` operator. -/
noncomputable def laplacianVec {d} (f : Space d → EuclideanSpace ℝ (Fin d)) :
    Space d → EuclideanSpace ℝ (Fin d) := fun x => WithLp.toLp 2 fun i =>
  -- get i-th component of `f`
  let fi i x := (f x) i
  Δ (fi i) x

@[inherit_doc laplacianVec]
scoped[Space] notation "Δ" => laplacianVec

end Space
