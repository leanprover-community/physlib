/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.DirectSum.Finite
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.Construction

/-!
# The Clebsch–Gordan dimension identity

Computes the dimensions in the tensor-product decomposition of standard `sl₂` modules.

## i. Overview

The product of the dimensions of two standard modules equals the sum of the dimensions
expected in their Clebsch–Gordan decomposition. Finite-dimensional linear algebra then gives
a nonempty type of vector-space equivalences. No equivariance or Clebsch–Gordan coefficients
are established.

## ii. Key results

- `clebsch_gordan_finrank` proves the dimension identity.
- `clebsch_gordan` gives a vector-space equivalence by dimension counting.

## iii. Table of contents

- A. Dimension counting

## iv. References

- Mathlib, `Mathlib.Algebra.Lie.Sl2`.

## A. Dimension counting
-/

@[expose] public section

noncomputable section

namespace PhyslibAlpha.Sl2

open scoped TensorProduct DirectSum

variable {K : Type*} [Field K]

/-- The arithmetic progression underlying the Clebsch–Gordan dimension count. -/
lemma sum_arithmetic_progression (m d : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (d + 2 * k + 1) = (m + 1) * (d + m + 1) := by
  have hgauss : ∑ k ∈ Finset.range (m + 1), 2 * k = (m + 1) * m := by
    have h := Finset.sum_range_id_mul_two (m + 1)
    rw [Finset.sum_mul] at h
    simpa [mul_comm] using h
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [hgauss]
  ring

/-- Reindex the dimension sum when `m ≤ n`. -/
lemma clebsch_gordan_finrank_aux (m n : ℕ) (h : m ≤ n) :
    (m + 1) * (n + 1) = ∑ k ∈ Finset.range (m + 1), (m + n - 2 * k + 1) := by
  set d := n - m with hd_def
  have hn : n = m + d := by omega
  have hterm : ∀ k ∈ Finset.range (m + 1), (m + n - 2 * k + 1 : ℕ) = d + 2 * (m - k) + 1 := by
    intro k hk
    simp only [Finset.mem_range] at hk
    omega
  rw [Finset.sum_congr rfl hterm]
  have hreflect := Finset.sum_range_reflect (fun k => d + 2 * k + 1) (m + 1)
  simp only [Nat.add_sub_cancel] at hreflect
  rw [hreflect]
  rw [sum_arithmetic_progression, hn]
  ring

/-- Clebsch–Gordan decomposition, dimension form:
the numerical shadow `(m+1)(n+1) = ∑_{k=0}^{min(m,n)} (m+n-2k+1)` of the module
isomorphism `V(m) ⊗ V(n) ≅ ⊕_k V(m+n-2k)`. -/
lemma clebsch_gordan_finrank (m n : ℕ) :
    (m + 1) * (n + 1) = ∑ k ∈ Finset.range (min m n + 1), (m + n - 2 * k + 1) := by
  rcases le_total m n with h | h
  · rw [min_eq_left h]
    exact clebsch_gordan_finrank_aux m n h
  · rw [min_eq_right h, Nat.add_comm m n, mul_comm]
    exact clebsch_gordan_finrank_aux n m h

/-- Clebsch–Gordan decomposition, vector-space form:
`V(m) ⊗ V(n)` is linearly isomorphic to `⊕_{k=0}^{min(m,n)} V(m+n-2k)`.

The equivalence follows only from equal dimensions. It does not identify the diagonal
`sl₂` action with the action on the direct sum or provide Clebsch–Gordan coefficients. -/
lemma clebsch_gordan (m n : ℕ) :
    Nonempty (StandardSl2Module K m ⊗[K] StandardSl2Module K n ≃ₗ[K]
      ⨁ _k : Fin (min m n + 1), StandardSl2Module K (m + n - 2 * (_k : ℕ))) := by
  have hdim : ∀ k : ℕ, Module.finrank K (StandardSl2Module K k) = k + 1 := fun k => by
    show Module.finrank K (Fin (k + 1) → K) = k + 1
    rw [Module.finrank_pi, Fintype.card_fin]
  have hfin : ∀ k : ℕ, Module.Finite K (StandardSl2Module K k) := fun k => by
    show Module.Finite K (Fin (k + 1) → K)
    infer_instance
  apply FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
  rw [Module.finrank_tensorProduct, hdim, hdim, Module.finrank_directSum]
  simp_rw [hdim]
  rw [Fin.sum_univ_eq_sum_range (fun k => m + n - 2 * k + 1)]
  exact clebsch_gordan_finrank m n

end PhyslibAlpha.Sl2
