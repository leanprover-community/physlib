/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order

/-!
# Positive-semidefinite matrix algebra

This file supplements Mathlib's `Matrix.PosSemidef` API for matrices indexed by arbitrary types.

## i. Overview

This file supplements Mathlib's `Matrix.PosSemidef` API for matrices indexed by arbitrary types.
It provides rank-one and constant matrices, finite Schur products, Schur powers,
products of weights over unions of finite sets, and the quadratic-form characterization.

The results apply in particular to positive-definite kernels, represented directly as matrices,
but do not depend on Tau Ceti's positive-definite-function theory.

## ii. Key results

* `TauCeti.posSemidef_rankOne`: rank-one positive-semidefinite matrices.
* `TauCeti.posSemidef_const_one` and `TauCeti.posSemidef_const_of_nonneg`: constant matrices.
* `TauCeti.posSemidef_iff_finite_sum`: the quadratic-form characterization.
* `TauCeti.posSemidef_schur_finset_prod` and `Matrix.PosSemidef.hadamard_pow`: finite Schur
  products and Schur powers.
* `TauCeti.posSemidef_prod_union`: the matrix `(i, j) ↦ ∏_{a ∈ L i ∪ L j} w a` for weights in
  `[0, 1]`.

## iii. Table of contents

- A. Development

## iv. References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

/-! ## A. Development -/

open Matrix
open scoped ComplexConjugate ComplexOrder

namespace TauCeti

universe u v w

variable {α : Type v}

private lemma posSemidef_of_support_posSemidef {R : Type u}
    [Ring R] [PartialOrder R] [StarRing R] (K : α → α → R)
    (hHerm : (Matrix.of fun a b => K a b).IsHermitian) (hgram : ∀ x : α →₀ R,
      (Matrix.of fun i j : x.support => K (i : α) (j : α)).PosSemidef) :
    (Matrix.of fun a b => K a b).PosSemidef := by
  classical
  refine ⟨hHerm, fun x => ?_⟩
  let y : x.support → R := fun i => x i
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp (hgram x)).2 y
  have h' :
      0 ≤ ∑ i : x.support, ∑ j : x.support,
        star (x (i : α)) * (K (i : α) (j : α) * x (j : α)) := by
    simpa only [y, dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply,
      Finset.mul_sum, mul_assoc] using h
  have h'' :
      0 ≤ ∑ i ∈ x.support, ∑ j ∈ x.support,
        star (x i) * (K i j * x j) := by
    convert h' using 1
    rw [Finset.sum_subtype x.support (by intro a; rfl)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_subtype x.support (by intro a; rfl)]
  simpa only [Matrix.of_apply, Finsupp.sum, mul_assoc] using h''

/-- The rank-one matrix `(a, b) ↦ star (g a) · g b` is positive semidefinite for an arbitrary
index type. Such matrices are elementary building blocks for positive-semidefinite matrices;
taking `g ≡ 1` gives the constant matrix `1`. -/
lemma posSemidef_rankOne {R : Type u}
    [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R] (g : α → R) :
    Matrix.PosSemidef (fun a b => star (g a) * g b) := by
  refine posSemidef_of_support_posSemidef (fun a b => star (g a) * g b) ?_ fun x => ?_
  · exact Matrix.IsHermitian.ext fun a b => by simp
  · convert Matrix.posSemidef_vecMulVec_star_self (fun a : x.support => g a) using 1
    ext a b
    simp [Matrix.vecMulVec_apply]

/-- The constant matrix with value `1` is positive semidefinite. -/
lemma posSemidef_const_one {R : Type u}
    [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R] :
    Matrix.PosSemidef (fun _ _ : α => (1 : R)) := by
  simpa using posSemidef_rankOne (R := R) (α := α) (fun _ => (1 : R))

/-- A nonnegative constant gives a positive-semidefinite constant matrix. -/
lemma posSemidef_const_of_nonneg {R : Type u}
    [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    {c : R} (hc : 0 ≤ c) : Matrix.PosSemidef (fun _ _ : α => c) := by
  have heq : (Matrix.diagonal (fun _ : Unit => c)).submatrix (fun _ : α => ())
      (fun _ : α => ()) = fun _ _ : α => c := by ext; simp
  rw [← heq]
  exact (Matrix.PosSemidef.diagonal (fun _ => hc)).submatrix _

/-- The quadratic-form characterization of an arbitrary-index positive-semidefinite matrix:
conjugate symmetry and nonnegativity on every finite family, allowing repeated indices. -/
lemma posSemidef_iff_finite_sum {R : Type u} [Ring R] [PartialOrder R] [StarRing R]
    {K : α → α → R} :
    Matrix.PosSemidef K ↔
      (∀ a b, star (K a b) = K b a) ∧
        ∀ {ι : Type*} [Fintype ι] (v : ι → α) (x : ι → R),
          0 ≤ ∑ i, ∑ j, star (x i) * K (v i) (v j) * x j := by
  classical
  refine ⟨fun hK => ⟨fun a b => ?_, ?_⟩, fun ⟨hsymm, hpos⟩ => ?_⟩
  · exact hK.isHermitian.apply b a
  · intro ι _ v x
    simpa only [dotProduct, Matrix.mulVec, Matrix.submatrix, Matrix.of_apply, Pi.star_apply,
      Finset.mul_sum, mul_assoc] using (hK.submatrix v).dotProduct_mulVec_nonneg x
  refine posSemidef_of_support_posSemidef K ?_ ?_
  · ext a b
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply]
    exact hsymm b a
  · intro x
    -- Realize the support in the universe quantified over by `hpos`.
    let e : ULift (Fin (Fintype.card x.support)) ≃ x.support :=
      Equiv.ulift.trans (Fintype.equivFin x.support).symm
    refine (Matrix.posSemidef_submatrix_equiv e).mp ?_
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, fun y => ?_⟩
    · ext i j
      rw [Matrix.conjTranspose_apply, Matrix.submatrix_apply, Matrix.submatrix_apply,
        Matrix.of_apply, Matrix.of_apply]
      exact hsymm (e j : α) (e i : α)
    · refine (hpos (ι := ULift (Fin (Fintype.card x.support)))
        (fun i => (e i : α)) y).trans_eq ?_
      simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Matrix.of_apply,
        Pi.star_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      exact mul_assoc _ _ _

variable {𝕜 : Type u} [RCLike 𝕜]

/-- Finite pointwise Schur products of positive-semidefinite matrices are positive semidefinite. -/
lemma posSemidef_schur_finset_prod {ι : Type w} {s : Finset ι}
    {K : ι → α → α → 𝕜} (hK : ∀ i ∈ s, Matrix.PosSemidef (K i)) :
    Matrix.PosSemidef (fun a b => ∏ i ∈ s, K i a b) := by
  have heq : (∏ i ∈ s, K i) = fun a b => ∏ i ∈ s, K i a b := by ext; simp
  rw [← heq]
  exact Finset.prod_induction K Matrix.PosSemidef
    (fun _ _ hA hB => hA.hadamard hB) posSemidef_const_one hK

/-- For weights `w` in `[0, 1]` and finite sets `L i`, the matrix
`(i, j) ↦ ∏_{a ∈ L i ∪ L j} w a` is positive semidefinite. -/
lemma posSemidef_prod_union {ι : Type w} [DecidableEq α] (L : ι → Finset α)
    {w : α → ℝ} (hw₀ : ∀ a, 0 ≤ w a) (hw₁ : ∀ a, w a ≤ 1) :
    Matrix.PosSemidef (fun i j => ∏ a ∈ L i ∪ L j, w a) := by
  -- The indicator of `a ∉ L i`.
  let χ : α → ι → ℝ := fun a i => if a ∈ L i then 0 else 1
  have hfactor (a : α) :
      Matrix.PosSemidef (fun i j => w a + star (√(1 - w a) * χ a i) * (√(1 - w a) * χ a j)) :=
    (posSemidef_const_of_nonneg (hw₀ a)).add (posSemidef_rankOne fun i => √(1 - w a) * χ a i)
  have hterm (i j : ι) (a : α) :
      (w a + star (√(1 - w a) * χ a i) * (√(1 - w a) * χ a j)) =
        if a ∈ L i ∪ L j then w a else 1 := by
    have hsq : √(1 - w a) * √(1 - w a) = 1 - w a := Real.mul_self_sqrt (sub_nonneg.2 (hw₁ a))
    by_cases hi : a ∈ L i <;> by_cases hj : a ∈ L j <;> simp [χ, hi, hj, hsq]
  refine posSemidef_of_support_posSemidef
    (fun i j => ∏ a ∈ L i ∪ L j, w a) ?_ fun x => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    rw [Finset.union_comm]
  · let s : Finset α := x.support.biUnion L
    have hs (i : x.support) : L i ⊆ s := by
      intro a ha
      exact Finset.mem_biUnion.mpr ⟨i, i.property, ha⟩
    have heq : (Matrix.of fun i j : x.support => ∏ a ∈ L i ∪ L j, w a) =
        (fun i j : x.support => ∏ a ∈ s,
          (w a + star (√(1 - w a) * χ a i) * (√(1 - w a) * χ a j))) := by
      ext i j
      simp only [Matrix.of_apply]
      simp_rw [hterm]
      rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr (Finset.union_subset (hs i) (hs j))]
    rw [heq]
    exact posSemidef_schur_finset_prod fun a _ => (hfactor a).submatrix Subtype.val

end TauCeti

/-- Schur powers of a positive-semidefinite matrix are positive semidefinite. -/
lemma Matrix.PosSemidef.hadamard_pow {α 𝕜 : Type*} [RCLike 𝕜] {K : α → α → 𝕜}
    (hK : Matrix.PosSemidef K) (n : ℕ) :
    Matrix.PosSemidef (fun a b => K a b ^ n) := by
  induction n with
  | zero =>
      simpa using TauCeti.posSemidef_const_one (R := 𝕜) (α := α)
  | succ n ih =>
      have heq : (Matrix.of fun a b => K a b ^ n) ⊙ Matrix.of K = (fun a b => K a b ^ (n + 1)) := by
        ext
        rw [Matrix.hadamard_apply, Matrix.of_apply, Matrix.of_apply, pow_succ]
      exact heq ▸ ih.hadamard hK
