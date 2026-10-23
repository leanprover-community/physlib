/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.CovarianceForm
public import PhyslibAlpha.ProbabilisticTheory.Channel.Basic
public import Mathlib.Analysis.Matrix.Order

/-!
# Covariances do not decrease under unital maps

## i. Overview

Let `Φ : A → B` be a linear map of unital `*`-algebras, `ω` a state on `B` and `ω'` the state
`ω ∘ Φ` on `A`. The map `Φ` moves observables (Heisenberg picture), and `ω'` is the state `ω`
after the dual map. We compare the covariance forms `C` of the two states.

* **Schwarz maps.** If `Φ(X)⋆ Φ(X) ≤ Φ(X⋆ X)`, the Kadison–Schwarz inequality, which holds for
  completely positive unital maps, then `C_ω(Φ X, Φ X) ≤ C_ω'(X, X)`: the difference is
  `ω(Φ(X⋆ X) - Φ(X)⋆ Φ(X))`. Taking `X = ∑ cⱼ Xⱼ`, the same holds for the quadratic form of the
  matrix of covariances of a family at every complex `c`, so commutator part included.
* **Positive maps of matrices.** Kadison's inequality `Φ(A)² ≤ Φ(A²)` for Hermitian `A` gives
  the same bound for Hermitian matrices, and for the matrix of covariances of Hermitian matrices
  at real `c`. Writing `A = ∑ λₖ Pₖ` with orthogonal projections, `Qₖ = Φ(Pₖ)` are positive with
  `∑ Qₖ = 1`, and `Φ(A²) - Φ(A)² = ∑ₖ (λₖ - Φ A) Qₖ (λₖ - Φ A)`.
* **The gap.** The transpose of `2 × 2` matrices is positive and unital, but the bound fails for
  the non-Hermitian matrix `E₀₁`.

## ii. Key results

- `AlgState.apply_nonneg` : on a star-ordered ring a state is nonnegative on nonnegative elements.
- `AlgState.covarianceForm_map_le` : a Schwarz inequality for `Φ` bounds the covariance form.
- `AlgState.covarianceMatrixForm_map_le` : Schwarz maps do not decrease the matrix of
  covariances.
- `Matrix.kadison` : Kadison's inequality for positive unital maps of matrices.
- `AlgState.covarianceForm_map_le_of_positive` : positive unital maps do not decrease the
  covariance form of Hermitian matrices.
- `AlgState.covarianceMatrixForm_map_le_of_positive` : nor the matrix of covariances of
  Hermitian matrices at real coefficients.
- `Matrix.transposeMap_gap` : the transpose is positive and unital but increases the covariance
  form of `E₀₁` after the map.

## iii. Table of contents

- A. Positivity of a state
- B. Schwarz maps
- C. Kadison's inequality
- D. Positive maps of matrices
- E. The transpose

## iv. References

* R. V. Kadison, *A generalized Schwarz inequality and algebraic invariants for operator
  algebras*, Ann. of Math. 56 (1952), 494–503.
* M.-D. Choi, *A Schwarz inequality for positive linear maps on C*-algebras*, Illinois J. Math.
  18 (1974), 565–574.

-/

@[expose] public section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace ProbabilisticTheory

namespace AlgState

/-! ## A. Positivity of a state -/

section Positivity

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A] [PartialOrder A]
  [StarOrderedRing A] (ω : AlgState A)

/-- On a star-ordered ring a state is nonnegative on every nonnegative element. -/
lemma apply_nonneg {a : A} (ha : 0 ≤ a) : 0 ≤ ω a := by
  rw [StarOrderedRing.nonneg_iff] at ha
  induction ha using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    exact ω.nonneg y
  | zero => exact (ω.toLinearMap.map_zero).ge
  | add x y _ _ hx hy =>
    rw [ω.map_add]
    exact add_nonneg hx hy

end Positivity

/-! ## B. Schwarz maps -/

section Schwarz

variable {A B : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]

/-- The quadratic form of the matrix of covariances at `c` is the covariance form of `∑ cⱼ aⱼ`
with itself. -/
lemma star_dotProduct_covarianceMatrixForm_mulVec {ι : Type*} [Fintype ι] (ω : AlgState A)
    (a : ι → A) (c : ι → ℂ) :
    star c ⬝ᵥ (ω.covarianceMatrixForm a a *ᵥ c) =
      ω.covarianceForm (∑ j, c j • a j) (∑ j, c j • a j) := by
  simp only [covarianceForm_sum_left, covarianceForm_sum_right, covarianceForm_smul_left,
    covarianceForm_smul_right, dotProduct, mulVec, covarianceMatrixForm, of_apply, Pi.star_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

variable (ω : AlgState B) (ω' : AlgState A) (Φ : A →ₗ[ℂ] B)

/-- Pulling the observable through `Φ` and pushing the state differ by the value of `ω` on
`Φ(X⋆ X) - Φ(X)⋆ Φ(X)`. -/
lemma covarianceForm_sub_covarianceForm_map (hω' : ∀ x, ω' x = ω (Φ x)) (X : A) :
    ω'.covarianceForm X X - ω.covarianceForm (Φ X) (Φ X) =
      ω (Φ (star X * X) - star (Φ X) * Φ X) := by
  rw [covarianceForm_apply, covarianceForm_apply, hω', hω',
    show ω (Φ (star X * X) - star (Φ X) * Φ X) = ω (Φ (star X * X)) - ω (star (Φ X) * Φ X) from
      ω.toLinearMap.map_sub _ _]
  ring

variable [PartialOrder B] [StarOrderedRing B]

/-- **A Schwarz inequality for `Φ` bounds the covariance form**: if
`Φ(X)⋆ Φ(X) ≤ Φ(X⋆ X)`, then `C_ω(Φ X, Φ X) ≤ C_ω'(X, X)`. -/
lemma covarianceForm_map_le (hω' : ∀ x, ω' x = ω (Φ x)) {X : A}
    (h : star (Φ X) * Φ X ≤ Φ (star X * X)) :
    ω.covarianceForm (Φ X) (Φ X) ≤ ω'.covarianceForm X X := by
  rw [← sub_nonneg, covarianceForm_sub_covarianceForm_map ω ω' Φ hω']
  exact ω.apply_nonneg (sub_nonneg.mpr h)

/-- **Maps satisfying the Schwarz inequality do not decrease the matrix of covariances.** The
hypothesis holds for completely positive unital maps. -/
lemma covarianceMatrixForm_map_le {ι : Type*} [Fintype ι] (hω' : ∀ x, ω' x = ω (Φ x))
    (hΦ : ∀ X, star (Φ X) * Φ X ≤ Φ (star X * X)) (a : ι → A) (c : ι → ℂ) :
    star c ⬝ᵥ (ω.covarianceMatrixForm (Φ ∘ a) (Φ ∘ a) *ᵥ c) ≤
      star c ⬝ᵥ (ω'.covarianceMatrixForm a a *ᵥ c) := by
  have e : ∑ j, c j • (Φ ∘ a) j = Φ (∑ j, c j • a j) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => (_root_.map_smul Φ _ _).symm
  rw [star_dotProduct_covarianceMatrixForm_mulVec, star_dotProduct_covarianceMatrixForm_mulVec, e]
  exact covarianceForm_map_le ω ω' Φ hω' (hΦ _)

end Schwarz

end AlgState

end ProbabilisticTheory

/-! ## C. Kadison's inequality -/

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- With positive `Qₖ` summing to `1`, `(∑ λₖ Qₖ)² ≤ ∑ λₖ² Qₖ`. -/
lemma sq_sum_le_sum_sq {ι : Type*} [Fintype ι] (Q : ι → Matrix m m ℂ)
    (hQ : ∀ k, (Q k).PosSemidef) (h1 : ∑ k, Q k = 1) (c : ι → ℝ) :
    (∑ k, (c k : ℂ) • Q k) * ∑ k, (c k : ℂ) • Q k ≤ ∑ k, ((c k : ℂ) * c k) • Q k := by
  set B := ∑ k, (c k : ℂ) • Q k
  have hB : Bᴴ = B := by
    simp [B, conjTranspose_sum, conjTranspose_smul, (hQ _).1.eq]
  have term : ∀ k, ((c k : ℂ) • 1 - B)ᴴ * Q k * ((c k : ℂ) • 1 - B) =
      ((c k : ℂ) * c k) • Q k - (c k : ℂ) • (Q k * B) - (c k : ℂ) • (B * Q k) + B * Q k * B := by
    intro k
    simp only [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hB, Complex.star_def,
      Complex.conj_ofReal, sub_mul, mul_sub, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
      smul_sub, smul_smul]
    abel
  have e₁ : ∑ k, (c k : ℂ) • (Q k * B) = B * B := by
    simp only [← smul_mul_assoc, ← Finset.sum_mul]; rfl
  have e₂ : ∑ k, (c k : ℂ) • (B * Q k) = B * B := by
    simp only [← mul_smul_comm, ← Finset.mul_sum]; rfl
  have e₃ : ∑ k, B * Q k * B = B * B := by rw [← Finset.sum_mul, ← Finset.mul_sum, h1, mul_one]
  have h : ∑ k, ((c k : ℂ) * c k) • Q k - B * B =
      ∑ k, ((c k : ℂ) • 1 - B)ᴴ * Q k * ((c k : ℂ) • 1 - B) := by
    simp only [term, Finset.sum_add_distrib, Finset.sum_sub_distrib, e₁, e₂, e₃]
    abel
  rw [← sub_nonneg, h, nonneg_iff_posSemidef]
  exact posSemidef_sum _ fun k _ => (hQ k).conjTranspose_mul_mul_same _

/-- **Kadison's inequality**: for a positive unital map and Hermitian `A`,
`Φ(A)² ≤ Φ(A²)`. -/
lemma kadison (Φ : Matrix n n ℂ →ₚ₁[ℂ] Matrix m m ℂ) {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : (Φ A)ᴴ * Φ A ≤ Φ (Aᴴ * A) := by
  let c := Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
  let P : n → Matrix n n ℂ := fun k => c (single k k 1)
  have hdiag : ∀ f : n → ℂ, c (diagonal f) = ∑ k, f k • P k := by
    intro f
    rw [show diagonal f = ∑ k, f k • single k k 1 by
      ext i j
      by_cases h : i = j
      · simp [h, single_apply, Matrix.sum_apply]
      · simp only [diagonal_apply, h, Matrix.sum_apply, Matrix.smul_apply, single_apply]
        exact (Finset.sum_eq_zero fun x _ => by simp [show ¬(x = i ∧ x = j) from
          fun hx => h (hx.1 ▸ hx.2)]).symm]
    simp only [P, map_sum, map_smul]
  have hA' : A = ∑ k, (hA.eigenvalues k : ℂ) • P k := by
    rw [← hdiag]; exact hA.spectral_theorem
  have hA2 : Aᴴ * A = ∑ k, ((hA.eigenvalues k : ℂ) * hA.eigenvalues k) • P k := by
    rw [← hdiag, ← diagonal_mul_diagonal, map_mul]
    conv_lhs => rw [hA.eq, hA.spectral_theorem]
    rfl
  have hP : ∀ k, (P k).PosSemidef := fun k => by
    let U : Matrix n n ℂ := hA.eigenvectorUnitary
    have e : P k = U * single k k 1 * (U * single k k 1)ᴴ := by
      rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (single k k 1),
        conjTranspose_single, star_one, single_mul_single_same, one_mul]
      simp only [P, c, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc]
      rfl
    rw [e]
    exact posSemidef_self_mul_conjTranspose _
  have hsum : ∑ k, Φ (P k) = 1 := by
    have h := hdiag fun _ => 1
    simp only [diagonal_one, map_one, one_smul] at h
    rw [← map_sum, ← h, map_one]
  have hQ : ∀ k, (Φ (P k)).PosSemidef := fun k =>
    nonneg_iff_posSemidef.mp (map_nonneg Φ (nonneg_iff_posSemidef.mpr (hP k)))
  have hH : (Φ A)ᴴ = Φ A := by
    rw [hA', map_sum, conjTranspose_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, conjTranspose_smul, (hQ k).1.eq, Complex.star_def, Complex.conj_ofReal]
  have hΦA : Φ A = ∑ k, (hA.eigenvalues k : ℂ) • Φ (P k) := by
    conv_lhs => rw [hA']
    simp only [map_sum, map_smul]
  rw [hH, hA2, hΦA, map_sum]
  simp only [map_smul]
  exact sq_sum_le_sum_sq _ hQ hsum _

end Matrix

/-! ## D. Positive maps of matrices -/

namespace ProbabilisticTheory

namespace AlgState

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
  (ω : AlgState (Matrix m m ℂ)) (ω' : AlgState (Matrix n n ℂ))
  (Φ : Matrix n n ℂ →ₚ₁[ℂ] Matrix m m ℂ)

/-- **Positive unital maps do not decrease the covariance form of Hermitian matrices.** -/
lemma covarianceForm_map_le_of_positive (hω' : ∀ x, ω' x = ω (Φ x)) {X : Matrix n n ℂ}
    (hX : X.IsHermitian) : ω.covarianceForm (Φ X) (Φ X) ≤ ω'.covarianceForm X X :=
  covarianceForm_map_le ω ω' Φ.toLinearMap hω' (Matrix.kadison Φ hX)

/-- **Positive unital maps do not decrease the matrix of covariances** of Hermitian matrices at
real coefficients. -/
lemma covarianceMatrixForm_map_le_of_positive {ι : Type*} [Fintype ι]
    (hω' : ∀ x, ω' x = ω (Φ x)) {a : ι → Matrix n n ℂ} (ha : ∀ i, (a i).IsHermitian)
    (c : ι → ℝ) :
    star (fun i => (c i : ℂ)) ⬝ᵥ (ω.covarianceMatrixForm (Φ ∘ a) (Φ ∘ a) *ᵥ fun i => (c i : ℂ)) ≤
      star (fun i => (c i : ℂ)) ⬝ᵥ (ω'.covarianceMatrixForm a a *ᵥ fun i => (c i : ℂ)) := by
  have e : ∑ j, (c j : ℂ) • (Φ ∘ a) j = Φ (∑ j, (c j : ℂ) • a j) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => (_root_.map_smul Φ _ _).symm
  rw [star_dotProduct_covarianceMatrixForm_mulVec, star_dotProduct_covarianceMatrixForm_mulVec, e]
  refine covarianceForm_map_le_of_positive ω ω' Φ hω' ?_
  simp [IsHermitian, conjTranspose_sum, conjTranspose_smul, (ha _).eq]

end AlgState

end ProbabilisticTheory

/-! ## E. The transpose -/

namespace Matrix

/-- The state `X ↦ X₀₀` of `2 × 2` matrices, the vector state of `|0⟩`. -/
def stateZero : ProbabilisticTheory.AlgState (Matrix (Fin 2) (Fin 2) ℂ) where
  toLinearMap :=
    { toFun X := X 0 0
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := one_apply_eq 0
  map_star' _ := rfl
  nonneg' X := show 0 ≤ ∑ k, star (X k 0) * X k 0 from
    Finset.sum_nonneg fun k _ => star_mul_self_nonneg (X k 0)

@[simp]
lemma stateZero_apply (X : Matrix (Fin 2) (Fin 2) ℂ) : stateZero X = X 0 0 := rfl

/-- The transpose of `2 × 2` matrices. -/
noncomputable def transposeMap : Matrix (Fin 2) (Fin 2) ℂ →ₚ₁[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  .ofLinearMap (transposeLinearEquiv (Fin 2) (Fin 2) ℂ ℂ).toLinearMap
    (fun _ hX => nonneg_iff_posSemidef.mpr (nonneg_iff_posSemidef.mp hX).transpose)
    (by simp)

@[simp]
lemma transposeMap_apply (X : Matrix (Fin 2) (Fin 2) ℂ) : transposeMap X = Xᵀ := rfl

/-- The state `X ↦ X₀₀` is unchanged by the transpose. -/
lemma stateZero_transposeMap (X : Matrix (Fin 2) (Fin 2) ℂ) :
    stateZero X = stateZero (transposeMap X) := rfl

/-- **The transpose is positive and unital, but the bound fails for `E₀₁`**: for positive maps
it holds only on Hermitian matrices. -/
lemma transposeMap_gap :
    ¬ stateZero.covarianceForm (transposeMap (single 0 1 1)) (transposeMap (single 0 1 1)) ≤
      stateZero.covarianceForm (single 0 1 1) (single 0 1 1) := by
  simp [ProbabilisticTheory.AlgState.covarianceForm_apply, mul_apply, Fin.sum_univ_two,
    Complex.le_def]

end Matrix
