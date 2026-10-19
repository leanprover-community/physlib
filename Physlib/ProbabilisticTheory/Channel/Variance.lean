/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Physlib.ProbabilisticTheory.Channel.Basic

/-!
# Variances cannot decrease under unital channels

## i. Overview

For a positive functional `ω` on `Mₘ(ℂ)` and a matrix `X`, the variance is
`ω(Xᴴ X) − |ω(X)|²`. A unital map `Φ : Mₙ(ℂ) → Mₘ(ℂ)` moves observables (Heisenberg picture);
the state `ω ∘ Φ` is the state `ω` after the dual channel.

* **Schwarz maps.** If `Φ(X)ᴴ Φ(X) ≤ Φ(Xᴴ X)` (the Kadison–Schwarz inequality, which holds for
  completely positive unital maps), the variance of `Φ X` in `ω` is at most the variance of `X`
  in `ω ∘ Φ`, for every `X`.
* **Positive maps.** Kadison's inequality `Φ(A)² ≤ Φ(A²)` gives the same bound for Hermitian
  `A`. Writing `A = ∑ λₖ Pₖ` with orthogonal projections, `Qₖ = Φ(Pₖ)` are positive with
  `∑ Qₖ = 1`, and `Φ(A²) − Φ(A)² = ∑ₖ (λₖ − Φ A) Qₖ (λₖ − Φ A)`.
* **Covariance matrices.** For observables `A₁, …, Aₖ` the quadratic form of the covariance
  matrix `ω(Aᵢᴴ Aⱼ) − ω(Aᵢ)* ω(Aⱼ)` at `c` is the variance of `∑ cⱼ Aⱼ`. Completely positive maps
  therefore order the whole covariance matrix, commutator part included; positive maps order it
  only at real `c`, its symmetric part.
* **The gap.** For the transpose, a positive unital map that is not completely positive, the
  bound fails for the non-Hermitian matrix `E₀₁`.

## ii. Key results

- `Matrix.variance` : the variance `ω(Xᴴ X) − |ω(X)|²`.
- `Matrix.variance_le_of_le` : a Schwarz inequality `Φ(X)ᴴ Φ(X) ≤ Φ(Xᴴ X)` bounds the variance.
- `Matrix.kadison` : Kadison's inequality for positive unital maps.
- `Matrix.variance_le_of_positive` : positive unital maps do not decrease variances of
  Hermitian matrices.
- `Matrix.transposeMap_gap` : the transpose is positive and unital but decreases the
  variance of `E₀₁`.
- `Matrix.covariance_le_of_schwarz` : maps with the Schwarz inequality do not decrease the
  covariance matrix, in the order of Hermitian forms.
- `Matrix.covariance_le_of_positive` : positive unital maps do not decrease its real part on
  Hermitian observables.

## iii. Table of contents

- A. The variance
- B. Positive maps
- C. The transpose
- D. The covariance matrix

## iv. References

* R. V. Kadison, *A generalized Schwarz inequality and algebraic invariants for operator
  algebras*, Ann. of Math. 56 (1952), 494–503.
* M.-D. Choi, *A Schwarz inequality for positive linear maps on C*-algebras*, Illinois J. Math.
  18 (1974), 565–574.

-/

@[expose] public section

open Matrix
open scoped ComplexOrder MatrixOrder

noncomputable section

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-!

## A. The variance

-/

/-- The variance `ω(Xᴴ X) − |ω(X)|²` of `X` in the functional `ω`. -/
def variance (ω : Matrix m m ℂ →ₗ[ℂ] ℂ) (X : Matrix m m ℂ) : ℂ :=
  ω (Xᴴ * X) - star (ω X) * ω X

/-- Pulling the observable through `Φ` is the same as pushing the state. -/
lemma variance_comp_sub (ω : Matrix m m ℂ →ₗ[ℂ] ℂ) (Φ : Matrix n n ℂ →ₚ₁[ℂ] Matrix m m ℂ)
    (X : Matrix n n ℂ) :
    variance (ω ∘ₗ Φ.toLinearMap) X - variance ω (Φ X) = ω (Φ (Xᴴ * X) - (Φ X)ᴴ * Φ X) := by
  simp [variance, map_sub]

lemma variance_le_of_le {ω : Matrix m m ℂ →ₗ[ℂ] ℂ} (hω : ∀ P, 0 ≤ P → 0 ≤ ω P)
    {Φ : Matrix n n ℂ →ₚ₁[ℂ] Matrix m m ℂ} {X : Matrix n n ℂ} (h : (Φ X)ᴴ * Φ X ≤ Φ (Xᴴ * X)) :
    variance ω (Φ X) ≤ variance (ω ∘ₗ Φ.toLinearMap) X := by
  rw [← sub_nonneg, variance_comp_sub]
  exact hω _ (sub_nonneg.mpr h)

/-!

## B. Positive maps

-/

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

/-- **Positive unital maps do not decrease variances of Hermitian matrices.** -/
lemma variance_le_of_positive {ω : Matrix m m ℂ →ₗ[ℂ] ℂ} (hω : ∀ P, 0 ≤ P → 0 ≤ ω P)
    (Φ : Matrix n n ℂ →ₚ₁[ℂ] Matrix m m ℂ) {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : variance ω (Φ A) ≤ variance (ω ∘ₗ Φ.toLinearMap) A :=
  variance_le_of_le hω (kadison Φ hA)

/-!

## C. The transpose

-/

/-- The functional `X ↦ X₀₀`, the expectation in the state `|0⟩⟨0|`. -/
def entry₀₀ : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] ℂ where
  toFun X := X 0 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma entry₀₀_apply (X : Matrix (Fin 2) (Fin 2) ℂ) : entry₀₀ X = X 0 0 := rfl

/-- The transpose of `2 × 2` matrices. -/
def transposeMap : Matrix (Fin 2) (Fin 2) ℂ →ₚ₁[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  .ofLinearMap (transposeLinearEquiv (Fin 2) (Fin 2) ℂ ℂ).toLinearMap
    (fun _ hX => nonneg_iff_posSemidef.mpr (nonneg_iff_posSemidef.mp hX).transpose)
    (by simp)

@[simp]
lemma transposeMap_apply (X : Matrix (Fin 2) (Fin 2) ℂ) : transposeMap X = Xᵀ := rfl

/-- **The transpose is positive and unital, but it decreases the variance of `E₀₁`**: for
positive maps the bound holds only on Hermitian matrices. -/
lemma transposeMap_gap : ¬ variance entry₀₀ (transposeMap (single 0 1 1)) ≤
    variance (entry₀₀ ∘ₗ transposeMap.toLinearMap) (single 0 1 1) := by
  simp [variance, Complex.le_def]

/-!

## D. The covariance matrix

-/

/-- The covariance matrix `ω(Aᵢᴴ Aⱼ) − ω(Aᵢ)* ω(Aⱼ)` of the observables `A` in `ω`. -/
def covariance {ι : Type*} (ω : Matrix m m ℂ →ₗ[ℂ] ℂ) (A : ι → Matrix m m ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => ω ((A i)ᴴ * A j) - star (ω (A i)) * ω (A j)

omit [DecidableEq m] in
/-- The quadratic form of the covariance matrix at `c` is the variance of `∑ cⱼ Aⱼ`. -/
lemma star_dotProduct_covariance_mulVec {ι : Type*} [Fintype ι] (ω : Matrix m m ℂ →ₗ[ℂ] ℂ)
    (A : ι → Matrix m m ℂ) (c : ι → ℂ) :
    star c ⬝ᵥ (covariance ω A *ᵥ c) = variance ω (∑ j, c j • A j) := by
  simp only [variance, covariance, dotProduct, mulVec, of_apply, conjTranspose_sum,
    conjTranspose_smul, Finset.sum_mul, Finset.mul_sum, map_sum, map_smul, star_sum,
    smul_eq_mul, smul_mul_assoc, mul_smul_comm, star_mul', Pi.star_apply, Complex.star_def]
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  congr 1 <;> rw [Finset.sum_comm] <;>
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- **Maps satisfying the Schwarz inequality do not decrease the covariance matrix.** The
hypothesis holds for completely positive unital maps. -/
lemma covariance_le_of_schwarz {ι : Type*} [Fintype ι] {ω : Matrix m m ℂ →ₗ[ℂ] ℂ}
    (hω : ∀ P, 0 ≤ P → 0 ≤ ω P) {Φ : Matrix n n ℂ →ₚ₁[ℂ] Matrix m m ℂ}
    (hΦ : ∀ X, (Φ X)ᴴ * Φ X ≤ Φ (Xᴴ * X)) (A : ι → Matrix n n ℂ) (c : ι → ℂ) :
    star c ⬝ᵥ (covariance ω (Φ ∘ A) *ᵥ c) ≤ star c ⬝ᵥ (covariance (ω ∘ₗ Φ.toLinearMap) A *ᵥ c) := by
  simp only [star_dotProduct_covariance_mulVec, Function.comp_apply, ← map_smul, ← map_sum]
  exact variance_le_of_le hω (hΦ _)

/-- **Positive unital maps do not decrease the real part of the covariance matrix** of
Hermitian observables. -/
lemma covariance_le_of_positive {ι : Type*} [Fintype ι] {ω : Matrix m m ℂ →ₗ[ℂ] ℂ}
    (hω : ∀ P, 0 ≤ P → 0 ≤ ω P) (Φ : Matrix n n ℂ →ₚ₁[ℂ] Matrix m m ℂ)
    {A : ι → Matrix n n ℂ} (hA : ∀ i, (A i).IsHermitian) (c : ι → ℝ) :
    star (fun i => (c i : ℂ)) ⬝ᵥ (covariance ω (Φ ∘ A) *ᵥ fun i => (c i : ℂ)) ≤
      star (fun i => (c i : ℂ)) ⬝ᵥ (covariance (ω ∘ₗ Φ.toLinearMap) A *ᵥ fun i => (c i : ℂ)) := by
  simp only [star_dotProduct_covariance_mulVec, Function.comp_apply, ← map_smul, ← map_sum]
  refine variance_le_of_positive hω Φ ?_
  simp [IsHermitian, conjTranspose_sum, conjTranspose_smul, (hA _).eq]

end Matrix
